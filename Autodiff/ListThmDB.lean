module

import Lean.Data.SMap
import Lean.Declaration
public import Lean.Elab.Term
import Lean.Environment
public import Lean.Data.NameMap

open Lean Elab.Term

def isDerivTheorem (env: Environment) (ci: ConstantInfo): Bool :=
  let t := ci.toConstantVal.type
  let n := Name.mkStr1 "HasDerivAt"

  let isTheorem := match (getOriginalConstKind? env ci.name) with
                   | some k => k == ConstantKind.thm
                   | none => false
  if (! isTheorem || ! t.isForall) then
    false
  else
    let b := t.getForallBody
    let app := b.isAppOf n
    app

/-- The function argument `f` of a theorem's `HasDerivAt f f' x` conclusion. -/
public def thmFnArg (ty: Expr): Option Expr :=
  let b := ty.getForallBody
  let args := b.getAppArgs
  if b.isAppOf `HasDerivAt && args.size ≥ 3 then some args[args.size - 3]! else none

/-- A catch-all theorem concludes `HasDerivAt f _ _` for an arbitrary function `f`
  (e.g. `HasStrictDerivAt.hasDerivAt`), so it applies to every goal. -/
public def isCatchAll (ty: Expr): Bool :=
  match thmFnArg ty with
  | some f => f.getAppFn.isBVar
  | none => false

public def appHead: Expr → Name
  | .const n _ => n
  | .app f _ => appHead f
  | _ => Name.anonymous

/-- Head symbol of the differentiated function, e.g. `Real.sin` for `fun y => Real.sin (f y)`;
  anonymous if unknown (e.g. `fun _ => c`). -/
public def thmHead (ty: Expr): Name :=
  match thmFnArg ty with
  | some (.lam _ _ b _) => appHead b
  | some f => appHead f
  | none => Name.anonymous

public def populateExt : TermElabM (List ConstantInfo) := do
  let env ← getEnv
  let cs := SMap.toList (env.constants)
  let thms' := /- Prod.fst <| List.unzip <| -/ (cs.map (Prod.snd)).filter ((isDerivTheorem env))
  let thms := List.mergeSort thms' (λ a b ↦ (a.type.getForallArity ≤ b.type.getForallArity))
  return thms

/-- Derivative theorems, sorted by arity. `byHead` maps a head symbol to the
  theorems that can match a function with that head: those with the same head and
  those whose head is unknown (`wild`). Catch-all theorems are left out, except
  from `legacy`, which is the original list used when `AD_LEGACY` is set. -/
public structure ThmIndex where
  legacy : List ConstantInfo := []
  all : List ConstantInfo := []
  wild : List ConstantInfo := []
  byHead : NameMap (List ConstantInfo) := {}
deriving Inhabited

/-- Theorems excluded by hand in the original search; not needed with the index
  (they are catch-alls or have heads such as `Complex.exp` that never match). -/
public def legacyBlackList : List Name := [`HasDerivAt.real_of_complex, `DifferentiableAt.hasDerivAt,
    `Complex.hasDerivAt_exp, `Complex.hasDerivAt_sinh, `Complex.hasDerivAt_sin, `Complex.hasDerivAt_cos,
    `Complex.hasDerivAt_cosh, `Complex.hasDerivAt_tan,
    `HasDerivAt.of_notMem_tsupport]

public def buildIndex (thms : List ConstantInfo) : ThmIndex :=
  let legacy := thms.filter (fun c => ! legacyBlackList.elem c.name)
  let all := thms.filter (fun c => ! isCatchAll c.type)
  let wild := all.filter (fun c => (thmHead c.type).isAnonymous)
  let heads := (all.map (fun c => thmHead c.type)).filter (! ·.isAnonymous) |>.eraseDups
  let byHead := heads.foldl (fun m h =>
    m.insert h (all.filter (fun c => let k := thmHead c.type; k == h || k.isAnonymous))) {}
  { legacy, all, wild, byHead }

public class ThmDB (α: Type) where
  init (t: α): TermElabM Unit
  size (t: α): TermElabM Nat
  lookup (t: α) (n: Name): TermElabM (List ConstantInfo)

public initialize derivThmIndex: EnvExtension ThmIndex ←
  registerEnvExtension (pure {})

public structure ListThmDB where
  store: EnvExtension ThmIndex := derivThmIndex

public instance: ThmDB ListThmDB where
  init t := do
    let env ← getEnv
    let env' := t.store.setState env (buildIndex (← populateExt))
    setEnv env'

  size t := do
    let env ← getEnv
    let s := t.store.getState env
    return s.legacy.length

  -- theorems that can match a function whose head symbol is `n`
  lookup t n := do
    let s := t.store.getState (← getEnv)
    if (← IO.getEnv "AD_LEGACY").isSome then
      return s.legacy
    if n.isAnonymous then
      return s.all
    return (s.byHead.find? n).getD s.wild
