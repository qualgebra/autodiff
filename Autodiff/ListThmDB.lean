module

import Lean.Data.SMap
import Lean.Declaration
public import Lean.Elab.Term
import Lean.Environment

open Lean Elab.Term

def isDerivTheorem (env: Environment) (ci: ConstantInfo): Bool :=
  let t := ci.toConstantVal.type
  let n' := ci.name
  let blackList := [`HasDerivAt.real_of_complex, `DifferentiableAt.hasDerivAt,
    `Complex.hasDerivAt_exp, `Complex.hasDerivAt_sinh, `Complex.hasDerivAt_sin, `Complex.hasDerivAt_cos,
    `Complex.hasDerivAt_cosh, `Complex.hasDerivAt_tan,
    `HasDerivAt.of_notMem_tsupport]
  let n := Name.mkStr1 "HasDerivAt"

  let isTheorem := match (getOriginalConstKind? env ci.name) with
                   | some k => k == ConstantKind.thm
                   | none => false
  if (! isTheorem || ! t.isForall || blackList.elem n') then
    false
  else
    let b := t.getForallBody
    let app := b.isAppOf n
    app

public def populateExt : TermElabM (List ConstantInfo) := do
  let env ← getEnv
  let cs := SMap.toList (env.constants)
  let thms' := /- Prod.fst <| List.unzip <| -/ (cs.map (Prod.snd)).filter ((isDerivTheorem env))
  let thms := List.mergeSort thms' (λ a b ↦ (a.type.getForallArity ≤ b.type.getForallArity))
  return thms

public class ThmDB (α: Type) where
  init (t: α): TermElabM Unit
  size (t: α): TermElabM Nat
  lookup (t: α) (n: Name): TermElabM (List ConstantInfo)

public initialize derivThmList: EnvExtension (List ConstantInfo) ←
  registerEnvExtension (pure [])

public structure ListThmDB where
  store: EnvExtension (List ConstantInfo) := derivThmList

public instance: ThmDB ListThmDB where
  init t := do
    let env ← getEnv
    let env' := t.store.setState env (← populateExt)
    setEnv env'

  size t := do
    let env ← getEnv
    let s := t.store.getState env
    return s.length

  lookup t _ := do
    let env ← getEnv
    pure <| t.store.getState env
