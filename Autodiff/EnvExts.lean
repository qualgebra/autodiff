/-
  environment extensions for automatic differentiation
-/
module

import Lean
public import Lean.Elab.Term
public import Lean.Elab.Deriving.Basic
public import Lean.Elab.Deriving.Util
public import Lean.Meta.Inductive
public import Lean.Meta.Transform
public import Autodiff.ListThmDB

open Lean Meta Elab.Tactic Meta.Tactic
open Lean Elab Command Lean.Meta Lean.Elab.Term
open Lean.Parser.Term Elab.Tactic Meta.Tactic
open Lean.Parser.Command
open Meta
open Std

namespace AR.Tools.Context
/-
def isDerivTheorem (env: Environment) (ci: ConstantInfo): Bool :=
  let t := ci.toConstantVal.type
  let n' := ci.name
  let blackList := [`HasDerivAt.real_of_complex, `DifferentiableAt.hasDerivAt,
    `Complex.hasDerivAt_exp, `Complex.hasDerivAt_sinh, `Complex.hasDerivAt_sin, `Complex.hasDerivAt_cos,
    `Complex.hasDerivAt_cosh, `Complex.hasDerivAt_tan]
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
-/
initialize derivThmList: EnvExtension (List Name) ← do
  registerEnvExtension (return [])

public initialize domainExt: EnvExtension (List Expr) ←
  registerEnvExtension (return ([]))

def arity (env: Environment) (n:Name): Nat :=
  let ty := env.find? n
  match ty with
  | some ci => ci.type.getForallArity
  | _ => 0

public def db: ListThmDB := {
}

/-
def populateExt : TermElabM (List ConstantInfo) := do
  let env ← getEnv
  let cs := SMap.toList (env.constants)
  let thms' := /- Prod.fst <| List.unzip <| -/ (cs.map (Prod.snd)).filter ((isDerivTheorem env))
  let thms := List.mergeSort thms' (λ a b ↦ (a.type.getForallArity ≤ b.type.getForallArity))
  --setEnv <| derivExt.setState env thms
  db.init thms
  return thms
-/

end AR.Tools.Context
