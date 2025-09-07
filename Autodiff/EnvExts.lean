/-
  environment extensions for automatic differentiation
-/
import Lean
import Lean.Elab.Term
import Lean.Elab.Deriving.Basic
import Lean.Elab.Deriving.Util
import Lean.Meta.Inductive
import Lean.Meta.Transform

open Lean Meta Elab.Tactic Meta.Tactic
open Lean Elab Command Lean.Meta Lean.Elab.Term
open Lean.Parser.Term Elab.Tactic Meta.Tactic
open Lean.Parser.Command
open Meta
open Std

namespace AR.Tools.Context

--def isTheorem: ConstantInfo → Bool
--| ConstantInfo.axiomInfo _ => True
--| ConstantInfo.thmInfo _ => True
--| _ => False

def isDerivTheorem (ci: ConstantInfo): Bool :=
  let t := ci.toConstantVal.type
  let n' := ci.name
  let blackList := [`HasDerivAt.real_of_complex, `DifferentiableAt.hasDerivAt]
  let n := Name.mkStr1 "HasDerivAt"
  --let dw := Name.mkStr1 "derivWithin"
  if (! ci.isTheorem || ! t.isForall || blackList.elem n') then
    false
  else
    let b := t.getForallBody
    let app := b.isAppOf n
    app
    --let eq? := b.eqOrIff?
    --match eq? with
    --| some (e₁,e₂) => e₁.isAppOf n
    --| _ => app

initialize derivExt: EnvExtension (List Name) ←
  registerEnvExtension (return [])

initialize domainExt: EnvExtension (List Expr) ←
  registerEnvExtension (return ([]))

def arity (env: Environment) (n:Name): Nat :=
  let ty := env.find? n
  match ty with
  | some ci => ci.type.getForallArity
  | _ => 0

def populateExt : TermElabM (List Name) := do
  let env ← getEnv
  let cs := SMap.toList (env.constants)
  let thms' := Prod.fst <| List.unzip <| cs.filter (isDerivTheorem ∘ Prod.snd)
  let thms := List.mergeSort thms' (λ a b ↦ (arity env a) ≤ (arity env b))
  setEnv <| derivExt.setState env thms
  return thms

end AR.Tools.Context
