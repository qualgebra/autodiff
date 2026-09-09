module

import Lean
public import Lean.Elab.Command
import Lean.Elab.Term
public meta import Lean.Elab.Tactic.Meta

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.Shift

public import Autodiff.FindTheorems
public meta import Autodiff.EnvExts

open Lean Elab Command Lean.Meta Lean.Elab.Term
open Lean.Parser.Term Elab.Tactic Meta.Tactic
open Lean.Parser.Command
open Meta
open Std

def RealOfNat (n: ℕ): ℝ  := @Nat.cast ℝ _ n

public theorem HasDerivAt.log' : ∀ {f : ℝ → ℝ} {x f' : ℝ}, f x ≠ 0 → HasDerivAt f f' x → HasDerivAt (fun y => Real.log (f y)) (f' / f x) x := by
  intros f x f' h₁ h₂; apply HasDerivAt.log
  exact h₂
  exact h₁

public theorem HasDerivAt.tan' {f : ℝ → ℝ} {x f': ℝ} (g: Real.cos (f x) ≠ 0) (hh : HasDerivAt f f' x):
  HasDerivAt (λ x ↦ Real.tan (f x)) (1 / Real.cos (f x) ^ 2 * f') x := by
  rw[←Function.comp_def]
  apply HasDerivAt.comp
  apply Real.hasDerivAt_tan
  exact g
  exact hh

namespace AR.Tools.AutoDiff.Differentiate

set_option maxHeartbeats 1000000

meta def domainBVar := Expr.bvar 0
meta def xBVar := Expr.bvar 1

meta def buildDomainExpr (d: List Expr) :=
  let t_const := Lean.mkConst `True []
  let domainExpr' := if d.length == 0 then t_const
                     else if d.length == 1 then d.head!
                     else d.tail.foldl (mkApp2 (mkConst `And [])) d.head!

  let domainExpr' := mkLambda `x BinderInfo.default (mkConst `Real []) domainExpr'

  match domainExpr'.find? Expr.isFVar with
  | some fv => domainExpr'.replaceFVar fv (mkConst `x [])
  | _ => domainExpr'

meta def buildDomainSelector (sorryT: Expr) (op: Expr) : List Expr → Expr
| [] => sorryT
| x' :: xs =>
    let x := x'.replace
      (λ e ↦ match e with
             | .lam _ _ b _ => b
             | .fvar _ => xBVar
             | _ => e)

    let anon := Lean.mkConst `_ []
    let l := mkApp3 (mkConst `And.left) anon anon
    let r := mkApp3 (mkConst `And.right) anon anon

    if x.eqv sorryT
    then (if xs.isEmpty then op else r op)
    else  (buildDomainSelector sorryT (l op) xs)

meta partial def prepareProof (prf: Expr) (d': List Expr): CommandElabM Expr := do
  let d :=  d'.map (Expr.replace (λ e ↦ if e.isFVar then some xBVar else none))

  let s' := prf.find? Expr.isSorry
  let t ←
    match s' with
    | some s => liftTermElabM <| inferType s
    | _ => return prf

  prepareProof
    (prf.replace
      (λ e ↦
        if e == s' then some (buildDomainSelector t domainBVar d.reverse ) else none))
    d

meta partial def runTactic' (f: TSyntax `ident): TermElabM (Expr × Expr × Expr × List Expr) := do
  let derivFn := `HasDerivAt
  let realT := mkIdent `Real
  let x_id := mkIdent `x

  let tr ← `(∀ ($x_id : $realT), (((?_ $x_id): Prop) → $(mkIdent derivFn) $f (_:$realT) $x_id))

  let goalExpr ← Term.elabTerm tr none
  let mvars ← getMVars goalExpr
  let goalMV ← mkFreshExprMVar (some goalExpr)

  --logInfo m!"goalExpr: {goalExpr} - goalMV: {goalMV}"
  let resultMVar := mvars[1]!
  let domainMVar := mvars[0]!

  let t ← `(tactic| unfold $f; intros; difftac)

  let _ ← runTactic goalMV.mvarId! t
  --logInfo m!"results: {results.1}"

  let result ← instantiateMVars (Expr.mvar resultMVar)
  --logInfo m!"result: {result}"
  let env ← getEnv
  let d := AR.Tools.Context.domainExt.getState env
  let domainExpr := buildDomainExpr d
  domainMVar.assign domainExpr

  let domain ← instantiateMVars (Expr.mvar domainMVar)
  let proof ← instantiateMVars goalMV
  --logInfo m!"domain: {domain}"
  --logInfo m!"result: {result}"
  --logInfo m!"proof:  {proof}"
  --logInfo m!"proof type: {goalExpr}"
  return (result, domain, proof, d)

-- certified derivative structure
public structure CDeriv {α β: Type}
  [NontriviallyNormedField α]
  [AddCommGroup β]
  [_root_.Module α β]
  [TopologicalSpace β]
  [ContinuousSMul α β]
  (f: α → β)
where
  f': α → β
  domain: α → Prop
  proof: ∀ (x:α), domain x → HasDerivAt f (f' x) x

/-
def fixNatCast (p: Expr): Expr :=
  p.replace (λ e ↦ if e.isAppOf `Nat.cast
                   then let as := e.getAppArgs
                        if as.size = 3
                        then some (mkApp (Expr.const `RealOfNat []) as[2]!)
                        else none
                   else none)
-/
elab "let " lhs: ident ":= " "differentiate " f: ident : command => do
  let (result', domain, prf', d) ← liftTermElabM <| runTactic' f
  let result := result' --fixNatCast result'
  let prf'' ← prepareProof prf' d
  let prf := prf'' --fixNatCast prf''
  --logInfo m!"prf'': {prf''} - prf: {prf}"
  let resultTerm ← liftTermElabM <| PrettyPrinter.delab result
  let domainTerm ← liftTermElabM <| PrettyPrinter.delab domain

  let prfTerm ← liftTermElabM <| PrettyPrinter.delab prf
  --logInfo m!"prfTerm: {prfTerm}"

  let dfn ← `(noncomputable def $lhs : CDeriv $f := CDeriv.mk $resultTerm $domainTerm $prfTerm)
  --logInfo m!"command dfn: {dfn}"
  elabCommand dfn

end AR.Tools.AutoDiff.Differentiate
