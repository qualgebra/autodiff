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

/-- The domain predicate `fun x => c₁ ∧ … ∧ cₙ`, where the conjuncts are the types of the
  domain holes collected by `difftac` (newest first), without duplicates. -/
meta def buildDomain (holes: List MVarId) : MetaM Expr := do
  -- keep each conjunct at the position of its first occurrence
  let mut uniq : Array Expr := #[]
  for h in holes.reverse do
    let t ← instantiateMVars (← h.getType)
    if ! uniq.contains t then
      uniq := uniq.push t
  let body := match uniq.reverse.toList with
    | [] => mkConst ``True
    | c :: cs => cs.foldl (mkApp2 (mkConst ``And)) c
  match (collectFVars {} body).fvarIds with
  | #[] => return mkLambda `x BinderInfo.default (mkConst ``Real) body
  | #[x] => holes.head!.withContext <| mkLambdaFVars #[mkFVar x] body
  | _ => throwError "domain constraints mention more than one variable: {body}"

/-- A proof of `target` obtained by projecting the conjunction proved by `h`,
  if `target` is one of its conjuncts. -/
meta partial def projectConjunct (h target: Expr) : MetaM (Option Expr) := do
  let hType ← instantiateMVars (← inferType h)
  if ← withReducible (isDefEq hType target) then
    return some h
  match (← whnfR hType).and? with
  | some (a, b) =>
    if let some p ← projectConjunct (mkApp3 (mkConst ``And.left) a b h) target then
      return some p
    projectConjunct (mkApp3 (mkConst ``And.right) a b h) target
  | none => return none

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

elab "let " lhs: ident ":= " "differentiate " f: ident : command => liftTermElabM do
  let derivFn := `HasDerivAt
  let realT := mkIdent `Real
  let x_id := mkIdent `x

  let tr ← `(∀ ($x_id : $realT), (((?_ $x_id): Prop) → $(mkIdent derivFn) $f (_:$realT) $x_id))

  let goalExpr ← Term.elabTerm tr none
  let mvars ← getMVars goalExpr
  let goalMV ← mkFreshExprMVar (some goalExpr)

  let resultMVar := mvars[1]!
  let domainMVar := mvars[0]!

  let t ← `(tactic| unfold $f; intros; difftac)
  let _ ← runTactic goalMV.mvarId! t

  let result ← instantiateMVars (Expr.mvar resultMVar)

  -- the domain constraints were left as holes in the proof; build the domain
  -- predicate from them, then fill each hole by projecting the domain hypothesis
  let holes := (AR.Tools.Context.domainExt.getState (← getEnv)).filterMap
    (fun e => if e.isMVar then some e.mvarId! else none)
  let domain ← buildDomain holes
  domainMVar.assign domain

  for h in holes do
    unless ← h.isAssigned do
      h.withContext do
        let some hyp := (← getLCtx).findDecl? (fun d =>
            if d.type.getAppFn.isMVar && d.type.getAppFn.mvarId! == domainMVar
            then some d.toExpr else none)
          | throwError "no domain hypothesis in the context of {mkMVar h}"
        let target ← instantiateMVars (← h.getType)
        let some p ← projectConjunct hyp target
          | throwError "no domain conjunct proves {target}"
        h.assign p

  let proof ← instantiateMVars goalMV
  if proof.hasMVar then
    throwError "incomplete derivative proof: {proof}"

  -- add the definition directly (checked by the kernel), with no
  -- pretty-print/re-elaboration round trip
  let value ← instantiateMVars (← mkAppM ``CDeriv.mk #[result, domain, proof])
  let type ← instantiateMVars (← inferType value)
  let (declName, _) ← mkDeclName (← getCurrNamespace) {} lhs.getId
  let value ← withDeclNameForAuxNaming declName <| Meta.abstractNestedProofs value
  addDecl <| .defnDecl { name := declName, levelParams := [], type, value,
                         hints := .regular (getMaxHeight (← getEnv) value + 1), safety := .safe }
  modifyEnv (addNoncomputable · declName)

end AR.Tools.AutoDiff.Differentiate
