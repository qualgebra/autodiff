/-
  Metaprogramming logic for finding theorems in the current
  context. Based on an example from The Hitchhiker's Guide
  to Logical Verification, Chapter 8.
-/
import Autodiff.EnvExts
import Batteries.Lean.Meta.InstantiateMVars

open Lean Meta Elab.Tactic Meta.Tactic
open Lean Elab Command Lean.Meta Lean.Elab.Term
open Lean.Parser.Term Elab.Tactic Meta.Tactic
open Lean.Parser.Command
open Meta
open Std

namespace AR.Tools.Context

set_option maxHeartbeats 100000

def applyConstant (name: Expr): TacticM Unit := do
  -- name to expression
  -- applies cst to the current goal,
  -- setting ?m := cst ?m₁ ... ?mₙ and returning
  -- the fresh variables ?mⱼ, which represent the
  -- premises of cst
  let f := λ goal ↦ MVarId.apply goal name
  -- retrieve the identifier of the first goal,
  -- run f on the goal within MetaM, and replace
  -- the goal with the subgoals returned by f
  liftMetaTactic f

def getFullTargetType: TacticM (Expr × Expr):= do
  withMainContext (
    do
      let target ← getMainTarget
      let lctx ← getLCtx

      let mut res : List LocalDecl := []
      for ldecl in lctx do
        if ! LocalDecl.isImplementationDetail ldecl && ldecl.type.isConst then
          res := ldecl :: res
      let ids := res.map (Expr.fvar ∘ LocalDecl.fvarId)
      let e := lctx.mkLambda ids.toArray target
      return ⟨e, ← inferType e⟩
  )

mutual

partial def differentiate (history domain': List Expr): TacticM (List Expr) := do
  let mut domain := domain'

  let goal ← getMainGoal
  let t ← goal.getType
  let h ← history.findM? (λ e ↦ do (isDefEq e t))
  if h.isSome then
    --logInfo m!"already in history: {t}"
    failure

  let blackList := [`DifferentiableAt, `HasFPowerSeriesAt, `HasDerivWithinAt,
                    `DifferentiableOn, `HasStrictDerivAt, `HasFDerivAt]
  if blackList.any (λ n ↦ t.isAppOf n) then
    --logInfo m!"goal {t} ignored."
    failure

  --logInfo m!"proveDirect: trying to prove {goal}"
  let env ← getEnv
  let mut thms := derivExt.getState env
  if thms.isEmpty then
    thms ← populateExt

  for name in thms do
    let cst ← Meta.mkConstWithFreshMVarLevels name
    --logInfo m!"trying --> {cst}"
    try
      applyConstant cst
      --logInfo m!"Proved directly by {name}"

      let subgoals₁ ← getUnsolvedGoals
      for g in subgoals₁ do
        let assigned ← MVarId.isAssigned g
        -- if the subgoal metavariable is already instantiated (assigned),
        -- it has been solved already
        if ! assigned then
          g.instantiateMVars
          if ! (← g.getType).hasMVar then
            let _ ← getFullTargetType
            let t ← g.getType
            if ! domain.contains t then
              domain := t :: domain
            --logInfo m!"extending domain with {t}"
            g.admit
          else
            setGoals [g]
            domain ← differentiate (t :: history) domain

      if ! (← goal.isAssigned) then
        domain ← differentiate (t :: history) domain
      return domain
    catch _ => continue
  if ! (← goal.isAssigned) || (← goal.getType).hasMVar then
    failure
  return domain
end -- mutual

elab "difftac" : tactic => do
  let d ← differentiate [] []

  let env ← getEnv
  setEnv <| domainExt.setState env d

end AR.Tools.Context
