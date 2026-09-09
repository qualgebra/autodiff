/-
  Metaprogramming logic for finding theorems in the current
  context. Based on an example from The Hitchhiker's Guide
  to Logical Verification, Chapter 8.
-/
module

public meta import Autodiff.EnvExts
public meta import Batteries.Lean.Meta.InstantiateMVars
public meta import Lean.Meta.Tactic.Apply
public meta import Lean.Elab.Tactic.Basic

open Lean Meta Elab.Tactic Meta.Tactic
open Lean Elab Command Lean.Meta Lean.Elab.Term Lean.Elab.Tactic
open Lean.Parser.Term Elab.Tactic Meta.Tactic
open Lean.Parser.Command
open Meta
open Std

namespace AR.Tools.Context

set_option maxHeartbeats 100000

meta def applyConstant (name: Expr): TacticM Unit := do
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

meta def getFullTargetType: TacticM (Expr × Expr):= do
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

meta def getAppHead: Expr → Name
| .const n _ => n
| .app t₁ _ => getAppHead t₁
| _ => Name.anonymous

def simplifyGoals: Bool := false --true

mutual
meta partial def differentiate (history domain': List Expr): TacticM (List Expr) := do
  let mut domain := domain'

  let mut goal ← getMainGoal
  -- if simplifyGoals then
  --   logInfo m!"goal before simplification: {← goal.getType}"
  --   let simpTac ← `(tactic| simp)
  --   let subgoals ← runTactic goal simpTac
  --   logInfo m!"subgoals: {subgoals.1}"
  --   if h: subgoals.1 ≠ [] then
  --      goal := subgoals.1.head h

  let t ← goal.getType
  -- logInfo m!"goal: {t}"

  let h ← history.findM? (isDefEq . t)
  if h.isSome then
    --logInfo m!"already in history: {t}"
    failure

  let blackList := [`DifferentiableAt, `HasFPowerSeriesAt, `HasDerivWithinAt,
                    `DifferentiableOn, `HasStrictDerivAt, `HasFDerivAt]
  if blackList.any (t.isAppOf) then
    --logInfo m!"goal {t} ignored."
    failure

  let appHead ← do
    match t with
    | .app (.app (.app t₁ (.lam _ _ (.app s₁ _) _)) _) _ =>
        --logInfo m!"target type: {t} - app of {t₁} --> ({s₁}) ({s₂}) --> {t₃} --> {t₄}"
        if !(t₁.isAppOf `HasDerivAt) then
          logInfo m!"expecting an application of HasDerivAt. Got {t₁.dbgToString}"
          failure
        let h := getAppHead s₁
        --logInfo m!"appHead: {h}"
        pure h
    | _ => --logInfo "not well-formed {t}";
              pure t.constName

  --logInfo m!"proveDirect: trying to prove {goal}"
  --let env ← getEnv
  let size ← ThmDB.size db
  if size = 0 then
    ThmDB.init db
    --logInfo m!"DB size: {← ThmDB.size db}"

  let mut thms ← ThmDB.lookup db appHead -- derivExt.getState env
  --if thms.isEmpty then
  --  thms ← populateExt

  --logInfo m!"theorems: {thms.map ConstantInfo.name}"
  for th in thms do
    let cst ← Meta.mkConstWithFreshMVarLevels th.name
    --logInfo m!"trying --> {cst}"
    try
      applyConstant cst
      -- logInfo m!"Proved directly by {th.name}"

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
            -- logInfo m!"extending domain with {t}"
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
