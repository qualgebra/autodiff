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

--partial def proveUsingTheorem (name: Name): TacticM Unit :=
--  applyConstant name

partial def proveDirect (history domain': List Expr): TacticM (List Expr) := do
  let mut domain := domain'

  --let domainPredStx ← `($(mkIdent `Real) → Prop)
  --let domainPredT ← Tactic.elabTerm domainPredStx none

  --let origGoals ← getUnsolvedGoals
  --logInfo m!"remaining goals: {origGoals}"
  let goal ← getMainGoal
  let t ← goal.getType
  let h ← history.findM? (λ e ↦ do (isDefEq e t))
  if h.isSome then
    --logInfo m!"already in history: {t}"
    failure

  --logInfo m!"context:"
  --let lctx ← getLCtx
  --for ldecl in lctx do
  --  logInfo m!"    {ldecl.userName} : {ldecl.type}"

  --let derivFn := `HasDerivAt
  let blackList := [`DifferentiableAt, `HasFPowerSeriesAt, `HasDerivWithinAt,
                    `DifferentiableOn, `HasStrictDerivAt, `HasFDerivAt]
  if blackList.any (λ n ↦ t.isAppOf n) then
    --logInfo m!"goal {t} ignored."
    failure

  --let mut domain := [] --← Tactic.elabTerm (← `(λ x ↦ True)) none
  --logInfo m!"proveDirect: trying to prove {goal}"
  --setGoals [goal]
  let env ← getEnv
  let mut thms := derivExt.getState env
  if thms.isEmpty then
    thms ← populateExt

  --let mvars ← getMVars t
  --let mvtypes ← mvars.mapM (λ v ↦ v.getType)
  --logInfo m!"mvars: {mvtypes}"

  --logInfo m!"domain mvarID: {domainMvar}"

  --let derivFn := `HasDerivAt
  for name in thms do
    let cst ← Meta.mkConstWithFreshMVarLevels name
    --logInfo m!"trying --> {cst}"
    try
      applyConstant cst
      --goal.instantiateMVars
      --goal.instantiateMVars
      --logInfo m!"Proved directly by {name}"

      let subgoals₁ ← getUnsolvedGoals
      --let mut newGoals := []
      for g in subgoals₁ do
        let assigned ← MVarId.isAssigned g
        -- if the subgoal metavariable is already instantiated (assigned),
        -- it has been solved already
        if ! assigned then
          g.instantiateMVars
      --    let g' ← g.getType
          --if Expr.isConst g' || Expr.isAppOf g' derivFn then
      --    logInfo m!"packing {g'}"
      --    newGoals := newGoals ++ [g]
          --else
          --  logInfo m!"ignoring {g'}"
          --  failure
          --logInfo m!"subgoal Mvar: {g}"
          if ! (← g.getType).hasMVar then
            let _ ← getFullTargetType
          --logInfo m!"main target: {mt}"
          --if (← isDefEq t' domainPredT) && ! t.hasMVar then
            --logInfo m!"debugging t: {target} {t'}"
            --domain := target :: domain
            --if ! (← domainMvar.getType).hasMVar then
            --  let andOp ← mkConst `and []
            --  let cur_d ← instantiateMVars (Expr.mvar domainMvar)
            --  let new_d := mkApp2 andOp cur_d target
            --  logInfo m!"updating domainMvar from {cur_d} to {new_d}"
            --  domainMvar.assign new_d
            --else

            --let c := Expr.mvar (← mkFreshMVarId)
            --let target := mkApp2 (mkConst `and []) c target'
            --logInfo m!"setting domainMvar to {target}"
            --domainMvar.assign target
            let t ← g.getType
            if ! domain.contains t then
              domain := t :: domain
            --domain := target :: domain
            g.admit
          else
            setGoals [g]
            domain ← proveDirect (t :: history) domain
          --let subgoals₂ ← getUnsolvedGoals
          --newGoals := newGoals ++ subgoals₂
      --newGoals := newGoals ++ origGoals.tail
      if ! (← goal.isAssigned) then
        --setGoals newGoals
        domain ← proveDirect (t :: history) domain
      --set

      --if ! origGoals.tail.isEmpty then
      --  proveDirect history

      return domain
    catch _ => continue
  if ! (← goal.isAssigned) || (← goal.getType).hasMVar then
    failure
  return domain
end -- mutual

elab "prove_direct" : tactic => do
  --let domainMVar' ← Tactic.elabTerm domainMVar'' none
  --let domainMVar := domainMVar'.mvarId!
  --let ctx ← Simp.Context.mkDefault
  --let g ← getMainGoal
  --let _ ← simpTarget g ctx
  --if ! (← getUnsolvedGoals).isEmpty then
  let d ← proveDirect [] []
  --if h: ! d.isEmpty then
  --  let domain := d.tail.foldr (mkApp2 (Expr.const `And [])) (d.head (by intros h'; simp at h; contradiction))
  --  mvExpr.mvarId!.assign domain

  --logInfo m!"prove_direct: domain returned: {d}"

  let env ← getEnv
  setEnv <| domainExt.setState env d
/-
  let domainMVar: MVarId ←
  withMainContext ( do
  let ctx ← getLCtx
  let ctxDecls := ctx.decls
  for d in ctxDecls do
    if d.isSome then
      let t := d.get!.type
      logInfo m!"context: {d.get!.userName} {t}"
      let mv := t.find? Expr.isMVar
      match mv with
      | some mv' => return mv'.mvarId!
      | _ => continue
  return MVarId.mk Name.anonymous
  )
-/

  --let gs ← get
  --logInfo m!"remaining goals: {gs}"
  --logInfo m!"domainMVar: {domainMVar} : {← domainMVar.getType}"
  --domainMVar.assign domainExpr
  --let _ ← instantiateMVars (.mvar domainMVar)

end AR.Tools.Context
