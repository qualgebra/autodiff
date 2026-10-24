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

  let legacy := (← IO.getEnv "AD_LEGACY").isSome
  let blackList := [`DifferentiableAt, `HasFPowerSeriesAt, `HasDerivWithinAt,
                    `DifferentiableOn, `HasStrictDerivAt, `HasFDerivAt]
  if legacy && blackList.any (t.isAppOf) then
    --logInfo m!"goal {t} ignored."
    failure
  -- the database only proves `HasDerivAt` goals
  if ! legacy && ! t.isAppOf `HasDerivAt then
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
    let t0 ← IO.monoNanosNow
    ThmDB.init db
    let t1 ← IO.monoNanosNow
    initNanosRef.modify (· + (t1 - t0))
    --logInfo m!"DB size: {← ThmDB.size db}"

  let mut thms ← ThmDB.lookup db appHead -- derivExt.getState env
  --if thms.isEmpty then
  --  thms ← populateExt

  --logInfo m!"theorems: {thms.map ConstantInfo.name}"
  for th in thms do
    let cst ← Meta.mkConstWithFreshMVarLevels th.name
    --logInfo m!"trying --> {cst}"
    try
      let t0 ← IO.monoNanosNow
      try
        applyConstant cst
      catch e =>
        let t1 ← IO.monoNanosNow
        statsRef.modify (·.push (th.name, false, t1 - t0))
        throw e
      let t1 ← IO.monoNanosNow
      statsRef.modify (·.push (th.name, true, t1 - t0))
      -- logInfo m!"Proved directly by {th.name}"

      let subgoals₁ ← getUnsolvedGoals
      for g in subgoals₁ do
        let assigned ← MVarId.isAssigned g
        -- if the subgoal metavariable is already instantiated (assigned),
        -- it has been solved already
        if ! assigned then
          g.instantiateMVars
          if ! (← g.getType).hasMVar then
            if (← IO.getEnv "AD_KEEPBUG").isSome then let _ ← getFullTargetType
            -- a domain constraint: leave it as a hole, to be filled from the
            -- domain hypothesis once the whole domain is known
            g.setKind .syntheticOpaque
            domain := .mvar g :: domain
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

-- Instrumentation (investigation branch), all opt-in via environment variables:
--   AD_STATS=1         log apply counts/timings per `difftac` call
--   AD_RECS=<file>     append one CSV line per apply attempt (theorem,success,nanos)
--   AD_LEGACY=1        original search: all theorems (incl. catch-alls), no head index
--   AD_KEEPBUG=1       restore the original `getFullTargetType` call (see B8)
elab "difftac" : tactic => do
  statsRef.set #[]
  initNanosRef.set 0
  let stats := (← IO.getEnv "AD_STATS").isSome
  let d ← try differentiate [] [] catch e =>
    if stats then
      let st ← statsRef.get
      logInfo m!"FAILED after {st.size} applies; ok: {(st.filter (·.2.1)).toList.map (·.1)}; tried: {(st.toList.map (·.1)).eraseDups}"
    throw e
  let st ← statsRef.get
  if stats then
    let ok := st.filter (·.2.1)
    let bad := st.filter (! ·.2.1)
    let sumMs (a : Array (Name × Bool × Nat)) := (a.foldl (· + ·.2.2) 0) / 1000000
    let dbSize ← ThmDB.size db
    logInfo m!"STATS db={dbSize} initMs={(← initNanosRef.get) / 1000000} applies={st.size} ok={ok.size} okMs={sumMs ok} fail={bad.size} failMs={sumMs bad}"
    let top := (bad.qsort (·.2.2 > ·.2.2)).extract 0 15
    logInfo m!"TOPFAIL {top.toList.map (fun (n, _, t) => (n, t / 1000000))}"
    logInfo m!"OK {ok.toList.map (fun (n, _, t) => (n, t / 1000000))}"
  if let some path ← IO.getEnv "AD_RECS" then
    let h ← IO.FS.Handle.mk path IO.FS.Mode.append
    h.putStrLn "RUN"
    for (n, b, t) in st do h.putStrLn s!"{n},{b},{t}"

  let env ← getEnv
  setEnv <| domainExt.setState env d

end AR.Tools.Context
