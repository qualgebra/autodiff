import Lean
import Lean.Elab.Term

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Shift

import Autodiff.FindTheorems
import Autodiff.EnvExts

open Lean Elab Command Lean.Meta Lean.Elab.Term
open Lean.Parser.Term Elab.Tactic Meta.Tactic
open Lean.Parser.Command
open Meta
open Std

def RealOfNat (n: ℕ): ℝ  := @Nat.cast ℝ _ n

namespace AR.Tools.AutoDiff.Differentiate

def domanBVar := Expr.bvar 0
def xBVar := Expr.bvar 1

def buildDomainExpr (d: List Expr) :=
  --let d := d'.map (λ e ↦ mkApp e xBVar)
  let t_const := Lean.mkConst `True []
  let domainExpr' := if d.length == 0 then t_const
                     else if d.length == 1 then d.head!
                     else d.tail.foldl (mkApp2 (mkConst `And [])) d.head!

  let domainExpr' := mkLambda `x BinderInfo.default (mkConst `Real []) domainExpr'

  match domainExpr'.find? Expr.isFVar with
  | some fv => domainExpr'.replaceFVar fv (mkConst `x [])
  | _ => domainExpr'

partial def runTactic' (f: TSyntax `ident): TermElabM (Expr × Expr × Expr × List Expr) := do
  let derivFn := `HasDerivAt
  let realT := mkIdent `Real
  let x_id := mkIdent `x
  --let domainTStx ← `(Real → Prop)
  --let mv ← mkFreshMVarId

  let tr ← `(∀ ($x_id : $realT), (((?_ $x_id): Prop) → $(mkIdent derivFn) $f (_:$realT) $x_id))

  let goalExpr ← Term.elabTerm tr none
  let mvars ← getMVars goalExpr
  --let mvtypes ← mvars.mapM (λ v ↦ v.getType)
  --logInfo m!"mvars: {mvtypes}"
  --let goal ← `($tr = (_ : $trType))

  /-
  let env ← getEnv
  let mut lemmas := Context.derivExt.getState env
  if lemmas.isEmpty then
    lemmas ← AR.Tools.Context.populateExt
  let lemIds := List.toArray <| lemmas.map mkIdent
  let t ← `(tactic| intros; apply_assumption [$[$lemIds:ident],*])
  -/
  --logInfo m!"trying to prove {tr}" --" -- trType: {trType}"
  --logInfo m!"tactic: {t}"
  let goalMV ← mkFreshExprMVar (some goalExpr)
  --let domainT ← Term.elabTerm domainTStx none
  --let domainMV ← mkFreshExprMVar (some domainT)
  --let domainMVStx ← PrettyPrinter.delab domainMV

  let resultMVar := mvars[1]!
  let domainMVar := mvars[0]!
  --let domainMVar' ← PrettyPrinter.delab (Expr.mvar domainMVar)

  let t ←
    --match f with
    --| some f' =>
    `(tactic| unfold $f; intros; prove_direct)
    --|_ => `(tactic| intros; prove_direct)

  let _ ← runTactic goalMV.mvarId! t
  --logInfo m!"returned list of MvarIds: {xs.fst}"
  --logInfo m!"goalMV is assigned: {← goalMV.mvarId!.isAssigned} {goalMV.mvarId!}"

  -- simplifications
  --let ctx ← Simp.Context.mkDefault
  --let _ ← simpTarget resultMVar ctx
  --let _ ← simpTarget domainMVar ctx
  --let _ ← simpTarget goalMV.mvarId! ctx

  let result ← instantiateMVars (Expr.mvar resultMVar)

  --logInfo m!"domainMVar: {domainMVar} {domainMVar.name} {← domainMVar.getType} {← domainMVar.isAssigned}"
  --if ! (← domainMVar.isAssigned) then
  --  let predStx ← `(λ _:Real ↦ True)
  --  domainMVar.assign (← Term.elabTerm predStx none)

  let env ← getEnv
  let d := AR.Tools.Context.domainExt.getState env
  let domainExpr := buildDomainExpr d
  domainMVar.assign domainExpr

  --logInfo m!"domain expression {domainExpr}"

  let domain ← instantiateMVars (Expr.mvar domainMVar)
  --let derivFn := `HasDerivAt
  let proof ← instantiateMVars goalMV
  --logInfo m!"domain: {domain}"
  --logInfo m!"result: {result}"
  --logInfo m!"proof:  {proof}"
  --logInfo m!"proof type: {goalExpr}"
  --if result.isAppOf derivFn then
  --  let newGoal ← PrettyPrinter.delab result
  --  let (res, prf) ← runTactic' none newGoal trType
  --  let trans ← Term.elabTerm (← `(Eq.trans)) none
  --  return (res, Expr.app (Expr.app trans proof) prf)
  --else
    return (result, domain, proof, d)

-- certified derivative structure
structure CDeriv {α β: Type}
  [NontriviallyNormedField α]
  [AddCommGroup β]
  [_root_.Module α β]
  [TopologicalSpace β]
  [ContinuousSMul α β]
  (f: α → β)
where
  f': α → β
  domain: α → Prop
  proof: ∀ (x:α) (_: domain x), HasDerivAt f (f' x) x

  --logInfo m!"prove_direct: domain expression: {domainExpr}"

def buildDomainSelector (sorryT: Expr): List Expr → Expr
| [] => sorryT -- mkApp domanBVar xBVar
| x' :: xs =>
    let x := x'.replace
      (λ e ↦ match e with
             | .lam _ _ b _ => b
             | .fvar _ => xBVar
             | _ => e)

    --let tmpName := `temp
    --let tmp := Lean.mkConst tmpName []
    --let propT := Lean.mkConst `Prop []
    let anon := Lean.mkConst `_ []
    --let conj := Lean.mkConstEx ``And.left []
    --let l (e: Expr) := mkHave tmpName propT domanBVar (mkApp3 e anon conj tmp)

    if x.eqv sorryT
    then (if xs.isEmpty then domanBVar else mkApp3 (mkConst `And.left []) anon anon domanBVar)
    else mkApp3 (mkConst `And.right) anon anon (buildDomainSelector sorryT xs)

partial def prepareProof (prf: Expr) (d': List Expr): CommandElabM Expr := do
  let d :=  d'.map (Expr.replace (λ e ↦ if e.isFVar then some xBVar else none))

  --logInfo m!"domain predicates: {d}"
  let s' := prf.find? Expr.isSorry
  let t ←
    match s' with
    | some s => liftTermElabM <| inferType s --logInfo m!"sorry type: {← liftTermElabM <|inferType s}"
    | _ => return prf --logInfo m!"sorry not found"
  --logInfo m!"sorry: {s'}:{t}"

  prepareProof
    (prf.replace
      (λ e ↦
        if e == s' then some (buildDomainSelector t d) else none))
    d

def fixNatCast (p: Expr): Expr :=
  p.replace (λ e ↦ if e.isAppOf `Nat.cast
                   then let as := e.getAppArgs
                        if as.size = 3
                        then some (mkApp (Expr.const `RealOfNat []) as[2]!)
                        else none
                   else none)

--def debugExpr (e: Expr): CommandElabM Unit := do
--  e.forEachWhere (λ e ↦ e.isAppOf `Nat.cast) (λ e ↦ logInfo m!"application: {e} {e.getAppArgs.size} {e.getAppArgs}")

set_option maxHeartbeats 2000000

elab "let " lhs: ident ":= " "differentiate " f: ident : command => do
  --let env ← getEnv
  --let fnName := f.getId
  --let fnType := env.find? fnName |> Option.get! |> ConstantInfo.toConstantVal |> ConstantVal.type
  --let fnTypeTerm ← liftTermElabM <| PrettyPrinter.delab fnType
  --let derivFn := `HasDerivAt
  --let rhs ← `(∀ x, $(mkIdent derivFn) $f (_) x)
  let (result', domain, prf', d) ← liftTermElabM <| runTactic' f --fnTypeTerm
  --debugExpr result'
  let result := fixNatCast result'
  --debugExpr result
  --logInfo m!"result term: {result}"
  let prf'' ← prepareProof prf' d
  let prf := fixNatCast prf''
  --let prfType ← liftTermElabM <| inferType prf
  let resultTerm ← liftTermElabM <| PrettyPrinter.delab result
  let domainTerm ← liftTermElabM <| PrettyPrinter.delab domain
  --let realT := mkIdent `Real

  let prfTerm ← liftTermElabM <| PrettyPrinter.delab prf
  --logInfo m!"proof term: {prfTerm}"
  --logInfo m!"proof type: {prfType}"

  let dfn ← `(noncomputable def $lhs : CDeriv $f := CDeriv.mk $resultTerm $domainTerm $prfTerm)
  --let prfDfn ← `(theorem $pr : ($rhs = $lhs) := $prfTerm)
  --let n := lhs.getId.append `proof
  --let env ← getEnv
  --setEnv <| Context.derivExt.modifyState env (λ xs ↦ n :: xs)
  elabCommand dfn
  --elabCommand prfDfn

end AR.Tools.AutoDiff.Differentiate
