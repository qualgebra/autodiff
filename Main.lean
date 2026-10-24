-- tests for automatic differentiation
import Autodiff
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Basic

open Lean Elab Command Lean.Meta Lean.Elab.Term
open Lean.Parser.Term Elab.Tactic Meta.Tactic
open Lean.Parser.Command
open Meta
open Std

set_option maxHeartbeats 1000000

def arg := "x"
def argName := mkIdent (Name.mkStr1 arg)

inductive FuncBody where
| IntLit (i:ℤ)
| Arg (p: ℤ)
| Plus (b₁ b₂: FuncBody)
| Minus (b₁ b₂: FuncBody)
| Mul (b₁ b₂: FuncBody)
| Div (b₁ b₂:FuncBody)
| Sin (p:FuncBody)
| Cos (p:FuncBody)
| Tan (p:FuncBody)
--| Exp (p:FuncBody)
| Log (p:FuncBody)

def realT := mkIdent `Real
def intT  := mkIdent `Int

def int2Syntax (i: ℤ): CommandElabM (TSyntax `term) := do
  let absv := i.natAbs
  let absvSyntax := Syntax.mkNatLit absv
  if i < 0 then
    `(- $absvSyntax)
  else `($absvSyntax)

def sinF := mkIdent `Real.sin
def cosF := mkIdent `Real.cos
def tanF := mkIdent `Real.tan
def expF := mkIdent `Real.exp
def logF := mkIdent `Real.log

def func2term: FuncBody → CommandElabM (TSyntax `term)
| .IntLit i =>      do `(($(← int2Syntax i) : ℝ))
| .Arg p =>         do `($argName ^ $(← int2Syntax p))  -- $(Syntax.mkNatLit p))
| .Plus b₁ b₂ =>    do `($(← func2term b₁) + $(← func2term b₂))
| .Minus b₁ b₂ =>   do `($(← func2term b₁) - $(← func2term b₂))
| .Mul b₁ b₂ =>     do `($(← func2term b₁) * $(← func2term b₂))
| .Div b₁ b₂ =>     do `($(← func2term b₁) / $(← func2term b₂))
| .Sin p =>         do `($sinF $(← func2term p))
| .Cos p =>         do `($cosF $(← func2term p))
| .Tan p =>         do `($tanF $(← func2term p))
--| .Exp p =>         do `($expF $(← func2term p))
| .Log p =>         do `($logF $(← func2term p))

def randInt(r:ℕ): IO Int := do
  let v ← IO.rand 0 (2*r)
  return (-(Int.ofNat r) + (Int.ofNat v))

def testRandInt: IO Unit := do
  for _ in List.range 100 do
    let v ← randInt 100
    IO.println v

--#eval testRandInt
def genFunc(d:ℕ): IO (FuncBody × ℕ × ℕ) := do
  if z: d == 0 then
    return ⟨FuncBody.IntLit (← randInt 100), 1, 1⟩
  else
    have h: 0 < d := by simp at z; exact Nat.zero_lt_of_ne_zero z
    let c ← if d ≤ 1 then pure 0 else IO.rand 0 10
    match c with
    | 0 => let v ← randInt 100
           return (FuncBody.IntLit v, 1, 1)
    | 1 => let p ← IO.rand 0 10
           return ⟨FuncBody.Arg 1 , 3, 2⟩
    | 2 => let ⟨t₁, s₁, h₁⟩ ← genFunc (d-1)
           let ⟨t₂, s₂, h₂⟩ ← genFunc (d-1)
           return ⟨FuncBody.Plus t₁ t₂, 1 + s₁ + s₂, 1 + Nat.max h₁ h₂⟩
    | 3 => let ⟨t₁, s₁, h₁⟩ ← genFunc (d-1)
           let ⟨t₂, s₂, h₂⟩ ← genFunc (d-1)
           return ⟨FuncBody.Minus t₁ t₂, 1 + s₁ + s₂, 1 + Nat.max h₁ h₂⟩
    | 4 => let ⟨t₁, s₁, h₁⟩ ← genFunc (d-1)
           let ⟨t₂, s₂, h₂⟩ ← genFunc (d-1)
           return ⟨FuncBody.Mul t₁ t₂, 1 + s₁ + s₂, 1 + Nat.max h₁ h₂⟩
    | 5 => let ⟨t₁, s₁, h₁⟩ ← genFunc (d-1)
           let ⟨t₂, s₂, h₂⟩ ← genFunc (d-1)
           return ⟨FuncBody.Div t₁ t₂, 1 + s₁ + s₂, 1 + Nat.max h₁ h₂⟩
    | 6 => let (p, s, h) ← genFunc (d-1)
           return (FuncBody.Sin p, s+1, h+1)
    | 7 => let (p, s, h) ← genFunc (d-1)
           return (FuncBody.Cos p, s+1, h+1)
    | 8 => let (p, s, h) ← genFunc (d-1)
           return (FuncBody.Tan p, s+1, h+1)
    --| 9 => let (p, s, h) ← genFunc (d-1)
    --       return (FuncBody.Exp p, s+1, h+1)
    | _ => let (p, s, h) ← genFunc (d-1)
           return (FuncBody.Log p, s+1, h+1)


def dumpTestData (outFile : IO.FS.Handle) (fnName resultName: Name): CommandElabM Unit := do
  let env ← getEnv
  let some fn := env.find? fnName | unreachable!

  outFile.putStrLn s!"Input: {fn.name}"
  outFile.putStrLn s!"{← liftTermElabM <| PrettyPrinter.ppExpr fn.value!}"
  outFile.putStrLn ""

  let some result := env.find? resultName | unreachable!

  outFile.putStrLn "Result:"
  outFile.putStrLn s!"{← liftTermElabM <| PrettyPrinter.ppExpr result.value!}"
  outFile.putStrLn ""

  -- the proof is the last argument of `CDeriv.mk`, usually an auxiliary lemma
  let prf := result.value!.getAppArgs.back!
  let prf := match prf.getAppFn with
             | .const n _ => match env.find? n with
                             | some ci => ci.value! (allowOpaque := true)
                             | none => prf
             | _ => prf

  outFile.putStrLn "Proof:"
  outFile.putStrLn s!"{← liftTermElabM <| PrettyPrinter.ppExpr prf}"
  outFile.putStrLn ""

/-- Elaborate `cmd`, returning the elapsed time in nanoseconds and whether it
  succeeded (no error messages). -/
def timedElab (cmd: Syntax): CommandElabM (Nat × Bool) := do
  let errs₀ := (← get).messages.toList.filter (·.severity == .error) |>.length
  let t₀ ← IO.monoNanosNow
  elabCommand cmd
  let t₁ ← IO.monoNanosNow
  let errs₁ := (← get).messages.toList.filter (·.severity == .error) |>.length
  return (t₁ - t₀, errs₁ == errs₀)

def fmtMs (ns: Nat): String :=
  s!"{(Float.ofNat (ns / 100000)) / 10}ms"

def runTest (i: ℕ) (ctx: Core.Context) (st: Core.State): CommandElabM Unit := do
  let ⟨b, size, depth⟩ ← genFunc 6
  let fsyntax ← func2term b

  let stderr ← IO.getStderr

  let tc ← `(λ $argName : $realT ↦ $fsyntax)
  let test := `test
  let test' := `d_test
  let fnName := Name.appendAfter test (toString i)
  let fnName' := Name.appendAfter test' (toString i)

  let outFile ← IO.FS.Handle.mk (fnName.toString ++ ".txt") IO.FS.Mode.write

  let fnCmd ← `(noncomputable def $(mkIdent fnName) : $realT → $realT := $tc)
  let derivCmd ← `(let $(mkIdent fnName') := differentiate $(mkIdent fnName))

  -- bootstrapping round (not timed)
  elabCommand fnCmd

  let env ← getEnv
  let some fn := env.find? fnName | unreachable!

  let f ← liftTermElabM <| PrettyPrinter.ppExpr fn.value!

  stderr.putStr s!"{i}, {f.pretty 100000}, {size}, {depth}"

  let (_, ok) ← timedElab derivCmd
  if ! ok then
    stderr.putStrLn ", FAIL"
    for m in (← get).messages.toList do
      outFile.putStrLn (← m.toString)
    return
  dumpTestData outFile fnName fnName'

  -- timed rounds, each from the same state: theorem database already built,
  -- test function not yet defined; only the `differentiate` command is timed
  for _ in List.range 4 do
    let ((t, ok), _) ← Lean.Core.CoreM.toIO (liftCommandElabM <| do
        elabCommand fnCmd
        timedElab derivCmd)
      ctx st
    stderr.putStr (if ok then s!", {fmtMs t}" else ", FAIL")

  stderr.putStrLn ""

unsafe def main(args: List String): IO Unit := do
  IO.println s!"{args}"

  let initIdx := if args.length > 0 then (args.head!).toNat! else 0
  -- reproducible test functions: the test index is the random seed
  IO.setRandSeed initIdx

  enableInitializersExecution

  initSearchPath (← Lean.findSysroot) ["build/lib"]

  let env ← importModules #[
    `Init,
    `Lean,
    `Autodiff,
    `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic,
    `Mathlib.Data.Real.Basic] {} 1 (loadExts := true)

  -- the heartbeat limit must be passed as an option to take effect in command
  -- elaboration; the default is Lean's own default
  let heartbeats := ((← IO.getEnv "AD_HEARTBEATS").bind String.toNat?).getD 200000
  let opts := maxHeartbeats.set Options.empty heartbeats
  let ctx: Core.Context := { fileName := "autodiff.lean", fileMap := default, options := opts }

  -- build the theorem database once, outside the timed runs
  let warmup : CommandElabM Unit := do
    elabCommand (← `(noncomputable def warmup : ℝ → ℝ := fun x => x))
    elabCommand (← `(let warmup' := differentiate warmup))
  let (_, st) ← Lean.Core.CoreM.toIO (liftCommandElabM warmup) ctx { env := env }

  let _ ← Lean.Core.CoreM.toIO (liftCommandElabM <| runTest initIdx ctx st) ctx st
