module

import Autodiff.Differentiate

import all Mathlib.Data.Real.Basic

set_option maxHeartbeats 1000000

-- disabling auxiliary lemma naming warnings for now,
-- until we figure out how to get rid of those auxiliary
-- lemmas altogether.
set_option linter.auxLemma false

def f (x: Real) := x^2 + 3
let f' := differentiate f

/--
info:
private def f' : AR.Tools.AutoDiff.Differentiate.CDeriv f :=
{ f' := fun x => 2 * x ^ (2 - 1), domain := fun x => True, proof := f'._proof_3 }
-/
#guard_msgs in
#print f'

/--
info:
private theorem f'._proof_3 : ∀ (x : ℝ), True → HasDerivAt f (2 * x ^ (2 - 1)) x :=
id fun x a => HasDerivAt.add_const 3 (hasDerivAt_pow 2 x)
-/
#guard_msgs in
#print f'._proof_3

noncomputable def test0 :=
  fun x: Real => 4 - (x ^ 1 / (92 - x ^ 2)) - ( (38 / x ^ 5) / Real.cos (x ^ 3))

let test0' := differentiate test0

/--
info:
private def test0' : AR.Tools.AutoDiff.Differentiate.CDeriv test0 :=
{
  f' := fun x =>
    -(Real.one * (92 - x ^ 2)⁻¹ + x ^ 1 * (-((92 - x ^ 2) ^ 2)⁻¹ * -(2 * x ^ (2 - 1)))) +
      -(38 * (-((x ^ 5) ^ 2)⁻¹ * (5 * x ^ (5 - 1))) * (Real.cos (x ^ 3))⁻¹ +
          38 / x ^ 5 * (-(Real.cos (x ^ 3) ^ 2)⁻¹ * (-Real.sin (x ^ 3) * (3 * x ^ (3 - 1))))),
  domain := fun x => (Real.cos (x ^ 3) ≠ 0 ∧ x ^ 5 ≠ 0) ∧ 92 - x ^ 2 ≠ 0, proof := test0'._proof_2 }
-/
#guard_msgs in
#print test0'

/--
info:
private theorem test0'._proof_2 : ∀ (x : ℝ),
  (Real.cos (x ^ 3) ≠ 0 ∧ x ^ 5 ≠ 0) ∧ 92 - x ^ 2 ≠ 0 →
    HasDerivAt test0
      (-(Real.one * (92 - x ^ 2)⁻¹ + x ^ 1 * (-((92 - x ^ 2) ^ 2)⁻¹ * -(2 * x ^ (2 - 1)))) +
        -(38 * (-((x ^ 5) ^ 2)⁻¹ * (5 * x ^ (5 - 1))) * (Real.cos (x ^ 3))⁻¹ +
            38 / x ^ 5 * (-(Real.cos (x ^ 3) ^ 2)⁻¹ * (-Real.sin (x ^ 3) * (3 * x ^ (3 - 1))))))
      x :=
id fun x a =>
  HasDerivAt.add
    (HasDerivAt.const_add 4
      (HasDerivAt.fun_neg
        (HasDerivAt.fun_mul (hasDerivAt_const_mul Real.one)
          (HasDerivAt.comp x (hasDerivAt_inv a.right)
            (HasDerivAt.const_add 92 (HasDerivAt.fun_neg (hasDerivAt_pow 2 x)))))))
    (HasDerivAt.fun_neg
      (HasDerivAt.fun_mul
        (HasDerivAt.const_mul 38 (HasDerivAt.comp x (hasDerivAt_inv a.left.right) (hasDerivAt_pow 5 x)))
        (HasDerivAt.comp x (hasDerivAt_inv a.left.left) (HasDerivAt.cos (hasDerivAt_pow 3 x)))))
-/
#guard_msgs in
#print test0'._proof_2

noncomputable def test1 :=
  fun x: Real => (Real.cos (Real.sin (x ^ 1)) + (x ^ 88)) / x ^ 1 * (((x ^ 1 * 1) + x ^ 1) / 50)

let test1' := differentiate test1

/--
info:
private def test1' : AR.Tools.AutoDiff.Differentiate.CDeriv test1 :=
{
  f' := fun x =>
    ((-Real.sin (Real.sin (x ^ 1)) * (Real.cos (x ^ 1) * Real.one) + 88 * x ^ (88 - 1)) * (x ^ 1)⁻¹ +
          (Real.cos (Real.sin (x ^ 1)) + x ^ 88) * (-((x ^ 1) ^ 2)⁻¹ * Real.one)) *
        ((x ^ 1 * 1 + x ^ 1) / 50) +
      (Real.cos (Real.sin (x ^ 1)) + x ^ 88) / x ^ 1 * ((Real.one * 1 + Real.one) * 50⁻¹),
  domain := fun x => x ^ 1 ≠ 0, proof := test1'._proof_2 }
-/
#guard_msgs in
#print test1'

/--
info:
private theorem test1'._proof_2 : ∀ (x : ℝ),
  x ^ 1 ≠ 0 →
    HasDerivAt test1
      (((-Real.sin (Real.sin (x ^ 1)) * (Real.cos (x ^ 1) * Real.one) + 88 * x ^ (88 - 1)) * (x ^ 1)⁻¹ +
            (Real.cos (Real.sin (x ^ 1)) + x ^ 88) * (-((x ^ 1) ^ 2)⁻¹ * Real.one)) *
          ((x ^ 1 * 1 + x ^ 1) / 50) +
        (Real.cos (Real.sin (x ^ 1)) + x ^ 88) / x ^ 1 * ((Real.one * 1 + Real.one) * 50⁻¹))
      x :=
id fun x a =>
  HasDerivAt.fun_mul
    (HasDerivAt.fun_mul
      (HasDerivAt.add (HasDerivAt.cos (HasDerivAt.sin (hasDerivAt_const_mul Real.one))) (hasDerivAt_pow 88 x))
      (HasDerivAt.comp x (hasDerivAt_inv a) (hasDerivAt_const_mul Real.one)))
    (HasDerivAt.mul_const
      (HasDerivAt.add (HasDerivAt.mul_const (hasDerivAt_const_mul Real.one) 1) (hasDerivAt_const_mul Real.one)) 50⁻¹)
-/
#guard_msgs in
#print test1'._proof_2

noncomputable def test2 := Real.tan ∘ Real.cos

let test2' := differentiate test2

/--
info:
private def test2' : AR.Tools.AutoDiff.Differentiate.CDeriv test2 :=
{ f' := fun x => 1 / Real.cos (Real.cos x) ^ 2 * -Real.sin x, domain := fun x => Real.cos (Real.cos x) ≠ 0,
  proof := test2'._proof_1 }
-/
#guard_msgs in
#print test2'

/--
info:
private theorem test2'._proof_1 : ∀ (x : ℝ),
  Real.cos (Real.cos x) ≠ 0 → HasDerivAt test2 (1 / Real.cos (Real.cos x) ^ 2 * -Real.sin x) x :=
id fun x a => HasDerivAt.tan' a (Real.hasDerivAt_cos x)
-/
#guard_msgs in
#print test2'._proof_1

noncomputable def test3 := fun x: Real => Real.tan (Real.log x) --((Real.sin x ^ 1))

let test3' := differentiate test3

/--
info:
private def test3' : AR.Tools.AutoDiff.Differentiate.CDeriv test3 :=
{ f' := fun x => 1 / Real.cos (Real.log x) ^ 2 * x⁻¹, domain := fun x => x ≠ 0 ∧ Real.cos (Real.log x) ≠ 0,
  proof := test3'._proof_1 }
-/
#guard_msgs in
#print test3'

/--
info:
private theorem test3'._proof_1 : ∀ (x : ℝ),
  x ≠ 0 ∧ Real.cos (Real.log x) ≠ 0 → HasDerivAt test3 (1 / Real.cos (Real.log x) ^ 2 * x⁻¹) x :=
id fun x a => HasDerivAt.tan' a.right (Real.hasDerivAt_log a.left)
-/
#guard_msgs in
#print test3'._proof_1

noncomputable def test4 := fun x: Real => /-Real.exp-/ (Real.log (5 * 23 / x ^ 1)) -- * Real.log (Real.exp (x ^ 1))

let test4' := differentiate test4

/--
info:
private def test4' : AR.Tools.AutoDiff.Differentiate.CDeriv test4 :=
{ f' := fun x => 5 * 23 * (-((x ^ 1) ^ 2)⁻¹ * Real.one) / (5 * 23 / x ^ 1),
  domain := fun x => x ^ 1 ≠ 0 ∧ 5 * 23 / x ^ 1 ≠ 0, proof := test4'._proof_1 }
-/
#guard_msgs in
#print test4'

/--
info:
private theorem test4'._proof_1 : ∀ (x : ℝ),
  x ^ 1 ≠ 0 ∧ 5 * 23 / x ^ 1 ≠ 0 → HasDerivAt test4 (5 * 23 * (-((x ^ 1) ^ 2)⁻¹ * Real.one) / (5 * 23 / x ^ 1)) x :=
id fun x a =>
  HasDerivAt.log' a.right
    (HasDerivAt.const_mul (5 * 23) (HasDerivAt.comp x (hasDerivAt_inv a.left) (hasDerivAt_const_mul Real.one)))
-/
#guard_msgs in
#print test4'._proof_1

/- This examples times out
noncomputable def test5 := fun x: Real => Real.sin (Real.sin (Real.sin (Real.log x)))

let test5' := differentiate test5
#print test5'
-/

noncomputable def test6 := fun x: Real => Real.cos (Real.cos (Real.tan (x ^ 1))) + Real.tan (Real.tan (x ^ 1))

let test6' := differentiate test6

/--
info:
private def test6' : AR.Tools.AutoDiff.Differentiate.CDeriv test6 :=
{
  f' := fun x =>
    -Real.sin (Real.cos (Real.tan (x ^ 1))) * (-Real.sin (Real.tan (x ^ 1)) * (1 / Real.cos (x ^ 1) ^ 2 * Real.one)) +
      1 / Real.cos (Real.tan (x ^ 1)) ^ 2 * (1 / Real.cos (x ^ 1) ^ 2 * Real.one),
  domain := fun x => Real.cos (Real.tan (x ^ 1)) ≠ 0 ∧ Real.cos (x ^ 1) ≠ 0, proof := test6'._proof_1 }
-/
#guard_msgs in
#print test6'

/--
info:
private theorem test6'._proof_1 : ∀ (x : ℝ),
  Real.cos (Real.tan (x ^ 1)) ≠ 0 ∧ Real.cos (x ^ 1) ≠ 0 →
    HasDerivAt test6
      (-Real.sin (Real.cos (Real.tan (x ^ 1))) *
          (-Real.sin (Real.tan (x ^ 1)) * (1 / Real.cos (x ^ 1) ^ 2 * Real.one)) +
        1 / Real.cos (Real.tan (x ^ 1)) ^ 2 * (1 / Real.cos (x ^ 1) ^ 2 * Real.one))
      x :=
id fun x a =>
  HasDerivAt.add (HasDerivAt.cos (HasDerivAt.cos (HasDerivAt.tan' a.right (hasDerivAt_const_mul Real.one))))
    (HasDerivAt.tan' a.left (HasDerivAt.tan' a.right (hasDerivAt_const_mul Real.one)))
-/
#guard_msgs in
#print test6'._proof_1

namespace demo
open Real

noncomputable def f := λ x:ℝ ↦ log (3 / x)
let f' := differentiate f

/--
info:
private def demo.f' : AR.Tools.AutoDiff.Differentiate.CDeriv f :=
{ f' := fun x => 3 * -(x ^ 2)⁻¹ / (3 / x), domain := fun x => x ≠ 0 ∧ 3 / x ≠ 0, proof := f'._proof_1 }
-/
#guard_msgs in
#print f'

/--
info:
private theorem demo.f'._proof_1 : ∀ (x : ℝ), x ≠ 0 ∧ 3 / x ≠ 0 → HasDerivAt f (3 * -(x ^ 2)⁻¹ / (3 / x)) x :=
id fun x a => HasDerivAt.log' a.right (HasDerivAt.const_mul 3 (hasDerivAt_inv a.left))
-/
#guard_msgs in
#print f'._proof_1

end demo
