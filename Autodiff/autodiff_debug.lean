import Autodiff.Differentiate

set_option maxHeartbeats 1000000

noncomputable def f (x: Real) := x^2 + 3
let f' := differentiate f
#print f'

noncomputable def test0 :=
  fun x: Real => 4 - Real.exp (x ^ 1 / (92 - x ^ 1)) - ( (38 / x ^ 1) / Real.cos (x ^ 1))

let test0' := differentiate test0

#print test0'

noncomputable def test1 :=
  fun x: Real => (Real.cos (Real.sin (x ^ 1)) + Real.exp (-88) / Real.exp 74) / x ^ 1 * ((Real.exp (x ^ 1 * 1) + x ^ 1) / 50)

let test1' := differentiate test1

#print test1'

noncomputable def test2 := Real.tan ∘ Real.cos

let test2' := differentiate test2
#print test2'


noncomputable def test3 := fun x: Real => Real.tan (Real.log x) --((Real.sin x ^ 1))

let test3' := differentiate test3

#print test3'


noncomputable def test4 := fun x: Real => /-Real.exp-/ (Real.log (5 * 23 / x ^ 1)) -- * Real.log (Real.exp (x ^ 1))

let test4' := differentiate test4
#print test4'

noncomputable def test5 := fun x: Real => Real.sin (Real.sin (Real.sin (Real.log (1 * 80))))

let test5' := differentiate test5
#print test5'

noncomputable def test6 := fun x: Real => Real.cos (Real.cos (Real.tan (x ^ 1))) + Real.tan (Real.tan (x ^ 1))

let test6' := differentiate test6
#print test6'

namespace demo
open Real

noncomputable def f := λ x:ℝ ↦ log (3 / x)
let f' := differentiate f
#print f'
#print f'._proof_1

/-
noncomputable def deriv :=
  fun x: ℝ => 3 * -(x ^ 2)⁻¹ / (3 / x)

def domain :=
  fun x => x ≠ 0 ∧ 3 / x ≠ 0

def proof' :=
  fun (x: ℝ) (a: sorry) => HasDerivAt.log' sorry (HasDerivAt.const_mul 3 (hasDerivAt_inv sorry))

def proof :=
  fun (x: ℝ) (a: x ≠ 0 ∧ 3 / x ≠ 0) => HasDerivAt.log' a.right (HasDerivAt.const_mul 3 (hasDerivAt_inv a.left))
-/
end demo
