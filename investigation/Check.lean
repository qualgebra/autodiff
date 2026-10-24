module
import Autodiff.Differentiate
import all Mathlib.Data.Real.Basic
set_option maxHeartbeats 1000000
set_option linter.auxLemma false
noncomputable def p1 := fun x: Real => x ^ 1
noncomputable def p4 := fun x: Real => 3 / x
noncomputable def f := fun x: Real => Real.log (3 / x)
noncomputable def test0 :=
  fun x: Real => 4 - (x ^ 1 / (92 - x ^ 2)) - ( (38 / x ^ 5) / Real.cos (x ^ 3))
let p1' := differentiate p1
let p4' := differentiate p4
let f' := differentiate f
let test0' := differentiate test0
#print p1'
#print f'
#print test0'
#print axioms test0'
#print axioms p1'
#print axioms p4'
#print axioms f'
#print f'._proof_1
