module
import Autodiff.Differentiate
import all Mathlib.Data.Real.Basic
set_option maxHeartbeats 1000000
set_option linter.auxLemma false
def w := fun x: Real => x ^ 1
noncomputable def test0 :=
  fun x: Real => 4 - (x ^ 1 / (92 - x ^ 2)) - ( (38 / x ^ 5) / Real.cos (x ^ 3))
let w' := differentiate w
let test0' := differentiate test0
#print test0'._proof_2
