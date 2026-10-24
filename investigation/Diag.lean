module
import Autodiff.Differentiate
import all Mathlib.Data.Real.Basic
set_option maxHeartbeats 1000000
set_option linter.auxLemma false
noncomputable def test0 :=
  fun x: Real => 4 - (x ^ 1 / (92 - x ^ 2)) - ( (38 / x ^ 5) / Real.cos (x ^ 3))
def w := fun x: Real => x ^ 1
let w' := differentiate w
set_option diagnostics true in
set_option diagnostics.threshold 200 in
let test0' := differentiate test0
