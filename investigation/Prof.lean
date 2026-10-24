module
import Autodiff.Differentiate
import all Mathlib.Data.Real.Basic
set_option maxHeartbeats 1000000
set_option linter.auxLemma false

noncomputable def u0 := fun x: Real => Real.sin (x ^ 1) * Real.cos (x ^ 1) + 7 * x ^ 1
noncomputable def test0 :=
  fun x: Real => 4 - (x ^ 1 / (92 - x ^ 2)) - ( (38 / x ^ 5) / Real.cos (x ^ 3))

-- warm-up (populates DB)
def w := fun x: Real => x ^ 1
let w' := differentiate w

set_option profiler true in
let u0' := differentiate u0

set_option profiler true in
let test0' := differentiate test0
