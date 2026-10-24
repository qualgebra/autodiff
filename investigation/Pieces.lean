module
import Autodiff.Differentiate
import all Mathlib.Data.Real.Basic
set_option maxHeartbeats 1000000
set_option linter.auxLemma false
noncomputable def p1 := fun x: Real => x ^ 1
noncomputable def p2 := fun x: Real => 92 - x ^ 2
noncomputable def p3 := fun x: Real => x / (92 - x)
noncomputable def p4 := fun x: Real => 3 / x
noncomputable def p5 := fun x: Real => Real.cos (x ^ 3)
noncomputable def p6 := fun x: Real => Real.log x
noncomputable def p7 := fun x: Real => 4 - x
noncomputable def p8 := fun x: Real => x * x
let p1' := differentiate p1
let p2' := differentiate p2
let p3' := differentiate p3
let p4' := differentiate p4
let p5' := differentiate p5
let p6' := differentiate p6
let p7' := differentiate p7
let p8' := differentiate p8
