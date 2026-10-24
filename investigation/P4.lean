module
import Autodiff.Differentiate
import all Mathlib.Data.Real.Basic
set_option linter.auxLemma false
noncomputable def p4 := fun x: Real => 3 / x
let p4' := differentiate p4
