import Autodiff.Differentiate

-- set_option maxHeartbeats 2000000

noncomputable def test0 :=
  fun x => 4 - Real.exp (x ^ 1 / (92 - x ^ 1)) - ( (38 / x ^ 1) / Real.cos (x ^ 1))

let test0' := differentiate test0

#print test0'

noncomputable def test1 :=
  fun x => (Real.cos (Real.sin (x ^ 1)) + Real.exp (-88) / Real.exp 74) / x ^ 1 * ((Real.exp (x ^ 1 * 1) + x ^ 1) / 50)

--let test1' := differentiate test1
