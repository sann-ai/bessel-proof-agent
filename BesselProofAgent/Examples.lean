import BesselProofAgent.Basic

namespace BesselProofAgent.Examples

example (n : ℤ) (x : ℝ) (_hx : 0 < x) :
    J n (-x) = (-1 : ℂ) ^ n * J n x := by
  simp only [BesselProofAgent.argument_neg, BesselProofAgent.order_neg,
    Int.cast_neg, Int.cast_add, Int.cast_mul] <;> ring

example (n : ℤ) (x : ℝ) (_hx : 0 < x) :
    J (-n) x = J n (-x) := by
  simp only [BesselProofAgent.argument_neg, BesselProofAgent.order_neg,
    Int.cast_neg, Int.cast_add, Int.cast_mul] <;> ring

example (n : ℤ) (x : ℝ) (_hx : 0 < x) : J (-n) (-x) = J n x := by
  simp only [BesselProofAgent.argument_neg, BesselProofAgent.order_neg,
    ← mul_assoc, BesselProofAgent.sign_cancel, one_mul, neg_neg,
    Int.cast_neg, Int.cast_add, Int.cast_mul] <;> ring

example (n : ℤ) (x : ℝ) (_hx : 0 < x) :
    (-1 : ℂ) ^ n * J n (-x) = J n x := by
  simp only [BesselProofAgent.argument_neg, BesselProofAgent.order_neg,
    ← mul_assoc, BesselProofAgent.sign_cancel, BesselProofAgent.sign_mul_self,
    one_mul, neg_neg, Int.cast_neg, Int.cast_add, Int.cast_mul] <;> ring

example : ¬ (∀ (n : ℤ) (x : ℝ), 0 < x → J n x + 1 = J n x) := by
  intro h
  have hbad := h 0 1 (by norm_num)
  first
  | (have bad : (0 : ℂ) = 1 := by linear_combination hbad; norm_num at bad)
  | (have bad : (0 : ℂ) = 1 := by linear_combination -hbad; norm_num at bad)
  | norm_num at hbad

example : ¬ (∀ (n : ℤ) (x : ℝ), 0 < x → J n x = J n x + 1) := by
  intro h
  have hbad := h 0 1 (by norm_num)
  first
  | (have bad : (0 : ℂ) = 1 := by linear_combination hbad; norm_num at bad)
  | (have bad : (0 : ℂ) = 1 := by linear_combination -hbad; norm_num at bad)
  | norm_num at hbad

#print axioms BesselProofAgent.argument_neg
#print axioms BesselProofAgent.order_neg
#print axioms BesselProofAgent.double_neg
#print axioms BesselProofAgent.recurrence_zero
#print axioms BesselProofAgent.not_forall_add_one

end BesselProofAgent.Examples
