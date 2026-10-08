import BesselProofAgent

namespace BesselAgentCandidate

theorem step_1 (n : ℤ) (x : ℝ) (hx : 0 < x) :
    ((BesselProofAgent.J (-n) x) + (BesselProofAgent.J n (-x))) = ((((-1 : ℂ) ^ n) * (BesselProofAgent.J n x)) + (BesselProofAgent.J n (-x))) := by
  (try simp only [BesselProofAgent.argument_neg, BesselProofAgent.order_neg, ← mul_assoc, BesselProofAgent.sign_cancel, BesselProofAgent.sign_mul_self, one_mul, neg_neg]) <;> ring

theorem step_2 (n : ℤ) (x : ℝ) (hx : 0 < x) :
    ((((-1 : ℂ) ^ n) * (BesselProofAgent.J n x)) + (BesselProofAgent.J n (-x))) = ((((-1 : ℂ) ^ n) * (BesselProofAgent.J n x)) + (((-1 : ℂ) ^ n) * (BesselProofAgent.J n x))) := by
  (try simp only [BesselProofAgent.argument_neg, BesselProofAgent.order_neg, ← mul_assoc, BesselProofAgent.sign_cancel, BesselProofAgent.sign_mul_self, one_mul, neg_neg]) <;> ring

theorem step_3 (n : ℤ) (x : ℝ) (hx : 0 < x) :
    ((((-1 : ℂ) ^ n) * (BesselProofAgent.J n x)) + (((-1 : ℂ) ^ n) * (BesselProofAgent.J n x))) = ((2 : ℂ) * (((-1 : ℂ) ^ n) * (BesselProofAgent.J n x))) := by
  ring

theorem target : ∀ (n : ℤ) (x : ℝ), 0 < x → ((BesselProofAgent.J (-n) x) + (BesselProofAgent.J n (-x))) = ((2 : ℂ) * (((-1 : ℂ) ^ n) * (BesselProofAgent.J n x))) := by
  intro n x hx
  calc
    ((BesselProofAgent.J (-n) x) + (BesselProofAgent.J n (-x))) = ((((-1 : ℂ) ^ n) * (BesselProofAgent.J n x)) + (BesselProofAgent.J n (-x))) := step_1 n x hx
    _ = ((((-1 : ℂ) ^ n) * (BesselProofAgent.J n x)) + (((-1 : ℂ) ^ n) * (BesselProofAgent.J n x))) := step_2 n x hx
    _ = ((2 : ℂ) * (((-1 : ℂ) ^ n) * (BesselProofAgent.J n x))) := step_3 n x hx

end BesselAgentCandidate

#eval IO.println "BESSEL_AUDIT_BEGIN"
#print axioms BesselAgentCandidate.target
#eval IO.println "BESSEL_AUDIT_END"
