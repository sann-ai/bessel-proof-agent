import BesselProofAgent

namespace BesselAgentCandidate

theorem target : ∀ (n : ℤ) (x : ℝ), 0 < x → ((BesselProofAgent.J (-n) x) + (BesselProofAgent.J n (-x))) = ((2 : ℂ) * (((-1 : ℂ) ^ n) * (BesselProofAgent.J n x))) := by
  intro n x hx
  (try simp only [BesselProofAgent.argument_neg, BesselProofAgent.order_neg, ← mul_assoc, BesselProofAgent.sign_cancel, BesselProofAgent.sign_mul_self, one_mul, neg_neg]) <;> ring

end BesselAgentCandidate

#eval IO.println "BESSEL_AUDIT_BEGIN"
#print axioms BesselAgentCandidate.target
#eval IO.println "BESSEL_AUDIT_END"
