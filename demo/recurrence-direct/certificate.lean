import BesselProofAgent

namespace BesselAgentCandidate

theorem target : ∀ (n : ℤ) (x : ℝ), 0 < x → (((BesselProofAgent.J (n - (1 : ℤ)) x) + (BesselProofAgent.J (n + (1 : ℤ)) x)) + (BesselProofAgent.J n x)) = (((((2 : ℂ) * (n : ℂ)) / (x : ℂ)) + (1 : ℂ)) * (BesselProofAgent.J n x)) := by
  intro n x hx
  have hrec := BesselProofAgent.recurrence n x hx
  first
  | linear_combination hrec
  | linear_combination -hrec
  | (try simp only [hrec]) <;> ring

end BesselAgentCandidate

#eval IO.println "BESSEL_AUDIT_BEGIN"
#print axioms BesselAgentCandidate.target
#eval IO.println "BESSEL_AUDIT_END"
