import BesselProofAgent

namespace BesselAgentCandidate

theorem step_1 (n : ℤ) (x : ℝ) (hx : 0 < x) :
    (((BesselProofAgent.J (n - (1 : ℤ)) x) + (BesselProofAgent.J (n + (1 : ℤ)) x)) + (BesselProofAgent.J n x)) = (((((2 : ℂ) * (n : ℂ)) / (x : ℂ)) * (BesselProofAgent.J n x)) + (BesselProofAgent.J n x)) := by
  have hrec := BesselProofAgent.recurrence n x hx
  first
  | linear_combination hrec
  | linear_combination -hrec
  | (try simp only [hrec]) <;> ring

theorem step_2 (n : ℤ) (x : ℝ) (hx : 0 < x) :
    (((((2 : ℂ) * (n : ℂ)) / (x : ℂ)) * (BesselProofAgent.J n x)) + (BesselProofAgent.J n x)) = (((((2 : ℂ) * (n : ℂ)) / (x : ℂ)) + (1 : ℂ)) * (BesselProofAgent.J n x)) := by
  ring

theorem target : ∀ (n : ℤ) (x : ℝ), 0 < x → (((BesselProofAgent.J (n - (1 : ℤ)) x) + (BesselProofAgent.J (n + (1 : ℤ)) x)) + (BesselProofAgent.J n x)) = (((((2 : ℂ) * (n : ℂ)) / (x : ℂ)) + (1 : ℂ)) * (BesselProofAgent.J n x)) := by
  intro n x hx
  calc
    (((BesselProofAgent.J (n - (1 : ℤ)) x) + (BesselProofAgent.J (n + (1 : ℤ)) x)) + (BesselProofAgent.J n x)) = (((((2 : ℂ) * (n : ℂ)) / (x : ℂ)) * (BesselProofAgent.J n x)) + (BesselProofAgent.J n x)) := step_1 n x hx
    _ = (((((2 : ℂ) * (n : ℂ)) / (x : ℂ)) + (1 : ℂ)) * (BesselProofAgent.J n x)) := step_2 n x hx

end BesselAgentCandidate

#eval IO.println "BESSEL_AUDIT_BEGIN"
#print axioms BesselAgentCandidate.target
#eval IO.println "BESSEL_AUDIT_END"
