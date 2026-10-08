import BesselProofAgent

namespace BesselAgentCandidate

theorem step_1 (n : ℤ) (x : ℝ) (hx : 0 < x) (hcondition_1 : 1 < x) :
    ((deriv (fun (x : ℝ) => (Complex.besselJ (((1 : ℝ) / (2 : ℝ) : ℝ) : ℂ) ((x) : ℂ))) x) + (intervalIntegral (fun (x : ℝ) => ((Real.rpow x ((-1 : ℝ) / (2 : ℝ))) : ℂ)) (0 : ℝ) x MeasureTheory.volume)) = ((((Complex.besselJ (((-1 : ℝ) / (2 : ℝ) : ℝ) : ℂ) ((x) : ℂ)) - (Complex.besselJ (((3 : ℝ) / (2 : ℝ) : ℝ) : ℂ) ((x) : ℂ))) / (2 : ℂ)) + (intervalIntegral (fun (x : ℝ) => ((Real.rpow x ((-1 : ℝ) / (2 : ℝ))) : ℂ)) (0 : ℝ) x MeasureTheory.volume)) := by
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hx)
  have hintegrable := BesselProofAgent.intervalIntegrable_inv_sqrt_complex x
  have hsingular := BesselProofAgent.integral_inv_sqrt x hx
  have hweighted := BesselProofAgent.integral_sqrt_mul_bessel_neg_half x hx
  have hderivative_0 := BesselProofAgent.deriv_bessel_rational (-1 : ℤ) (2 : ℕ) (by norm_num) x hx
  have hsymmetric_0 := BesselProofAgent.deriv_bessel_real_symmetric ((-1 : ℂ) / (2 : ℂ)) x hx
  have hintegral_0 := BesselProofAgent.integral_deriv_bessel_real ((-1 : ℂ) / (2 : ℂ)) x hx
  have hderivative_1 := BesselProofAgent.deriv_bessel_rational (1 : ℤ) (2 : ℕ) (by norm_num) x hx
  have hsymmetric_1 := BesselProofAgent.deriv_bessel_real_symmetric ((1 : ℂ) / (2 : ℂ)) x hx
  have hintegral_1 := BesselProofAgent.integral_deriv_bessel_real ((1 : ℂ) / (2 : ℂ)) x hx
  have hderivative_2 := BesselProofAgent.deriv_bessel_rational (3 : ℤ) (2 : ℕ) (by norm_num) x hx
  have hsymmetric_2 := BesselProofAgent.deriv_bessel_real_symmetric ((3 : ℂ) / (2 : ℂ)) x hx
  have hintegral_2 := BesselProofAgent.integral_deriv_bessel_real ((3 : ℂ) / (2 : ℂ)) x hx
  norm_num [div_div] at hsingular hweighted hderivative_0 hintegral_0 hderivative_1 hintegral_1 hderivative_2 hintegral_2 hsymmetric_0 hsymmetric_1 hsymmetric_2 ⊢
  solve
  | (try simp only [hsingular, hweighted, hderivative_0, hintegral_0, hderivative_1, hintegral_1, hderivative_2, hintegral_2]) <;> (solve | ring | (field_simp [hxC] <;> ring))
  | (try simp only [hsingular, hweighted, hsymmetric_0, hintegral_0, hsymmetric_1, hintegral_1, hsymmetric_2, hintegral_2]) <;> (solve | ring | (field_simp [hxC] <;> ring))

theorem step_2 (n : ℤ) (x : ℝ) (hx : 0 < x) (hcondition_1 : 1 < x) :
    ((((Complex.besselJ (((-1 : ℝ) / (2 : ℝ) : ℝ) : ℂ) ((x) : ℂ)) - (Complex.besselJ (((3 : ℝ) / (2 : ℝ) : ℝ) : ℂ) ((x) : ℂ))) / (2 : ℂ)) + (intervalIntegral (fun (x : ℝ) => ((Real.rpow x ((-1 : ℝ) / (2 : ℝ))) : ℂ)) (0 : ℝ) x MeasureTheory.volume)) = (((((1 : ℂ) / ((2 : ℂ) * (x : ℂ))) * (Complex.besselJ (((1 : ℝ) / (2 : ℝ) : ℝ) : ℂ) ((x) : ℂ))) - (Complex.besselJ (((3 : ℝ) / (2 : ℝ) : ℝ) : ℂ) ((x) : ℂ))) + (intervalIntegral (fun (x : ℝ) => ((Real.rpow x ((-1 : ℝ) / (2 : ℝ))) : ℂ)) (0 : ℝ) x MeasureTheory.volume)) := by
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hx)
  solve
  | have hrec := BesselProofAgent.bessel_recurrence ((-1 : ℂ) / (2 : ℂ)) (x : ℂ) hxC
    norm_num at hrec ⊢
    solve
    | linear_combination hrec
    | linear_combination -hrec
    | linear_combination (1 / 2 : ℂ) * hrec
    | linear_combination -(1 / 2 : ℂ) * hrec
    | (try simp only [hrec]) <;> ring
  | have hrec := BesselProofAgent.bessel_recurrence ((1 : ℂ) / (2 : ℂ)) (x : ℂ) hxC
    norm_num at hrec ⊢
    solve
    | linear_combination hrec
    | linear_combination -hrec
    | linear_combination (1 / 2 : ℂ) * hrec
    | linear_combination -(1 / 2 : ℂ) * hrec
    | (try simp only [hrec]) <;> ring
  | have hrec := BesselProofAgent.bessel_recurrence ((3 : ℂ) / (2 : ℂ)) (x : ℂ) hxC
    norm_num at hrec ⊢
    solve
    | linear_combination hrec
    | linear_combination -hrec
    | linear_combination (1 / 2 : ℂ) * hrec
    | linear_combination -(1 / 2 : ℂ) * hrec
    | (try simp only [hrec]) <;> ring

theorem step_3 (n : ℤ) (x : ℝ) (hx : 0 < x) (hcondition_1 : 1 < x) :
    (((((1 : ℂ) / ((2 : ℂ) * (x : ℂ))) * (Complex.besselJ (((1 : ℝ) / (2 : ℝ) : ℝ) : ℂ) ((x) : ℂ))) - (Complex.besselJ (((3 : ℝ) / (2 : ℝ) : ℝ) : ℂ) ((x) : ℂ))) + (intervalIntegral (fun (x : ℝ) => ((Real.rpow x ((-1 : ℝ) / (2 : ℝ))) : ℂ)) (0 : ℝ) x MeasureTheory.volume)) = (((((1 : ℂ) / ((2 : ℂ) * (x : ℂ))) * (Complex.besselJ (((1 : ℝ) / (2 : ℝ) : ℝ) : ℂ) ((x) : ℂ))) - (Complex.besselJ (((3 : ℝ) / (2 : ℝ) : ℝ) : ℂ) ((x) : ℂ))) + ((2 : ℂ) * ((Real.sqrt x) : ℂ))) := by
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hx)
  have hintegrable := BesselProofAgent.intervalIntegrable_inv_sqrt_complex x
  have hsingular := BesselProofAgent.integral_inv_sqrt x hx
  have hweighted := BesselProofAgent.integral_sqrt_mul_bessel_neg_half x hx
  have hderivative_0 := BesselProofAgent.deriv_bessel_rational (1 : ℤ) (2 : ℕ) (by norm_num) x hx
  have hsymmetric_0 := BesselProofAgent.deriv_bessel_real_symmetric ((1 : ℂ) / (2 : ℂ)) x hx
  have hintegral_0 := BesselProofAgent.integral_deriv_bessel_real ((1 : ℂ) / (2 : ℂ)) x hx
  have hderivative_1 := BesselProofAgent.deriv_bessel_rational (3 : ℤ) (2 : ℕ) (by norm_num) x hx
  have hsymmetric_1 := BesselProofAgent.deriv_bessel_real_symmetric ((3 : ℂ) / (2 : ℂ)) x hx
  have hintegral_1 := BesselProofAgent.integral_deriv_bessel_real ((3 : ℂ) / (2 : ℂ)) x hx
  norm_num [div_div] at hsingular hweighted hderivative_0 hintegral_0 hderivative_1 hintegral_1 hsymmetric_0 hsymmetric_1 ⊢
  solve
  | (try simp only [hsingular, hweighted, hderivative_0, hintegral_0, hderivative_1, hintegral_1]) <;> (solve | ring | (field_simp [hxC] <;> ring))
  | (try simp only [hsingular, hweighted, hsymmetric_0, hintegral_0, hsymmetric_1, hintegral_1]) <;> (solve | ring | (field_simp [hxC] <;> ring))

theorem target : ∀ (n : ℤ) (x : ℝ), 0 < x → 1 < x → ((deriv (fun (x : ℝ) => (Complex.besselJ (((1 : ℝ) / (2 : ℝ) : ℝ) : ℂ) ((x) : ℂ))) x) + (intervalIntegral (fun (x : ℝ) => ((Real.rpow x ((-1 : ℝ) / (2 : ℝ))) : ℂ)) (0 : ℝ) x MeasureTheory.volume)) = (((((1 : ℂ) / ((2 : ℂ) * (x : ℂ))) * (Complex.besselJ (((1 : ℝ) / (2 : ℝ) : ℝ) : ℂ) ((x) : ℂ))) - (Complex.besselJ (((3 : ℝ) / (2 : ℝ) : ℝ) : ℂ) ((x) : ℂ))) + ((2 : ℂ) * ((Real.sqrt x) : ℂ))) := by
  intro n x hx hcondition_1
  calc
    ((deriv (fun (x : ℝ) => (Complex.besselJ (((1 : ℝ) / (2 : ℝ) : ℝ) : ℂ) ((x) : ℂ))) x) + (intervalIntegral (fun (x : ℝ) => ((Real.rpow x ((-1 : ℝ) / (2 : ℝ))) : ℂ)) (0 : ℝ) x MeasureTheory.volume)) = ((((Complex.besselJ (((-1 : ℝ) / (2 : ℝ) : ℝ) : ℂ) ((x) : ℂ)) - (Complex.besselJ (((3 : ℝ) / (2 : ℝ) : ℝ) : ℂ) ((x) : ℂ))) / (2 : ℂ)) + (intervalIntegral (fun (x : ℝ) => ((Real.rpow x ((-1 : ℝ) / (2 : ℝ))) : ℂ)) (0 : ℝ) x MeasureTheory.volume)) := step_1 n x hx hcondition_1
    _ = (((((1 : ℂ) / ((2 : ℂ) * (x : ℂ))) * (Complex.besselJ (((1 : ℝ) / (2 : ℝ) : ℝ) : ℂ) ((x) : ℂ))) - (Complex.besselJ (((3 : ℝ) / (2 : ℝ) : ℝ) : ℂ) ((x) : ℂ))) + (intervalIntegral (fun (x : ℝ) => ((Real.rpow x ((-1 : ℝ) / (2 : ℝ))) : ℂ)) (0 : ℝ) x MeasureTheory.volume)) := step_2 n x hx hcondition_1
    _ = (((((1 : ℂ) / ((2 : ℂ) * (x : ℂ))) * (Complex.besselJ (((1 : ℝ) / (2 : ℝ) : ℝ) : ℂ) ((x) : ℂ))) - (Complex.besselJ (((3 : ℝ) / (2 : ℝ) : ℝ) : ℂ) ((x) : ℂ))) + ((2 : ℂ) * ((Real.sqrt x) : ℂ))) := step_3 n x hx hcondition_1

end BesselAgentCandidate

#eval IO.println "BESSEL_AUDIT_BEGIN"
#print axioms BesselAgentCandidate.target
#eval IO.println "BESSEL_AUDIT_END"
