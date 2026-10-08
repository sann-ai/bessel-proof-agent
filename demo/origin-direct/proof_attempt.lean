import BesselProofAgent

namespace BesselAgentCandidate

theorem target : ∀ (n : ℤ) (x : ℝ), 0 < x → x ≤ 2 → (x : ℝ) ≠ ((1 : ℝ) / 2) → ((intervalIntegral (fun (x : ℝ) => (((Real.rpow x ((1 : ℝ) / (4 : ℝ))) : ℂ) * (Complex.besselJ (((-3 : ℝ) / (4 : ℝ) : ℝ) : ℂ) ((x) : ℂ)))) (0 : ℝ) x MeasureTheory.volume) + (((Real.rpow x ((1 : ℝ) / (4 : ℝ))) : ℂ) * (Complex.besselJ (((1 : ℝ) / (4 : ℝ) : ℝ) : ℂ) ((x) : ℂ)))) = (((2 : ℂ) * ((Real.rpow x ((1 : ℝ) / (4 : ℝ))) : ℂ)) * (Complex.besselJ (((1 : ℝ) / (4 : ℝ) : ℝ) : ℂ) ((x) : ℂ))) := by
  intro n x hx hcondition_1 hcondition_2
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hx)
  have hintegrable := BesselProofAgent.intervalIntegrable_inv_sqrt_complex x
  have hsingular := BesselProofAgent.integral_inv_sqrt x hx
  have hweighted := BesselProofAgent.integral_sqrt_mul_bessel_neg_half x hx
  have horigin_integrable := BesselProofAgent.intervalIntegrable_origin_weighted_bessel x hx
  have horigin := BesselProofAgent.integral_origin_weighted_bessel x hx
  have hderivative_0 := BesselProofAgent.deriv_bessel_rational (-3 : ℤ) (4 : ℕ) (by norm_num) x hx
  have hsymmetric_0 := BesselProofAgent.deriv_bessel_real_symmetric ((-3 : ℂ) / (4 : ℂ)) x hx
  have hintegral_0 := BesselProofAgent.integral_deriv_bessel_real ((-3 : ℂ) / (4 : ℂ)) x hx
  have hderivative_1 := BesselProofAgent.deriv_bessel_rational (1 : ℤ) (4 : ℕ) (by norm_num) x hx
  have hsymmetric_1 := BesselProofAgent.deriv_bessel_real_symmetric ((1 : ℂ) / (4 : ℂ)) x hx
  have hintegral_1 := BesselProofAgent.integral_deriv_bessel_real ((1 : ℂ) / (4 : ℂ)) x hx
  norm_num [div_div] at hsingular hweighted horigin hderivative_0 hintegral_0 hderivative_1 hintegral_1 hsymmetric_0 hsymmetric_1 ⊢
  solve
  | (try simp only [hsingular, hweighted, horigin, hderivative_0, hintegral_0, hderivative_1, hintegral_1]) <;> (solve | ring | (field_simp [hxC] <;> ring))
  | (try simp only [hsingular, hweighted, horigin, hsymmetric_0, hintegral_0, hsymmetric_1, hintegral_1]) <;> (solve | ring | (field_simp [hxC] <;> ring))

end BesselAgentCandidate

#eval IO.println "BESSEL_AUDIT_BEGIN"
#print axioms BesselAgentCandidate.target
#eval IO.println "BESSEL_AUDIT_END"
