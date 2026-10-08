import BesselProofAgent.RealCalculus
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Rational-order derivatives and the fundamental theorem on positive intervals -/

namespace BesselProofAgent

/-- The derivative formula at an exact rational order and positive real argument. -/
theorem deriv_bessel_rational (p : ℤ) (q : ℕ) (_hq : 0 < q) (x : ℝ) (hx : 0 < x) :
    deriv (fun t : ℝ => Complex.besselJ (((p : ℝ) / (q : ℝ) : ℝ) : ℂ) (t : ℂ)) x =
      ((((p : ℝ) / (q : ℝ) : ℝ) : ℂ) / (x : ℂ)) *
        Complex.besselJ (((p : ℝ) / (q : ℝ) : ℝ) : ℂ) (x : ℂ) -
      Complex.besselJ ((((p : ℝ) / (q : ℝ) : ℝ) : ℂ) + 1) (x : ℂ) :=
  deriv_bessel_real _ x hx

/-- A concrete half-integer derivative identity. -/
theorem deriv_bessel_half (x : ℝ) (hx : 0 < x) :
    deriv (fun t : ℝ => Complex.besselJ (1 / 2 : ℂ) (t : ℂ)) x =
      (1 / (2 * (x : ℂ))) * Complex.besselJ (1 / 2 : ℂ) (x : ℂ) -
        Complex.besselJ (3 / 2 : ℂ) (x : ℂ) := by
  have h := deriv_bessel_real (1 / 2 : ℂ) x hx
  simpa only [div_div, show (1 / 2 : ℂ) + 1 = 3 / 2 by norm_num] using h

/-- All points between positive endpoints remain in the positive domain. -/
private theorem positive_on_uIcc {a b t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (ht : t ∈ Set.uIcc a b) : 0 < t := by
  rcases Set.mem_uIcc.mp ht with ht | ht
  · exact ha.trans_le ht.1
  · exact hb.trans_le ht.1

/-- The ordinary derivative expression is integrable between positive endpoints. -/
theorem intervalIntegrable_bessel_derivative (a : ℂ) (l u : ℝ) (hl : 0 < l) (hu : 0 < u) :
    IntervalIntegrable (fun t : ℝ => (a / (t : ℂ)) * Complex.besselJ a (t : ℂ) -
      Complex.besselJ (a + 1) (t : ℂ)) MeasureTheory.volume l u := by
  have hJ (b : ℂ) : ContinuousOn (fun t : ℝ => Complex.besselJ b (t : ℂ)) (Set.uIcc l u) := by
    intro t ht
    exact (hasDerivAt_bessel_real b t (positive_on_uIcc hl hu ht)).continuousAt.continuousWithinAt
  have hdiv : ContinuousOn (fun t : ℝ => a / (t : ℂ)) (Set.uIcc l u) := by
    apply continuousOn_const.div Complex.continuous_ofReal.continuousOn
    intro t ht
    exact_mod_cast (ne_of_gt (positive_on_uIcc hl hu ht))
  exact ((hdiv.mul (hJ a)).sub (hJ (a + 1))).intervalIntegrable

/-- The fundamental theorem of calculus at arbitrary complex order on positive intervals. -/
theorem integral_bessel_derivative (a : ℂ) (l u : ℝ) (hl : 0 < l) (hu : 0 < u) :
    (∫ t in l..u, (a / (t : ℂ)) * Complex.besselJ a (t : ℂ) -
      Complex.besselJ (a + 1) (t : ℂ)) =
      Complex.besselJ a (u : ℂ) - Complex.besselJ a (l : ℂ) := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hasDerivAt_bessel_real a t (positive_on_uIcc hl hu ht))
    (intervalIntegrable_bessel_derivative a l u hl hu)

/-- A convenient fixed-lower-endpoint specialization for structured input. -/
theorem integral_deriv_bessel_real (a : ℂ) (x : ℝ) (hx : 0 < x) :
    (∫ t in (1 : ℝ)..x, (a / (t : ℂ)) * Complex.besselJ a (t : ℂ) -
      Complex.besselJ (a + 1) (t : ℂ)) =
      Complex.besselJ a (x : ℂ) - Complex.besselJ a 1 := by
  simpa using integral_bessel_derivative a 1 x zero_lt_one hx

/-- A weighted half-integer Bessel antiderivative on positive real arguments. -/
theorem hasDerivAt_sqrt_mul_bessel_half (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => ((Real.sqrt t) : ℂ) * Complex.besselJ (1 / 2 : ℂ) (t : ℂ))
      (((Real.sqrt x) : ℂ) * Complex.besselJ (-(1 : ℂ) / 2) (x : ℂ)) x := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hx)
  have hs0 : ((Real.sqrt x) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr hx))
  have hs2 : ((Real.sqrt x) : ℂ) ^ 2 = (x : ℂ) := by exact_mod_cast (Real.sq_sqrt hx.le)
  have hr := bessel_recurrence (1 / 2 : ℂ) (x : ℂ) hx0
  norm_num at hr
  have hp := ((Real.hasDerivAt_sqrt (ne_of_gt hx)).ofReal_comp).mul
    (hasDerivAt_bessel_real (1 / 2 : ℂ) x hx)
  change HasDerivAt (fun t : ℝ => ((Real.sqrt t) : ℂ) * Complex.besselJ (1 / 2 : ℂ) (t : ℂ)) _ x at hp
  convert hp using 1
  push_cast
  norm_num
  field_simp at hr ⊢
  ring_nf
  rw [hs2]
  simp only [neg_div]
  linear_combination (2 * (x : ℂ)) * hr

/-- A concrete noninteger-order weighted integral between positive endpoints. -/
theorem integral_sqrt_mul_bessel_neg_half (x : ℝ) (hx : 0 < x) :
    (∫ t in (1 : ℝ)..x, ((Real.sqrt t) : ℂ) * Complex.besselJ (-(1 : ℂ) / 2) (t : ℂ)) =
      ((Real.sqrt x) : ℂ) * Complex.besselJ (1 / 2 : ℂ) (x : ℂ) -
        Complex.besselJ (1 / 2 : ℂ) 1 := by
  have hJ : ContinuousOn (fun t : ℝ => Complex.besselJ (-(1 : ℂ) / 2) (t : ℂ))
      (Set.uIcc 1 x) := by
    intro t ht
    exact (hasDerivAt_bessel_real _ t (positive_on_uIcc zero_lt_one hx ht)).continuousAt.continuousWithinAt
  have hcont : ContinuousOn (fun t : ℝ => ((Real.sqrt t) : ℂ) *
      Complex.besselJ (-(1 : ℂ) / 2) (t : ℂ)) (Set.uIcc 1 x) :=
    (Complex.continuous_ofReal.comp Real.continuous_sqrt).continuousOn.mul hJ
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hasDerivAt_sqrt_mul_bessel_half t (positive_on_uIcc zero_lt_one hx ht))
    hcont.intervalIntegrable
  simpa using h

#print axioms hasDerivAt_sqrt_mul_bessel_half
#print axioms integral_sqrt_mul_bessel_neg_half
#print axioms deriv_bessel_rational
#print axioms deriv_bessel_half
#print axioms integral_deriv_bessel_real

end BesselProofAgent
