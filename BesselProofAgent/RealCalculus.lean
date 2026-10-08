import BesselProofAgent.Calculus
import BesselProofAgent.Derivative

/-! # Real-argument derivative formulas and a definite Bessel integral -/

namespace BesselProofAgent

/-- Restriction of the complex-order derivative formula to positive real arguments. -/
theorem hasDerivAt_bessel_real (a : ℂ) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => Complex.besselJ a (t : ℂ))
      ((a / (x : ℂ)) * Complex.besselJ a (x : ℂ) -
        Complex.besselJ (a + 1) (x : ℂ)) x :=
  (bessel_hasDerivAt a (x : ℂ) (Complex.ofReal_mem_slitPlane.mpr hx)).comp_ofReal

theorem deriv_bessel_real (a : ℂ) (x : ℝ) (hx : 0 < x) :
    deriv (fun t : ℝ => Complex.besselJ a (t : ℂ)) x =
      (a / (x : ℂ)) * Complex.besselJ a (x : ℂ) -
        Complex.besselJ (a + 1) (x : ℂ) :=
  (hasDerivAt_bessel_real a x hx).deriv

/-- The usual adjacent-order derivative formula for `J`. -/
theorem hasDerivAt_J (n : ℤ) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (J n) (((n : ℂ) / (x : ℂ)) * J n x - J (n + 1) x) x := by
  unfold J
  simpa only [Int.cast_add, Int.cast_one] using hasDerivAt_bessel_real (n : ℂ) x hx

theorem deriv_J (n : ℤ) (x : ℝ) (hx : 0 < x) :
    deriv (J n) x = ((n : ℂ) / (x : ℂ)) * J n x - J (n + 1) x :=
  (hasDerivAt_J n x hx).deriv

/-- The symmetric adjacent-order derivative formula for `J`. -/
theorem deriv_J_symmetric (n : ℤ) (x : ℝ) (hx : 0 < x) :
    deriv (J n) x = (J (n - 1) x - J (n + 1) x) / 2 := by
  have h := (bessel_hasDerivAt_symmetric (n : ℂ) (x : ℂ)
    (Complex.ofReal_mem_slitPlane.mpr hx)).comp_ofReal.deriv
  unfold J
  simpa only [Int.cast_sub, Int.cast_add, Int.cast_one] using h

/-- An antiderivative of `x J₀(x)` on the positive half-line. -/
theorem hasDerivAt_mul_J_one (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => (t : ℂ) * J 1 t) ((x : ℂ) * J 0 x) x := by
  have h := Complex.ofRealCLM.hasDerivAt.mul (hasDerivAt_J 1 x hx)
  convert h using 1
  · ext t
    rfl
  · have hr := recurrence 1 x hx
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hx)
    norm_num at hr ⊢
    field_simp at hr ⊢
    linear_combination hr

/-- The integral from zero, with the endpoint handled by continuity of the primitive. -/
theorem integral_mul_J_zero (x : ℝ) (hx : 0 < x) :
    (∫ t in (0 : ℝ)..x, (t : ℂ) * J 0 t) = (x : ℂ) * J 1 x := by
  have hcont : Continuous (fun t : ℝ => (t : ℂ) * J 1 t) :=
    Complex.continuous_ofReal.mul (differentiable_J 1).continuous
  have hint : IntervalIntegrable (fun t : ℝ => (t : ℂ) * J 0 t)
      MeasureTheory.volume 0 x :=
    (Complex.continuous_ofReal.mul (differentiable_J 0).continuous).intervalIntegrable 0 x
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.le hcont.continuousOn
    (fun t ht => hasDerivAt_mul_J_one t ht.1) hint
  simpa using h

#print axioms deriv_J
#print axioms deriv_J_symmetric
#print axioms integral_mul_J_zero

end BesselProofAgent
