import BesselProofAgent.NonintegerCalculus
import BesselProofAgent.SingularIntegrals

/-! # An integrable Bessel singularity at the origin

The integrand `t^(1/4) J_{-3/4}(t)` has an inverse-square-root singularity from the
right. Its primitive `t^(1/4) J_{1/4}(t)` tends to zero at the origin.
-/

namespace BesselProofAgent

open Complex Filter Set
open scoped Topology

/-- Factor a weighted Bessel function into a real power and a regularized hypergeometric factor. -/
theorem real_weighted_bessel_eq (p a x : ℝ) (hx : 0 < x) :
    ((x ^ p : ℝ) : ℂ) * besselJ (a : ℂ) (x : ℂ) =
      ((x ^ (p + a) / (2 : ℝ) ^ a : ℝ) : ℂ) *
        regularizedHGFun 0 {(a : ℂ) + 1} (-((x : ℂ) / 2) ^ 2) := by
  unfold besselJ
  have hpow : ((x : ℂ) / 2) ^ (a : ℂ) = (((x / 2) ^ a : ℝ) : ℂ) := by
    simpa using (Complex.ofReal_cpow (show 0 ≤ x / 2 by positivity) a).symm
  rw [hpow, Real.div_rpow hx.le (by norm_num), ← mul_assoc,
    ← Complex.ofReal_mul, ← mul_div_assoc, ← Real.rpow_add hx]

/-- The weighted adjacent-order derivative formula on positive real arguments. -/
theorem hasDerivAt_rpow_mul_bessel (a x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => ((t ^ a : ℝ) : ℂ) * besselJ (a : ℂ) (t : ℂ))
      (((x ^ a : ℝ) : ℂ) * besselJ ((a : ℂ) - 1) (x : ℂ)) x := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hx)
  have hr := bessel_recurrence (a : ℂ) (x : ℂ) hx0
  have hp := ((Real.hasDerivAt_rpow_const (p := a) (Or.inl (ne_of_gt hx))).ofReal_comp).mul
    (hasDerivAt_bessel_real (a : ℂ) x hx)
  convert hp using 1
  rw [Real.rpow_sub_one (ne_of_gt hx)]
  push_cast
  linear_combination ((x ^ a : ℝ) : ℂ) * hr

/-- The hypergeometric factor remains continuous across zero. -/
theorem continuous_bessel_hg_factor (a : ℂ) :
    Continuous (fun t : ℝ => regularizedHGFun 0 {a} (-((t : ℂ) / 2) ^ 2)) := by
  apply (continuous_iff_continuousAt.mpr fun z => (hg_hasDerivAt a z).continuousAt).comp
  fun_prop

/-- The singular power and continuous factor for the selected quarter-order integrand. -/
theorem origin_weighted_bessel_factor (x : ℝ) (hx : 0 < x) :
    ((x ^ (1 / 4 : ℝ) : ℝ) : ℂ) * besselJ (-3 / 4 : ℂ) (x : ℂ) =
      ((x ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) *
        ((((2 : ℝ) ^ (-3 / 4 : ℝ) : ℝ) : ℂ)⁻¹ *
          regularizedHGFun 0 {(1 / 4 : ℂ)} (-((x : ℂ) / 2) ^ 2)) := by
  have h := real_weighted_bessel_eq (1 / 4) (-3 / 4) x hx
  norm_num at h
  simpa only [ofReal_div, div_eq_mul_inv, mul_assoc, neg_mul] using h

/-- The primitive is a square root times a continuous factor. -/
theorem origin_weighted_bessel_primitive_factor (x : ℝ) (hx : 0 < x) :
    ((x ^ (1 / 4 : ℝ) : ℝ) : ℂ) * besselJ (1 / 4 : ℂ) (x : ℂ) =
      ((x ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
        ((((2 : ℝ) ^ (1 / 4 : ℝ) : ℝ) : ℂ)⁻¹ *
          regularizedHGFun 0 {(5 / 4 : ℂ)} (-((x : ℂ) / 2) ^ 2)) := by
  have h := real_weighted_bessel_eq (1 / 4) (1 / 4) x hx
  norm_num at h
  simpa only [ofReal_div, div_eq_mul_inv, mul_assoc, neg_mul] using h

/-- The selected Bessel singularity is interval integrable from the origin. -/
theorem intervalIntegrable_origin_weighted_bessel (x : ℝ) (hx : 0 < x) :
    IntervalIntegrable (fun t : ℝ => ((t ^ (1 / 4 : ℝ) : ℝ) : ℂ) *
      besselJ (-3 / 4 : ℂ) (t : ℂ)) MeasureTheory.volume 0 x := by
  have hc : Continuous (fun t : ℝ => ((((2 : ℝ) ^ (-3 / 4 : ℝ) : ℝ) : ℂ)⁻¹) *
      regularizedHGFun 0 {(1 / 4 : ℂ)} (-((t : ℂ) / 2) ^ 2)) :=
    continuous_const.mul (continuous_bessel_hg_factor (1 / 4 : ℂ))
  have hint := (intervalIntegrable_inv_sqrt_complex x).mul_continuousOn hc.continuousOn
  apply hint.congr_uIoo
  intro t ht
  rw [Set.uIoo_of_lt hx] at ht
  exact (origin_weighted_bessel_factor t ht.1).symm

/-- The primitive has right-hand limit zero, independently of its assigned value at zero. -/
theorem tendsto_origin_weighted_bessel_primitive :
    Tendsto (fun t : ℝ => ((t ^ (1 / 4 : ℝ) : ℝ) : ℂ) * besselJ (1 / 4 : ℂ) (t : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
  have hc : Continuous (fun t : ℝ => ((t ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
      ((((2 : ℝ) ^ (1 / 4 : ℝ) : ℝ) : ℂ)⁻¹ *
        regularizedHGFun 0 {(5 / 4 : ℂ)} (-((t : ℂ) / 2) ^ 2))) :=
    (Complex.continuous_ofReal.comp (Real.continuous_rpow_const (by norm_num))).mul
      (continuous_const.mul (continuous_bessel_hg_factor (5 / 4 : ℂ)))
  have ht := (hc.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  simp only [Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0), ofReal_zero, zero_mul] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (origin_weighted_bessel_primitive_factor t ht).symm

/-- The selected integrand actually diverges in norm at the origin from the right. -/
theorem tendsto_norm_origin_weighted_bessel :
    Tendsto (fun t : ℝ => ‖((t ^ (1 / 4 : ℝ) : ℝ) : ℂ) * besselJ (-3 / 4 : ℂ) (t : ℂ)‖)
      (𝓝[>] (0 : ℝ)) atTop := by
  have hc : Continuous (fun t : ℝ => ((((2 : ℝ) ^ (-3 / 4 : ℝ) : ℝ) : ℂ)⁻¹) *
      regularizedHGFun 0 {(1 / 4 : ℂ)} (-((t : ℂ) / 2) ^ 2)) :=
    continuous_const.mul (continuous_bessel_hg_factor (1 / 4 : ℂ))
  have ht := (hc.norm.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  simp only [ofReal_zero, zero_div, zero_pow (by norm_num : (2 : ℕ) ≠ 0), neg_zero,
    regularizedHGFun_zero, hg_coeff, Nat.factorial_zero, Nat.cast_one, inv_one,
    one_mul, Nat.cast_zero, add_zero] at ht
  have hpow : ((((2 : ℝ) ^ (-3 / 4 : ℝ) : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-3 / 4)))
  have hgamma : Gamma (1 / 4 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have hpos : 0 < ‖((((2 : ℝ) ^ (-3 / 4 : ℝ) : ℝ) : ℂ)⁻¹) * (Gamma (1 / 4 : ℂ))⁻¹‖ :=
    norm_pos_iff.mpr (mul_ne_zero (inv_ne_zero hpow) (inv_ne_zero hgamma))
  have h := (tendsto_rpow_neg_nhdsGT_zero (by norm_num : -(1 : ℝ) / 2 < 0)).atTop_mul_pos hpos ht
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [origin_weighted_bessel_factor t ht]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos ht _)]

/-- The totalized expression has value zero at zero; its right-hand norm limit is infinite. -/
theorem origin_weighted_bessel_zero :
    (((0 : ℝ) ^ (1 / 4 : ℝ) : ℝ) : ℂ) * besselJ (-3 / 4 : ℂ) 0 = 0 := by
  norm_num [Real.zero_rpow]

/-- An explicit integral with a singular Bessel integrand and a zero endpoint limit. -/
theorem integral_origin_weighted_bessel (x : ℝ) (hx : 0 < x) :
    (∫ t in (0 : ℝ)..x, ((t ^ (1 / 4 : ℝ) : ℝ) : ℂ) * besselJ (-3 / 4 : ℂ) (t : ℂ)) =
      ((x ^ (1 / 4 : ℝ) : ℝ) : ℂ) * besselJ (1 / 4 : ℂ) (x : ℂ) := by
  have hd (t : ℝ) (ht : 0 < t) :
      HasDerivAt (fun u : ℝ => ((u ^ (1 / 4 : ℝ) : ℝ) : ℂ) * besselJ (1 / 4 : ℂ) (u : ℂ))
        (((t ^ (1 / 4 : ℝ) : ℝ) : ℂ) * besselJ (-3 / 4 : ℂ) (t : ℂ)) t := by
    convert hasDerivAt_rpow_mul_bessel (1 / 4) t ht using 1 <;> norm_num
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hx
    (fun t ht => hd t ht.1) (intervalIntegrable_origin_weighted_bessel x hx)
    tendsto_origin_weighted_bessel_primitive
    ((hd x hx).continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio x)))
  simpa using h

#print axioms hasDerivAt_rpow_mul_bessel
#print axioms origin_weighted_bessel_zero
#print axioms intervalIntegrable_origin_weighted_bessel
#print axioms tendsto_origin_weighted_bessel_primitive
#print axioms tendsto_norm_origin_weighted_bessel
#print axioms integral_origin_weighted_bessel

end BesselProofAgent
