import BesselProofAgent.Recurrence
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # Bessel differentiation through its entire regularized hypergeometric factor -/

namespace BesselProofAgent

open Complex FormalMultilinearSeries

/-- Differentiating the scalar `₀F₁` series shifts its parameter by one. -/
theorem hg_coeff_derivative (a : ℂ) (k : ℕ) :
    (k + 1 : ℂ) * regularizedHGFunCoeff 0 {a} (k + 1) =
      regularizedHGFunCoeff 0 {a + 1} k := by
  rw [hg_coeff, hg_coeff, Nat.factorial_succ]
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_mul, mul_inv_rev]
  have heq : a + (k + 1) = a + 1 + k := by ring
  rw [heq]
  have hk : (k + 1 : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero k)
  calc
    _ = ((k + 1 : ℂ) * (k + 1 : ℂ)⁻¹) *
        ((k.factorial : ℂ)⁻¹ * (Gamma (a + 1 + k))⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hk, one_mul]

/-- The derivative of regularized `₀F₁` at any complex argument. -/
theorem hg_hasDerivAt (a z : ℂ) :
    HasDerivAt (regularizedHGFun 0 {a}) (regularizedHGFun 0 {a + 1} z) z := by
  let p := regularizedHGFunSeries 0 {a}
  have hr : ‖z‖ₑ < p.radius := by simp [p]
  have hr' : ‖z‖ₑ < p.derivSeries.radius := hr.trans_le p.radius_le_radius_derivSeries
  have hs := p.derivSeries.hasSum (x := z) (by simpa [Metric.mem_eball, edist_zero_right] using hr')
  have hm := (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).hasSum hs
  have ht : HasSum (fun k : ℕ => z ^ k * regularizedHGFunCoeff 0 {a + 1} k)
      ((p.derivSeries.sum z) 1) := by
    convert hm using 1
    · ext k
      simp only [ContinuousLinearMap.apply_apply, apply_eq_pow_smul_coeff,
        _root_.smul_apply, derivSeries_coeff_one, p,
        regularizedHGFunSeries_coeff, nsmul_eq_mul, smul_eq_mul, Nat.cast_add, Nat.cast_one]
      rw [hg_coeff_derivative]
    · rfl
  have heq := ht.unique (hg_hasSum (a + 1) z)
  have hd : HasDerivAt (regularizedHGFun 0 {a}) ((p.derivSeries.sum z) 1) z :=
    (p.hasFDerivAt_sum hr).hasDerivAt
  rwa [heq] at hd

/-- The first derivative at complex order, on the branch domain of complex powers. -/
theorem bessel_hasDerivAt (a z : ℂ) (hz : z ∈ Complex.slitPlane) :
    HasDerivAt (Complex.besselJ a)
      ((a / z) * Complex.besselJ a z - Complex.besselJ (a + 1) z) z := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have ht : z / 2 ∈ slitPlane := by
    rcases hz with h | h
    · left
      simpa [Complex.div_re] using (div_pos h (by norm_num : (0 : ℝ) < 2))
    · right
      simpa [Complex.div_im] using (div_ne_zero h (by norm_num : (2 : ℝ) ≠ 0))
  have hbase : HasDerivAt (fun w : ℂ => w / 2) (1 / 2) z :=
    (hasDerivAt_id z).div_const 2
  have hpow := hbase.cpow_const (c := a) ht
  have harg := (hbase.pow 2).neg
  have hh := (hg_hasDerivAt (a + 1) (-(z / 2) ^ 2)).comp z harg
  have hprod := hpow.mul hh
  change HasDerivAt (Complex.besselJ a) _ z at hprod
  dsimp only [Function.comp_apply, Pi.neg_apply, Pi.pow_apply] at hprod
  convert hprod using 1
  have ht0 : z / 2 ≠ 0 := slitPlane_ne_zero ht
  have heq : a + 1 + 1 = a + 2 := by ring
  simp only [Complex.besselJ, cpow_add _ _ ht0, cpow_sub _ _ ht0, cpow_one,
    heq, Nat.cast_ofNat]
  field_simp
  ring

/-- The symmetric adjacent-order form of the derivative. -/
theorem bessel_hasDerivAt_symmetric (a z : ℂ) (hz : z ∈ Complex.slitPlane) :
    HasDerivAt (Complex.besselJ a)
      ((Complex.besselJ (a - 1) z - Complex.besselJ (a + 1) z) / 2) z := by
  convert bessel_hasDerivAt a z hz using 1
  have hr := bessel_recurrence a z (slitPlane_ne_zero hz)
  linear_combination (1 / 2 : ℂ) * hr

#print axioms hg_hasDerivAt
#print axioms bessel_hasDerivAt
#print axioms bessel_hasDerivAt_symmetric

end BesselProofAgent
