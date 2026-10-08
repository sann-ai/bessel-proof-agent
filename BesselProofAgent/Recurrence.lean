import BesselProofAgent.Basic
import Mathlib.Tactic.FieldSimp

/-! # The three-term Bessel recurrence from the regularized hypergeometric series -/

namespace BesselProofAgent

open Complex

/-- The reciprocal Gamma functional equation also holds at zero. -/
theorem gamma_inv_step (a : ℂ) : (Gamma a)⁻¹ = a * (Gamma (a + 1))⁻¹ := by
  by_cases ha : a = 0
  · simp [ha, Gamma_zero]
  · rw [Gamma_add_one a ha, mul_inv_rev, ← mul_assoc, mul_comm a, mul_assoc,
      mul_inv_cancel₀ ha, mul_one]

/-- An explicit scalar coefficient of the regularized `₀F₁` series. -/
theorem hg_coeff (a : ℂ) (k : ℕ) :
    regularizedHGFunCoeff 0 {a} k = (k.factorial : ℂ)⁻¹ * (Gamma (a + k))⁻¹ := by
  simp [regularizedHGFunCoeff, mul_inv_rev, mul_comm]

theorem hg_coeff_zero (a : ℂ) :
    regularizedHGFunCoeff 0 {a} 0 = a * regularizedHGFunCoeff 0 {a + 1} 0 := by
  simpa [hg_coeff] using gamma_inv_step a

theorem hg_coeff_succ (a : ℂ) (k : ℕ) :
    regularizedHGFunCoeff 0 {a} (k + 1) =
      a * regularizedHGFunCoeff 0 {a + 1} (k + 1) + regularizedHGFunCoeff 0 {a + 2} k := by
  simp only [hg_coeff, Nat.cast_add, Nat.cast_one]
  rw [gamma_inv_step (a + (k + 1))]
  have hp : a + (k + 1) + 1 = a + 1 + (k + 1) := by ring
  have hq : a + 2 + k = a + 1 + (k + 1) := by ring
  rw [hp, hq]
  have hk : (k + 1 : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero k)
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_inv_rev]
  calc
    _ = (k.factorial : ℂ)⁻¹ * (k + 1 : ℂ)⁻¹ * a * (Gamma (a + 1 + (k + 1)))⁻¹ +
        (k.factorial : ℂ)⁻¹ * ((k + 1 : ℂ)⁻¹ * (k + 1)) *
          (Gamma (a + 1 + (k + 1)))⁻¹ := by ring
    _ = _ := by rw [inv_mul_cancel₀ hk]; ring

/-- The everywhere-convergent scalar series for regularized `₀F₁`. -/
theorem hg_hasSum (a z : ℂ) :
    HasSum (fun k : ℕ => z ^ k * regularizedHGFunCoeff 0 {a} k)
      (regularizedHGFun 0 {a} z) := by
  have h := (regularizedHGFunSeries 0 {a}).summable (x := z) (by simp)
  simpa [regularizedHGFun, FormalMultilinearSeries.sum] using h.hasSum

/-- A contiguous-parameter relation for regularized `₀F₁`, including Gamma poles. -/
theorem hg_contiguous (a z : ℂ) :
    regularizedHGFun 0 {a} z =
      a * regularizedHGFun 0 {a + 1} z + z * regularizedHGFun 0 {a + 2} z := by
  have h := (hg_hasSum a z).sub ((hg_hasSum (a + 1) z).mul_left a)
  have hs := (hasSum_nat_add_iff' 1).mpr h
  have hzero : z ^ 0 * regularizedHGFunCoeff 0 {a} 0 -
      a * (z ^ 0 * regularizedHGFunCoeff 0 {a + 1} 0) = 0 := by
    rw [hg_coeff_zero a]
    ring
  simp only [Finset.sum_range_one, hzero, sub_zero] at hs
  have ht : HasSum (fun k : ℕ => z * (z ^ k * regularizedHGFunCoeff 0 {a + 2} k))
      (regularizedHGFun 0 {a} z - a * regularizedHGFun 0 {a + 1} z) := by
    convert hs using 1
    ext k
    rw [hg_coeff_succ a k]
    ring
  have heq := ht.unique ((hg_hasSum (a + 2) z).mul_left z)
  linear_combination heq

/-- The three-term recurrence at any complex order and nonzero complex argument. -/
theorem bessel_recurrence (a z : ℂ) (hz : z ≠ 0) :
    Complex.besselJ (a - 1) z + Complex.besselJ (a + 1) z =
      (2 * a / z) * Complex.besselJ a z := by
  have ht : z / 2 ≠ 0 := div_ne_zero hz (by norm_num)
  have ha : a - 1 + 1 = a := by ring
  have hb : a + 1 + 1 = a + 2 := by ring
  unfold Complex.besselJ
  rw [ha, hb, cpow_sub _ _ ht, cpow_add _ _ ht, cpow_one]
  rw [hg_contiguous a (-(z / 2) ^ 2)]
  field_simp
  ring

/-- The integer-order recurrence on the CLI's positive-real domain. -/
theorem recurrence (n : ℤ) (x : ℝ) (hx : 0 < x) :
    J (n - 1) x + J (n + 1) x = (2 * (n : ℂ) / (x : ℂ)) * J n x := by
  have hz : (x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hx)
  simpa only [J, Int.cast_sub, Int.cast_add, Int.cast_one] using
    bessel_recurrence (n : ℂ) (x : ℂ) hz

#print axioms bessel_recurrence
#print axioms recurrence

end BesselProofAgent
