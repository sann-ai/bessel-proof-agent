import Mathlib.Analysis.SpecialFunctions.Bessel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

/-!
# Integer-order Bessel identities

`J n x` is mathlib's first-kind Bessel function, restricted to integer orders
and real arguments, with its complex value preserved. The identities below
hold for all real arguments; a generated task may restrict to `0 < x`.
-/

namespace BesselProofAgent

/-- The first-kind Bessel function at integer order and real argument. -/
noncomputable def J (n : ℤ) (x : ℝ) : ℂ :=
  Complex.besselJ (n : ℂ) (x : ℂ)

/-- Integer-order argument parity. -/
theorem argument_neg (n : ℤ) (x : ℝ) :
    J n (-x) = (-1 : ℂ) ^ n * J n x := by
  simpa only [J, Complex.ofReal_neg] using Complex.besselJ_int_neg n (x : ℂ)

/-- Integer-order reflection. -/
theorem order_neg (n : ℤ) (x : ℝ) :
    J (-n) x = (-1 : ℂ) ^ n * J n x := by
  simpa only [J, Int.cast_neg] using Complex.besselJ_neg_int n (x : ℂ)

/-- Reflecting the order has the same effect as reflecting the argument. -/
theorem order_argument_neg (n : ℤ) (x : ℝ) : J (-n) x = J n (-x) := by
  rw [order_neg, argument_neg]

/-- Simultaneous reflection leaves the Bessel value unchanged. -/
theorem double_neg (n : ℤ) (x : ℝ) : J (-n) (-x) = J n x := by
  simpa only [neg_neg] using order_argument_neg n (-x)

/-- Integer sign factors cancel under opposite exponents. -/
theorem sign_cancel (n : ℤ) : (-1 : ℂ) ^ (-n) * (-1 : ℂ) ^ n = 1 := by
  rw [zpow_neg, inv_mul_cancel₀ (zpow_ne_zero _ (by norm_num))]

/-- Squaring an integer sign factor gives one. -/
theorem sign_mul_self (n : ℤ) : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := by
  rw [← mul_zpow]
  norm_num

/-- The order-zero instance of the three-term recurrence. -/
theorem recurrence_zero (x : ℝ) :
    J (-1) x + J 1 x = (2 * (0 : ℂ) / (x : ℂ)) * J 0 x := by
  have h := order_neg 1 x
  norm_num at h ⊢
  rw [h]
  ring

/-- A deliberately false candidate has a formal negation proof. -/
theorem add_one_ne (n : ℤ) (x : ℝ) : J n x + 1 ≠ J n x := by
  intro h
  have hz : (1 : ℂ) = 0 := add_left_cancel (show J n x + 1 = J n x + 0 by simpa only [add_zero] using h)
  exact one_ne_zero hz

/-- Refutation of the corresponding universally quantified candidate on `x > 0`. -/
theorem not_forall_add_one :
    ¬ (∀ (n : ℤ) (x : ℝ), 0 < x → J n x + 1 = J n x) := by
  intro h
  exact add_one_ne 0 1 (h 0 1 (by norm_num))

end BesselProofAgent
