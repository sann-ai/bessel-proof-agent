import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Explicit integrable and nonintegrable singularities at the origin

Real powers are evaluated in `ℝ` and then embedded into `ℂ` for the CLI.
-/

namespace BesselProofAgent

/-- The inverse-square-root singularity is integrable at zero. -/
theorem intervalIntegrable_inv_sqrt (x : ℝ) :
    IntervalIntegrable (fun t : ℝ => Real.rpow t (-(1 : ℝ) / 2)) MeasureTheory.volume 0 x :=
  intervalIntegral.intervalIntegrable_rpow' (by norm_num)

/-- Integrability of the exact complex-valued expression used by the CLI. -/
theorem intervalIntegrable_inv_sqrt_complex (x : ℝ) :
    IntervalIntegrable (fun t : ℝ => ((Real.rpow t (-(1 : ℝ) / 2)) : ℂ))
      MeasureTheory.volume 0 x := by
  rw [intervalIntegrable_iff]
  exact Complex.ofRealCLM.integrable_comp (intervalIntegrable_iff.mp (intervalIntegrable_inv_sqrt x))

/-- The real-valued inverse-square-root integral. -/
theorem integral_inv_sqrt_real (x : ℝ) (_hx : 0 < x) :
    (∫ t in (0 : ℝ)..x, Real.rpow t (-(1 : ℝ) / 2)) = 2 * Real.sqrt x := by
  change (∫ t in (0 : ℝ)..x, t ^ (-(1 : ℝ) / 2)) = _
  rw [integral_rpow (Or.inl (by norm_num : -(1 : ℝ) < -(1 : ℝ) / 2))]
  norm_num [Real.sqrt_eq_rpow]
  ring

/-- The same singular integral embedded into complex values. -/
theorem integral_inv_sqrt (x : ℝ) (hx : 0 < x) :
    (∫ t in (0 : ℝ)..x, ((Real.rpow t (-(1 : ℝ) / 2)) : ℂ)) =
      ((2 * Real.sqrt x : ℝ) : ℂ) := by
  rw [intervalIntegral.integral_ofReal, integral_inv_sqrt_real x hx]

/-- The reciprocal singularity is not integrable on an interval starting at zero. -/
theorem not_intervalIntegrable_inv (x : ℝ) (hx : 0 < x) :
    ¬ IntervalIntegrable (fun t : ℝ => t⁻¹) MeasureTheory.volume 0 x := by
  simp [intervalIntegrable_inv_iff, ne_of_gt hx, eq_comm]

#print axioms intervalIntegrable_inv_sqrt
#print axioms intervalIntegrable_inv_sqrt_complex
#print axioms integral_inv_sqrt
#print axioms not_intervalIntegrable_inv

end BesselProofAgent
