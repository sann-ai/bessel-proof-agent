import BesselProofAgent.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace BesselProofAgent

noncomputable def DJ (n : ℤ) (x : ℝ) : ℂ := deriv (J n) x
noncomputable def IJ (n : ℤ) (a b : ℝ) : ℂ := ∫ t in a..b, J n t

theorem derivative_order_neg (n : ℤ) (x : ℝ) :
    DJ (-n) x = (-1 : ℂ) ^ n * DJ n x := by
  have hf : J (-n) = fun x => (-1 : ℂ) ^ n * J n x := funext (order_neg n)
  simp only [DJ, hf, deriv_const_mul_field]

theorem integral_order_neg (n : ℤ) (a b : ℝ) :
    IJ (-n) a b = (-1 : ℂ) ^ n * IJ n a b := by
  simp only [IJ, order_neg, intervalIntegral.integral_const_mul]

theorem analytic_J (n : ℤ) (x : ℝ) : AnalyticAt ℝ (J n) x := by
  exact ((Complex.analyticAt_besselJ_int n (x : ℂ)).restrictScalars (𝕜 := ℝ)).comp
    (Complex.ofRealCLM.analyticAt x)

theorem differentiable_J (n : ℤ) : Differentiable ℝ (J n) :=
  fun x => (analytic_J n x).differentiableAt

theorem continuous_DJ (n : ℤ) : Continuous (DJ n) := by
  exact continuous_iff_continuousAt.mpr (fun x => (analytic_J n x).deriv.continuousAt)

theorem integral_DJ (n : ℤ) (a b : ℝ) :
    (∫ t in a..b, DJ n t) = J n b - J n a := by
  exact intervalIntegral.integral_deriv_eq_sub (fun x _ => differentiable_J n x)
    ((continuous_DJ n).intervalIntegrable a b)

theorem deriv_order_neg (n : ℤ) (x : ℝ) :
    deriv (fun t : ℝ => J (-n) t) x =
      (-1 : ℂ) ^ n * deriv (fun t : ℝ => J n t) x := derivative_order_neg n x

theorem integral_order_neg_raw (n : ℤ) (a b : ℝ) :
    (∫ t in a..b, J (-n) t) = (-1 : ℂ) ^ n * (∫ t in a..b, J n t) :=
  integral_order_neg n a b

theorem integral_deriv_J (n : ℤ) (a b : ℝ) :
    (∫ t in a..b, deriv (fun y : ℝ => J n y) t) = J n b - J n a := integral_DJ n a b

#print axioms derivative_order_neg
#print axioms integral_order_neg
#print axioms integral_deriv_J

end BesselProofAgent
