import BesselProofAgent
import Mathlib.Tactic

/-
This file checks algebraic consequences of explicitly assumed identities.
It does not define Bessel Y or prove the Bessel/ODE hypotheses.

For a positive real root z of X_01(z, lambda*z) = 0, interpret:
  A = X_00(z, lambda*z), B = X_11(z, lambda*z),
  C = X_02(z, lambda*z), Q = X_01(z,z).
The Bessel recurrence, Wronskian/cross-product formula, and an energy integral
supply hrec, hcross, hQ, and hpos analytically; these are premises here.
-/
namespace BesselAgentCandidate

/-- The cross-product identity is polynomial algebra in eight function values. -/
theorem cross_product_identity (a b c d e f g h : ℝ) :
    (a*f-b*e)*(c*h-d*g) - (a*h-b*g)*(c*f-d*e) =
      (a*d-b*c)*(e*h-f*g) := by
  ring

/-- At a root of the off-diagonal cross product, the determinant simplifies. -/
theorem cross_product_at_root (a b c d e f g h : ℝ)
    (hroot : a*h-b*g = 0) :
    (a*f-b*e)*(c*h-d*g) = (a*d-b*c)*(e*h-f*g) := by
  have hdet := cross_product_identity a b c d e f g h
  simpa [hroot] using hdet

/-- Conditional algebraic certificate for the photographed fraction. -/
theorem target (lam A B C Q : ℝ)
    (hlam : 0 < lam) (hQ : Q ≠ 0)
    (hrec : C = -A) (hcross : lam*A*B = Q^2)
    (hpos : 0 < Q^2-lam^2*A^2) :
    A^2/(Q^2+lam^2*A*C) = (1/lam)*A/(B-lam*A) := by
  have hlam0 : lam ≠ 0 := ne_of_gt hlam
  have hA : A ≠ 0 := by
    intro hz
    rw [hz] at hcross
    nlinarith [sq_pos_of_ne_zero hQ]
  have hfactor : Q^2+lam^2*A*C = lam*A*(B-lam*A) := by
    rw [hrec, ← hcross]
    ring
  have henergy : Q^2-lam^2*A^2 = lam*A*(B-lam*A) := by
    rw [← hcross]
    ring
  have hden : B-lam*A ≠ 0 := by
    intro hz
    rw [henergy, hz] at hpos
    norm_num at hpos
  rw [hfactor]
  field_simp [hlam0, hA, hden]

end BesselAgentCandidate

#eval IO.println "BESSEL_AUDIT_BEGIN"
#print axioms BesselAgentCandidate.target
#eval IO.println "BESSEL_AUDIT_END"
