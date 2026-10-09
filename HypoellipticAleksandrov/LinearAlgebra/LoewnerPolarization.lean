module

public import HypoellipticAleksandrov.Coefficients.Ellipticity

/-!
# Loewner polarization

This module turns two-sided Loewner bounds into the sharp polarized quadratic bound.
-/

@[expose] public section

open scoped BigOperators MatrixOrder
open Matrix

namespace HypoellipticAleksandrov

private theorem matrix_isSymm_of_loewner_lower {d : ℕ} {lam : ℝ} {A : PDE.Mat d}
    (hlower : lam • (1 : PDE.Mat d) ≤ A) : A.IsSymm := by
  have hgap : (A - lam • (1 : PDE.Mat d)).PosSemidef := Matrix.le_iff.mp hlower
  refine Matrix.IsSymm.ext ?_
  intro i j
  by_cases hij : i = j
  · subst j
    rfl
  · have hji : j ≠ i := Ne.symm hij
    have h := hgap.isHermitian.apply i j
    simpa only [star_trivial, Matrix.sub_apply, Matrix.smul_apply, one_apply, hij, hji,
      ite_false, mul_zero, smul_zero, sub_zero] using h

private theorem vecDot_mulVec_comm_of_isSymm {d : ℕ} {A : PDE.Mat d}
    (hA : A.IsSymm) (G W : PDE.Vec d) :
    PDE.vecDot G (A *ᵥ W) = PDE.vecDot W (A *ᵥ G) := by
  classical
  unfold PDE.vecDot Matrix.mulVec
  simp only [dotProduct]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hA.apply]
  ring

private theorem vecDot_mulVec_upper_of_loewner {d : ℕ} {Lam : ℝ} {A : PDE.Mat d}
    (hupper : A ≤ Lam • (1 : PDE.Mat d)) (W : PDE.Vec d) :
    PDE.vecDot W (A *ᵥ W) ≤ Lam * PDE.vecNormSq W := by
  have hneg : (-Lam) • (1 : PDE.Mat d) ≤ -A := by
    simpa only [neg_smul] using neg_le_neg hupper
  have hquad := vecDot_mulVec_lower_of_loewner hneg W
  have hrewrite : PDE.vecDot W ((-A) *ᵥ W) = -PDE.vecDot W (A *ᵥ W) := by
    simp only [neg_mulVec, PDE.vecDot, Pi.neg_apply, mul_neg,
      Finset.sum_neg_distrib]
  rw [hrewrite] at hquad
  exact neg_le_neg_iff.mp (by
    simpa only [neg_mul, neg_le_neg_iff] using hquad)

/-- Two-sided Loewner bounds control the polarized coordinate form with no
sign assumptions on either bound. -/
theorem vecDot_add_mulVec_sub_lower_of_loewner
    {d : ℕ} {lam Lam : ℝ} {A : PDE.Mat d}
    (hlower : lam • (1 : PDE.Mat d) ≤ A)
    (hupper : A ≤ Lam • (1 : PDE.Mat d))
    (G W : PDE.Vec d) :
    lam * PDE.vecNormSq G - Lam * PDE.vecNormSq W ≤
      PDE.vecDot (G + W) (A *ᵥ (G - W)) := by
  have hG := vecDot_mulVec_lower_of_loewner hlower G
  have hW := vecDot_mulVec_upper_of_loewner hupper W
  have hA := matrix_isSymm_of_loewner_lower hlower
  have hcross := vecDot_mulVec_comm_of_isSymm hA G W
  calc
    lam * PDE.vecNormSq G - Lam * PDE.vecNormSq W ≤
        PDE.vecDot G (A *ᵥ G) - PDE.vecDot W (A *ᵥ W) := sub_le_sub hG hW
    _ = PDE.vecDot (G + W) (A *ᵥ (G - W)) := by
      rw [Matrix.mulVec_sub]
      change (∑ i, G i * (A *ᵥ G) i) - ∑ i, W i * (A *ᵥ W) i =
        ∑ i, (G i + W i) * ((A *ᵥ G) i - (A *ᵥ W) i)
      change (∑ i, G i * (A *ᵥ W) i) = ∑ i, W i * (A *ᵥ G) i at hcross
      simp only [add_mul, mul_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib]
      linarith

end HypoellipticAleksandrov
