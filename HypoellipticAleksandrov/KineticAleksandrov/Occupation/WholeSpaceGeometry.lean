module

public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.WholeSpaceQuadratic
public import PDEFoundation.Geometry.EuclideanBall.Topology

/-! # Boundary inequalities for the occupation quadratic -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set

/-- On the lateral frontier the spatial quadratic is at least the squared radius. -/
theorem radius_sq_le_frontier_sum {d : ℕ} (vStar : PDE.Vec d) (R : ℝ)
    {v : PDE.Vec d} (hv : v ∈ frontier (PDE.euclideanBall vStar R)) :
    R ^ 2 ≤ ∑ i, (v i - vStar i) ^ 2 := by
  have hn : v ∉ PDE.euclideanBall vStar R :=
    (PDE.isOpen_euclideanBall vStar R).frontier_eq ▸ hv |>.2
  have hsq : ¬ PDE.euclideanSqDist v vStar < R ^ 2 := hn
  simpa [PDE.euclideanSqDist, PDE.vecNormSq_eq_sum_sq] using le_of_not_gt hsq

/-- The chosen squared radius makes the central quadratic at most one half. -/
theorem occupationQuadratic_center_half {d : ℕ} {Lam α R : ℝ}
    (hLam : 0 ≤ Lam) (hα : 0 ≤ α) (hR : 0 < R)
    (hRsq : R ^ 2 = max 1 (4 * d * Lam)) :
    (2 * d * Lam * (1 - α)) / R ^ 2 ≤ 1 / 2 := by
  apply (div_le_iff₀ (sq_pos_of_pos hR)).mpr
  have hb : 4 * (d : ℝ) * Lam ≤ R ^ 2 := hRsq ▸ le_max_right _ _
  have ha : 0 ≤ 2 * (d : ℝ) * Lam := by positivity
  nlinarith [mul_nonneg ha hα]

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
