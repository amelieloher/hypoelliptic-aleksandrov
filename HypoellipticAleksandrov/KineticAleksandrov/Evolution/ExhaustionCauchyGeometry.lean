module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TruncationGeometry
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic.Linarith

/-!
# Open and bounded geometry of the actual straightened ellipsoid

These facts allow the scalar finite-cylinder maximum principle to be applied directly
on the truncations used by the truncated problems, without a full-domain solution premise.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set
open scoped Topology

/-- The actual straightened ellipsoid is open. -/
theorem isOpen_straightenedEllipsoid (n : ℕ) {r R : ℝ} (hr : 0 < r) (hR : 0 < R) :
    IsOpen (openEllipsoid (straightenedEllipsoidMatrix n r R)) := by
  have he : openEllipsoid (straightenedEllipsoidMatrix n r R) =
      {x | PDE.vecNormSq (spatialY x) / r ^ 2 +
        PDE.vecNormSq (spatialZ x) / R ^ 2 < 1} :=
    Set.ext fun x => (straightenedEllipsoid_characterization n r R hr hR).2 x
  rw [he]
  exact isOpen_lt
    (((PDE.continuous_vecNormSq.comp (contDiff_spatialY (m := 0)).continuous).div_const _).add
      ((PDE.continuous_vecNormSq.comp (contDiff_spatialZ (m := 0)).continuous).div_const _))
    continuous_const

/-- The actual straightened ellipsoid is bounded in the inherited topology; its geometric
characterization still uses the Euclidean block norms. -/
theorem isBounded_straightenedEllipsoid (n : ℕ) {r R : ℝ} (hr : 0 < r) (hR : 0 < R) :
    Bornology.IsBounded (openEllipsoid (straightenedEllipsoidMatrix n r R)) := by
  let H := terminalCoordinateHomeomorph (0 : PDE.Vec n)
  have hc : IsCompact (H ⁻¹'
      (Metric.closedBall (0 : PDE.Vec n) r ×ˢ Metric.closedBall (0 : PDE.Vec n) R)) :=
    H.isCompact_preimage.mpr ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  refine hc.isBounded.subset ?_
  intro x hx
  have hsum := (straightenedEllipsoid_characterization n r R hr hR).2 x |>.mp hx
  have hY : PDE.vecNormSq (spatialY x) < r ^ 2 := by
    have := div_nonneg (PDE.vecNormSq_nonneg (spatialZ x)) (sq_nonneg R)
    exact (div_lt_one (sq_pos_of_pos hr)).mp (by linarith)
  have hZ : PDE.vecNormSq (spatialZ x) < R ^ 2 := by
    have := div_nonneg (PDE.vecNormSq_nonneg (spatialY x)) (sq_nonneg r)
    exact (div_lt_one (sq_pos_of_pos hR)).mp (by linarith)
  have hball {s : ℝ} (hs : 0 < s) (y : PDE.Vec n) (hy : PDE.vecNormSq y < s ^ 2) :
      y ∈ Metric.closedBall (0 : PDE.Vec n) s := by
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hs.le]
    intro i
    rw [Real.norm_eq_abs]
    exact abs_le_of_sq_le_sq ((PDE.sq_apply_le_vecNormSq y i).trans hy.le) hs.le
  change (0 + spatialY x, spatialZ x) ∈
    Metric.closedBall (0 : PDE.Vec n) r ×ˢ Metric.closedBall (0 : PDE.Vec n) R
  simp only [zero_add, mem_prod]
  exact ⟨hball hr _ hY, hball hR _ hZ⟩

end HypoellipticAleksandrov.KineticAleksandrov
