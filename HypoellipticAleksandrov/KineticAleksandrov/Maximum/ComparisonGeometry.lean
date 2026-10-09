module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.InnerCylinderGeometry
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Constructions.SumProd

/-! # Closed cylinders and their face coordinates for comparison -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open Set Filter
open scoped Topology

/-- The Euclidean open ball has the expected closure on the native vector carrier. -/
theorem comparison_closure_euclideanBall_zero {d : ℕ} {R : ℝ} (hR : 0 < R) :
    closure (PDE.euclideanBall (0 : PDE.Vec d) R) = PDE.euclideanClosedBall 0 R := by
  apply Subset.antisymm
  · exact closure_minimal (PDE.euclideanBall_subset_euclideanClosedBall _ _)
      (PDE.isClosed_euclideanClosedBall _ _)
  · intro x hx
    have ht : Tendsto (fun r : ℝ => r • x) (𝓝[<] 1) (𝓝 x) := by
      have hc : Continuous (fun r : ℝ => r • x) := continuous_id.smul continuous_const
      simpa only [one_smul] using (hc.tendsto 1).mono_left nhdsWithin_le_nhds
    apply mem_closure_of_tendsto ht
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 from zero_lt_one)] with r hr
    change PDE.vecNormSq (r • x - 0) < R ^ 2
    change PDE.vecNormSq (x - 0) ≤ R ^ 2 at hx
    simp only [sub_zero, PDE.vecNormSq_smul] at hx ⊢
    have hsq : r ^ 2 < 1 := by nlinarith [hr.1,hr.2]
    calc r ^ 2 * PDE.vecNormSq x ≤ r ^ 2 * R ^ 2 :=
        mul_le_mul_of_nonneg_left hx (sq_nonneg r)
      _ < R ^ 2 := by nlinarith [sq_pos_of_pos hR]

/-- A forward cylinder is the open product box in its free-transport coordinates. -/
theorem comparison_forwardCylinder_eq_preimage {d : ℕ}
    (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R) :
    forwardCylinder Z₀ R hR = (relativeHomeomorph Z₀) ⁻¹'
      (Ioo Z₀.time (Z₀.time + R ^ 2) ×ˢ
        (PDE.euclideanBall 0 (R ^ 3) ×ˢ PDE.euclideanBall 0 R)) := by
  ext P
  simp only [mem_forwardCylinder_iff, mem_preimage, mem_prod, mem_Ioo]
  dsimp only [relativeHomeomorph]
  simp only [PDE.euclideanBall, PDE.euclideanSqDist, relativeVelocity, sub_zero]
  tauto

/-- The closed forward cylinder is the exact closed product box, including all faces. -/
theorem comparison_closure_forwardCylinder_eq {d : ℕ}
    (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R) :
    closure (forwardCylinder Z₀ R hR) =
      relativeClosedBox Z₀ Z₀.time (Z₀.time + R ^ 2) R (R ^ 3) := by
  rw [comparison_forwardCylinder_eq_preimage, ← (relativeHomeomorph Z₀).preimage_closure,
    closure_prod_eq, closure_prod_eq, closure_Ioo (by nlinarith [sq_pos_of_pos hR]),
    comparison_closure_euclideanBall_zero (pow_pos hR 3),
    comparison_closure_euclideanBall_zero hR]
  rfl

/-- Forward kinetic cylinders are open in the physical topology. -/
theorem isOpen_forwardCylinder {d : ℕ}
    (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R) :
    IsOpen (forwardCylinder Z₀ R hR) := by
  rw [comparison_forwardCylinder_eq_preimage]
  exact (isOpen_Ioo.prod ((PDE.isOpen_euclideanBall _ _).prod
    (PDE.isOpen_euclideanBall _ _))).preimage (relativeHomeomorph Z₀).continuous

end HypoellipticAleksandrov.KineticAleksandrov
