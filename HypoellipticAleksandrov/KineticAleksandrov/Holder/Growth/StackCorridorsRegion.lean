module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.StackCorridorsGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.NullFacesBoundary
import Mathlib.Tactic

/-! # Topology and reference closures of the fixed stack comparison box -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth
open Set

/-- The uniform path constant exceeds the source's required minimum. -/
theorem stackPathBound_large (m : ℕ) : (m : ℝ)+3 ≤ stackPathBound m := by
  dsimp [stackPathBound]
  have := Nat.cast_nonneg (α := ℝ) m
  linarith

/-- The fixed comparison region is open. -/
theorem isOpen_stackComparisonRegion (d m : ℕ) : IsOpen (stackComparisonRegion d m) :=
  (isOpen_lt continuous_const continuous_time).inter
    ((isOpen_lt continuous_time continuous_const).inter
      ((isOpen_lt (PDE.continuous_vecEuclideanNorm.comp continuous_position)
        continuous_const).inter
        (isOpen_lt (PDE.continuous_vecEuclideanNorm.comp continuous_velocity)
          continuous_const)))

/-- A compact rectangular envelope bounds the comparison region. -/
theorem isBounded_stackComparisonRegion (d m : ℕ) :
    Bornology.IsBounded (stackComparisonRegion d m) := by
  let E : Set (KineticPoint d) := (KineticPoint.equivProd d) ⁻¹'
    (Icc (-2 : ℝ) ((m : ℝ)+1) ×ˢ
      (PDE.euclideanClosedBall (0 : PDE.Vec d) (stackPathBound m+1) ×ˢ
        PDE.euclideanClosedBall (0 : PDE.Vec d) (stackPathBound m+1)))
  have hL : 0 ≤ stackPathBound m+1 := by dsimp [stackPathBound]; positivity
  have hc : IsCompact E := (KineticPoint.homeomorphProd d).isCompact_preimage.mpr
    (isCompact_Icc.prod ((PDE.isCompact_euclideanClosedBall _ hL).prod
      (PDE.isCompact_euclideanClosedBall _ hL)))
  apply hc.isBounded.subset
  intro P hP
  refine ⟨⟨hP.1.le, hP.2.1.le⟩, ?_, ?_⟩
  · apply (PDE.mem_euclideanClosedBall_iff_vecEuclideanNorm_le hL).mpr
    change PDE.vecEuclideanNorm (P.position-0) ≤ stackPathBound m+1
    simpa only [sub_zero] using hP.2.2.1.le
  · apply (PDE.mem_euclideanClosedBall_iff_vecEuclideanNorm_le hL).mpr
    change PDE.vecEuclideanNorm (P.velocity-0) ≤ stackPathBound m+1
    simpa only [sub_zero] using hP.2.2.2.le

/-- The unit backward-cylinder closure is strictly inside the comparison region. -/
theorem closure_unitCylinder_subset_comparison (d m : ℕ) :
    closure (backwardCylinder (⟨0,0,0⟩ : KineticPoint d) 1) ⊆
      stackComparisonRegion d m := by
  intro P hP
  have hb := Covering.closure_cylinder_bounds (⟨0,0,0⟩ : KineticPoint d) 1 hP
  simp only [relativePosition, sub_zero, smul_zero, one_pow, zero_sub] at hb
  have hx := PDE.vecEuclideanNorm_sq P.position
  have hv := PDE.vecEuclideanNorm_sq P.velocity
  have hxn := PDE.vecEuclideanNorm_nonneg P.position
  have hvn := PDE.vecEuclideanNorm_nonneg P.velocity
  have hL := stackPathBound_large m
  have hm := Nat.cast_nonneg (α := ℝ) m
  refine ⟨by linarith [hb.1], by linarith [hb.2.1], ?_, ?_⟩ <;>
    nlinarith [hb.2.2.1, hb.2.2.2]

/-- Weak endpoint inequalities hold throughout the unit-stack closure. -/
theorem closure_unitStack_bounds (d m : ℕ) :
    closure (forwardStack (⟨0,0,0⟩ : KineticPoint d) 1 m) ⊆
      {P | 0 ≤ P.time ∧ P.time ≤ (m : ℝ) ∧
        PDE.vecEuclideanNorm P.position ≤ (m : ℝ)+2 ∧
        PDE.vecEuclideanNorm P.velocity ≤ 1} := by
  apply closure_minimal
  · intro P hP
    change 0 < P.time-0 ∧ P.time-0 ≤ (m : ℝ)*1^2 ∧
      P.velocity ∈ PDE.euclideanBall 0 1 ∧
      relativePosition (⟨0,0,0⟩ : KineticPoint d) P ∈
        PDE.euclideanBall 0 (((m+2 : ℕ) : ℝ)*1^3) at hP
    simp only [sub_zero, one_pow, mul_one] at hP
    have hx := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt
      (by positivity : 0 < ((m+2 : ℕ) : ℝ))).mp
      hP.2.2.2
    have hv := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt one_pos).mp hP.2.2.1
    simp only [relativePosition, sub_zero, smul_zero] at hx hv
    push_cast at hx
    exact ⟨hP.1.le, hP.2.1, hx.le, hv.le⟩
  · exact (isClosed_le continuous_const continuous_time).inter
      ((isClosed_le continuous_time continuous_const).inter
        ((isClosed_le (PDE.continuous_vecEuclideanNorm.comp continuous_position)
          continuous_const).inter
          (isClosed_le (PDE.continuous_vecEuclideanNorm.comp continuous_velocity)
            continuous_const)))

/-- The unit forward-stack closure is strictly inside the same comparison region. -/
theorem closure_unitStack_subset_comparison (d m : ℕ) :
    closure (forwardStack (⟨0,0,0⟩ : KineticPoint d) 1 m) ⊆
      stackComparisonRegion d m := by
  intro P hP
  have hb := closure_unitStack_bounds d m hP
  have hL := stackPathBound_large m
  have hm := Nat.cast_nonneg (α := ℝ) m
  exact ⟨by linarith [hb.1], by linarith [hb.2.1],
    by linarith [hb.2.2.1], by linarith [hb.2.2.2]⟩

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth
