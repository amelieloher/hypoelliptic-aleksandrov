module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularAnnihilation
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularAnnihilationReflectionStationary
import Mathlib.Tactic

/-! # Vanishing off the position axis at degree at least three -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- A genuine stationary homogeneous pair of degree at least three is supported on the
position axis. -/
theorem adjoint_vanishes_off_position_axis (R β : ℝ) (hR : 1 ≤ R) (hβ : 3 ≤ β)
    (μ η : Measure BellmanPuncturedPlane) (hp : IsBellmanAdjointPair 1 R β μ η) :
    μ {q | q.val.1 ≠ 0} = 0 ∧ η {q | q.val.1 ≠ 0} = 0 := by
  have hpos := bellmanAdjointPair_positive_position_zero R β hR hβ μ η hp
  have hneg := bellmanAdjointPair_positive_position_zero R β hR hβ
    (Measure.map bellmanReflection μ) (Measure.map bellmanReflection η) hp.reflect
  have hm : MeasurableSet {q : BellmanPuncturedPlane | 0 < q.val.1} := by measurability
  rw [Measure.map_apply bellmanReflection.measurable hm,
    Measure.map_apply bellmanReflection.measurable hm] at hneg
  have he : bellmanReflection ⁻¹' {q : BellmanPuncturedPlane | 0 < q.val.1} =
      {q : BellmanPuncturedPlane | q.val.1 < 0} := by
    ext q
    change (0 < -q.val.1) ↔ q.val.1 < 0
    exact neg_pos
  rw [he] at hneg
  have hunion : {q : BellmanPuncturedPlane | q.val.1 ≠ 0} =
      {q | 0 < q.val.1} ∪ {q | q.val.1 < 0} := by
    ext q
    simp only [mem_ofPred_eq, mem_union]
    exact ⟨fun h => (lt_or_gt_of_ne h).symm, fun h => h.elim LT.lt.ne' LT.lt.ne⟩
  rw [hunion]
  exact ⟨measure_union_null hpos.1 hneg.1, measure_union_null hpos.2 hneg.2⟩

end HypoellipticAleksandrov.KineticAleksandrov
