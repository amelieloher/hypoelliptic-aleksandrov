module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularTailRadial
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDisintegration
import Mathlib.Tactic

/-! # A compact rectangle meeting the position axis but avoiding the origin -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- The source rectangle combines both velocity signs while avoiding zero velocity. -/
def bellmanAngularTailRectangle : Set BellmanPuncturedPlane :=
  {q | 0 ≤ q.val.1 ∧ q.val.1 ≤ 1 ∧ 1 ≤ |q.val.2| ∧ |q.val.2| ≤ 2}

/-- The velocity annulus on the real line is compact. -/
theorem bellman_velocity_annulus_compact : IsCompact {v : ℝ | 1 ≤ |v| ∧ |v| ≤ 2} := by
  apply isCompact_Icc.of_isClosed_subset
    ((isClosed_le continuous_const continuous_abs).inter
      (isClosed_le continuous_abs continuous_const))
  intro v hv
  exact abs_le.mp hv.2

/-- The rectangle stays compact on the punctured plane because its velocities avoid zero. -/
theorem bellmanAngularTailRectangle_isCompact : IsCompact bellmanAngularTailRectangle := by
  have hK : IsCompact (Icc (0 : ℝ) 1 ×ˢ {v : ℝ | 1 ≤ |v| ∧ |v| ≤ 2}) :=
    isCompact_Icc.prod bellman_velocity_annulus_compact
  have he : bellmanAngularTailRectangle =
      (Subtype.val : BellmanPuncturedPlane → ℝ × ℝ) ⁻¹'
        (Icc (0 : ℝ) 1 ×ˢ {v : ℝ | 1 ≤ |v| ∧ |v| ≤ 2}) := by
    ext q
    simp only [bellmanAngularTailRectangle, mem_ofPred_eq, mem_preimage,
      mem_prod, mem_Icc, and_assoc]
  rw [he]
  apply Topology.IsInducing.subtypeVal.isCompact_preimage' hK
  intro q hq
  refine ⟨⟨q, ?_⟩, rfl⟩
  intro hz
  have hv := hq.2.1
  rw [hz] at hv
  norm_num at hv

/-- In radial coordinates the source rectangle contains the full velocity strips at large
angle. -/
theorem bellmanAngularTail_strip_subset :
    {w : BellmanPositiveTime × ℝ | 2 < |w.2| ∧
      1 ≤ |w.1.val * w.2| ∧ |w.1.val * w.2| ≤ 2} ⊆
      bellmanAngularPoint ⁻¹' bellmanAngularTailRectangle := by
  intro w hw
  change 2 < |w.2| ∧ 1 ≤ |w.1.val * w.2| ∧ |w.1.val * w.2| ≤ 2 at hw
  change 0 ≤ w.1.val ^ 3 ∧ w.1.val ^ 3 ≤ 1 ∧
    1 ≤ |w.1.val * w.2| ∧ |w.1.val * w.2| ≤ 2
  have hs : w.1.val ≤ 1 := by
    have hv := hw.2.2
    rw [abs_mul, abs_of_pos w.1.property] at hv
    nlinarith [w.1.property, hw.1]
  exact ⟨pow_nonneg w.1.property.le 3,
    (pow_le_pow_left₀ w.1.property.le hs 3).trans_eq (one_pow 3), hw.2.1, hw.2.2⟩

/-- Local finiteness on the original plane bounds both angular velocity strips. -/
theorem bellmanAngularTail_strip_finite (β : ℝ) (μ : Measure BellmanPuncturedPlane)
    [IsFiniteMeasureOnCompacts μ] (F : Measure ℝ) [IsFiniteMeasureOnCompacts F]
    (hrep : μ.restrict {q | 0 < q.val.1} = bellmanAngularRep β F) :
    (bellmanRadialWeight β).prod F
      {w : BellmanPositiveTime × ℝ | 2 < |w.2| ∧
        1 ≤ |w.1.val * w.2| ∧ |w.1.val * w.2| ≤ 2} < ⊤ := by
  have hm := bellmanAngularTailRectangle_isCompact.measurableSet
  have he : (bellmanRadialWeight β).prod F
      (bellmanAngularPoint ⁻¹' bellmanAngularTailRectangle) =
      μ.restrict {q | 0 < q.val.1} bellmanAngularTailRectangle := by
    rw [hrep, bellmanAngularRep, Measure.map_apply continuous_bellmanAngularPoint.measurable hm]
  calc
    _ ≤ (bellmanRadialWeight β).prod F
        (bellmanAngularPoint ⁻¹' bellmanAngularTailRectangle) :=
      measure_mono bellmanAngularTail_strip_subset
    _ = _ := he
    _ ≤ μ bellmanAngularTailRectangle := Measure.restrict_le_self _
    _ < ⊤ := bellmanAngularTailRectangle_isCompact.measure_lt_top

end HypoellipticAleksandrov.KineticAleksandrov
