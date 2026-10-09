module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularTailRectangle
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic

/-! # Tonelli evaluation of the angular tail weight -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Measure Set

/-- The radial reference strip has positive mass for every density degree. -/
theorem bellmanRadialWeight_reference_ne_zero (β : ℝ) :
    bellmanRadialWeight β {s : BellmanPositiveTime | 1 ≤ s.val ∧ s.val ≤ 2} ≠ 0 := by
  have ho : IsOpen {s : BellmanPositiveTime | 1 < s.val ∧ s.val < 2} := by
    exact (isOpen_lt continuous_const continuous_subtype_val).inter
      (isOpen_lt continuous_subtype_val continuous_const)
  have hn : ({s : BellmanPositiveTime | 1 < s.val ∧ s.val < 2} : Set _).Nonempty := by
    refine ⟨⟨3 / 2, by norm_num⟩, ?_⟩
    norm_num
  have hm := ho.measure_pos (bellmanRadialWeight β) hn
  apply ne_of_gt
  exact hm.trans_le (measure_mono (fun s hs => ⟨hs.1.le, hs.2.le⟩))

/-- Integrating the two-sided velocity strips gives the literal angular tail factor. -/
theorem bellmanAngularTail_strip_mass (β : ℝ) (F : Measure ℝ)
    [IsFiniteMeasureOnCompacts F] :
    (bellmanRadialWeight β).prod F
      {w : BellmanPositiveTime × ℝ | 2 < |w.2| ∧
        1 ≤ |w.1.val * w.2| ∧ |w.1.val * w.2| ≤ 2} =
      bellmanRadialWeight β {s | 1 ≤ s.val ∧ s.val ≤ 2} *
        (∫⁻ y in {y : ℝ | 2 < |y|}, ENNReal.ofReal (|y| ^ (β - 4)) ∂F) := by
  have hm : MeasurableSet {w : BellmanPositiveTime × ℝ | 2 < |w.2| ∧
      1 ≤ |w.1.val * w.2| ∧ |w.1.val * w.2| ≤ 2} := by measurability
  rw [Measure.prod_apply_symm hm]
  have hf : (fun y => bellmanRadialWeight β
      ((fun s => (s, y)) ⁻¹' {w : BellmanPositiveTime × ℝ | 2 < |w.2| ∧
        1 ≤ |w.1.val * w.2| ∧ |w.1.val * w.2| ≤ 2})) =
      {y : ℝ | 2 < |y|}.indicator (fun y =>
        ENNReal.ofReal (|y| ^ (β - 4)) *
          bellmanRadialWeight β {s | 1 ≤ s.val ∧ s.val ≤ 2}) := by
    funext y
    by_cases hy : 2 < |y|
    · rw [indicator_of_mem (show y ∈ {y : ℝ | 2 < |y|} from hy)]
      have he : ((fun s => (s, y)) ⁻¹'
          {w : BellmanPositiveTime × ℝ | 2 < |w.2| ∧
            1 ≤ |w.1.val * w.2| ∧ |w.1.val * w.2| ≤ 2}) =
          {s : BellmanPositiveTime | 1 ≤ |y| * s.val ∧ |y| * s.val ≤ 2} := by
        ext s
        simp only [mem_preimage, mem_ofPred_eq, hy, true_and, abs_mul,
          abs_of_pos s.property, mul_comm s.val |y|]
      rw [he]
      exact bellmanRadialWeight_velocity_strip β |y| (by linarith)
    · rw [indicator_of_notMem (show y ∉ {y : ℝ | 2 < |y|} from hy)]
      have he : ((fun s => (s, y)) ⁻¹'
          {w : BellmanPositiveTime × ℝ | 2 < |w.2| ∧
            1 ≤ |w.1.val * w.2| ∧ |w.1.val * w.2| ≤ 2}) = ∅ := by
        ext s
        simp only [mem_preimage, mem_ofPred_eq, hy, false_and, mem_empty_iff_false]
      rw [he, measure_empty]
  rw [hf, lintegral_indicator (by measurability), lintegral_mul_const _ (by fun_prop)]
  exact mul_comm _ _

/-- Local finiteness of the original measure implies finite weighted angular tail mass. -/
theorem bellmanAngularTail_lintegral_finite (β : ℝ) (μ : Measure BellmanPuncturedPlane)
    [IsFiniteMeasureOnCompacts μ] (F : Measure ℝ) [IsFiniteMeasureOnCompacts F]
    (hrep : μ.restrict {q | 0 < q.val.1} = bellmanAngularRep β F) :
    (∫⁻ y in {y : ℝ | 2 < |y|}, ENNReal.ofReal (|y| ^ (β - 4)) ∂F) < ⊤ := by
  have hm := bellmanAngularTail_strip_finite β μ F hrep
  rw [bellmanAngularTail_strip_mass] at hm
  exact ENNReal.lt_top_of_mul_ne_top_right hm.ne (bellmanRadialWeight_reference_ne_zero β)

end HypoellipticAleksandrov.KineticAleksandrov
