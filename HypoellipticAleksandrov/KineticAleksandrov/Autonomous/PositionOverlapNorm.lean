module

public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Topology.Order.Monotone
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # Extended positive Lq triangle inequalities for countable mixtures -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory Filter
open scoped ENNReal

/-- The positive extended Lq norm, before converting a finite density to real values. -/
def positionPositiveNorm {X : Type*} [MeasurableSpace X]
    (m : Measure X) (q : ℝ) (f : X → ℝ≥0∞) : ℝ≥0∞ :=
  (∫⁻ x, f x ^ q ∂m) ^ (1 / q)

/-- Positive real powers commute with arbitrary indexed suprema in ENNReal. -/
theorem position_rpow_iSup {ι : Sort*} (a : ι → ℝ≥0∞) (q : ℝ) (hq : 0 < q) :
    (⨆ i, a i) ^ q = ⨆ i, a i ^ q :=
  Monotone.map_iSup_of_continuousAt (ENNReal.continuous_rpow_const (y := q)).continuousAt
    (fun _ _ h => ENNReal.rpow_le_rpow h hq.le)
    (ENNReal.zero_rpow_of_pos hq)

/-- The extended positive Lq norm satisfies the finite triangle inequality. -/
theorem positionPositiveNorm_add {X : Type*} [MeasurableSpace X]
    (m : Measure X) (q : ℝ) (hq : 1 ≤ q) (f g : X → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) :
    positionPositiveNorm m q (f + g) ≤
      positionPositiveNorm m q f + positionPositiveNorm m q g :=
  ENNReal.lintegral_Lp_add_le hf.aemeasurable hg.aemeasurable hq

/-- The extended positive Lq norm satisfies the finite-sum triangle inequality. -/
theorem positionPositiveNorm_finsetSum {X ι : Type*} [MeasurableSpace X]
    (m : Measure X) (q : ℝ) (hq : 1 ≤ q) (f : ι → X → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) (S : Finset ι) :
    positionPositiveNorm m q (fun x => ∑ i ∈ S, f i x) ≤
      ∑ i ∈ S, positionPositiveNorm m q (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, positionPositiveNorm,
      ENNReal.zero_rpow_of_pos (by linarith : 0 < q), lintegral_zero,
      ENNReal.zero_rpow_of_pos (one_div_pos.mpr (by linarith : 0 < q)), le_refl]
  | @insert i S hi ih =>
    simp_rw [Finset.sum_insert hi]
    exact (positionPositiveNorm_add m q hq _ _ (hf i)
      (Finset.measurable_sum S (fun j _ => hf j))).trans (add_le_add le_rfl ih)

/-- Countably many positive densities obey Minkowski without an integrability side premise. -/
theorem positionPositiveNorm_tsum {X ι : Type*} [MeasurableSpace X] [Countable ι]
    (m : Measure X) (q : ℝ) (hq : 1 ≤ q) (f : ι → X → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    positionPositiveNorm m q (fun x => ∑' i, f i x) ≤
      ∑' i, positionPositiveNorm m q (f i) := by
  classical
  have hq0 : 0 < q := by linarith
  have hm (S : Finset ι) : Measurable (fun x => (∑ i ∈ S, f i x) ^ q) :=
    (Finset.measurable_sum S (fun i _ => hf i)).pow_const q
  have hd : Directed (· ≤ ·) (fun S : Finset ι => fun x => (∑ i ∈ S, f i x) ^ q) := by
    intro S T
    refine ⟨S ∪ T, ?_, ?_⟩
    · intro x
      exact ENNReal.rpow_le_rpow (Finset.sum_le_sum_of_subset_of_nonneg
        Finset.subset_union_left (fun _ _ _ => zero_le)) hq0.le
    · intro x
      exact ENNReal.rpow_le_rpow (Finset.sum_le_sum_of_subset_of_nonneg
        Finset.subset_union_right (fun _ _ _ => zero_le)) hq0.le
  have he : positionPositiveNorm m q (fun x => ∑' i, f i x) =
      ⨆ S : Finset ι, positionPositiveNorm m q (fun x => ∑ i ∈ S, f i x) := by
    unfold positionPositiveNorm
    simp_rw [ENNReal.tsum_eq_iSup_sum, position_rpow_iSup _ q hq0]
    rw [lintegral_iSup_directed_of_measurable hm hd,
      position_rpow_iSup _ (1 / q) (one_div_pos.mpr hq0)]
  rw [he]
  refine iSup_le (fun S => (positionPositiveNorm_finsetSum m q hq f hf S).trans ?_)
  exact ENNReal.sum_le_tsum S

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
