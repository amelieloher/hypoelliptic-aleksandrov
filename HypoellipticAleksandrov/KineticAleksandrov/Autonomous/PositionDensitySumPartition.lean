module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionOverlap
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-! # Output-cell partition of the actual positive Green density -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

/-- Raising the positive norm to its exponent recovers the power integral. -/
theorem positionPositiveNorm_rpow {X : Type*} [MeasurableSpace X]
    (m : Measure X) (q : ℝ) (hq : 0 < q) (f : X → ℝ≥0∞) :
    positionPositiveNorm m q f ^ q = ∫⁻ z, f z ^ q ∂m := by
  rw [positionPositiveNorm, ← ENNReal.rpow_mul,
    one_div_mul_cancel hq.ne', ENNReal.rpow_one]

/-- The output cells partition the region after the grid origin in the active interval. -/
theorem enlargedOutputCell_iUnion (c : Clock) (s x : ℝ) :
    (⋃ a : ℕ × ℤ, enlargedOutputCell c s x a.1 a.2) =
      {p | s ≤ p.time ∧ p.velocity 0 ∈ c.active} := by
  unfold enlargedOutputCell
  rw [← iUnion_inter, enlargedStartCell_iUnion]
  rfl

/-- The output-cell partition is pairwise disjoint. -/
theorem enlargedOutputCell_pairwiseDisjoint (c : Clock) (s x : ℝ) :
    Pairwise (fun a b : ℕ × ℤ =>
      Disjoint (enlargedOutputCell c s x a.1 a.2) (enlargedOutputCell c s x b.1 b.2)) := by
  intro a b hab
  exact (enlargedStartCell_pairwiseDisjoint c s x hab).mono inter_subset_left inter_subset_left

/-- A mixture started after the origin stays after the origin in the active interval. -/
theorem positionMixtureDensity_support (hpush : PushforwardStatement)
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (hc : |c.vbar| = 2 * c.r)
    (nu : Measure Point) [SFinite nu] (s : ℝ)
    (hnu : ∀ᵐ e ∂nu, s ≤ e.time ∧ e.velocity 0 ∈ c.active) :
    ∀ᵐ z ∂(volume : Measure Point),
      positionMixtureDensity hH hLE hlam hLam A c nu z ≠ 0 →
        s ≤ z.time ∧ z.velocity 0 ∈ c.active := by
  have hm := measurable_positionMixtureDensity hH hLE hlam hLam A c nu
  apply (ae_withDensity_iff hm).mp
  rw [withDensity_positionMixtureDensity hpush hH hLE hlam hLam]
  have hS : MeasurableSet {z : Point | s ≤ z.time ∧ z.velocity 0 ∈ c.active} :=
    (measurableSet_Ici.preimage continuous_time.measurable).inter
      (isOpen_Ioo.measurableSet.preimage ((continuous_apply 0).comp continuous_velocity).measurable)
  apply Measure.ae_comp_of_ae_ae hS
  filter_upwards [hnu] with e he
  rw [← withDensity_positionActiveDensity hpush hH hLE hlam hLam]
  apply (ae_withDensity_iff ((measurable_positionActiveDensity hH hLE hlam hLam A c).comp
    (measurable_const.prodMk measurable_id))).mpr
  filter_upwards [positionActiveDensity_support hpush hH hLE hlam hLam A c hc e he.2]
    with z hz hnonzero
  exact ⟨he.1.trans (hz hnonzero).1.le, (hz hnonzero).2.1⟩

/-- Summing output-cell q-power norms recovers the full density power integral. -/
theorem positionMixtureDensity_power_partition (hpush : PushforwardStatement)
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (hc : |c.vbar| = 2 * c.r)
    (nu : Measure Point) [SFinite nu] (s x q : ℝ) (hq : 0 < q)
    (hnu : ∀ᵐ e ∂nu, s ≤ e.time ∧ e.velocity 0 ∈ c.active) :
    (∫⁻ z, positionMixtureDensity hH hLE hlam hLam A c nu z ^ q ∂volume) =
      ∑' a : ℕ × ℤ,
        positionPositiveNorm (volume.restrict (enlargedOutputCell c s x a.1 a.2)) q
          (positionMixtureDensity hH hLE hlam hLam A c nu) ^ q := by
  let F := positionMixtureDensity hH hLE hlam hLam A c nu
  let U := {z : Point | s ≤ z.time ∧ z.velocity 0 ∈ c.active}
  have hU : MeasurableSet U := (measurableSet_Ici.preimage continuous_time.measurable).inter
    (isOpen_Ioo.measurableSet.preimage ((continuous_apply 0).comp continuous_velocity).measurable)
  have he : (∫⁻ z, F z ^ q ∂volume) = ∫⁻ z in U, F z ^ q ∂volume := by
    rw [← lintegral_indicator hU]
    apply lintegral_congr_ae
    filter_upwards [positionMixtureDensity_support hpush hH hLE hlam hLam A c hc nu s hnu]
      with z hz
    by_cases h : z ∈ U
    · simp only [indicator_of_mem h]
    · have hf : F z = 0 := by by_contra hn; exact h (hz hn)
      simp only [indicator_of_notMem h, hf, ENNReal.zero_rpow_of_pos hq]
  rw [he]
  dsimp only [U]
  rw [← enlargedOutputCell_iUnion c s x,
    lintegral_iUnion (fun a : ℕ × ℤ => measurableSet_enlargedOutputCell c s x a.1 a.2)
      (enlargedOutputCell_pairwiseDisjoint c s x)]
  apply tsum_congr
  intro a
  exact (positionPositiveNorm_rpow _ q hq F).symm

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
