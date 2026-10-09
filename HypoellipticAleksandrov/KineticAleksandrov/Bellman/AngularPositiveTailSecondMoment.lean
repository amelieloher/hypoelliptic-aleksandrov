module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularPositiveTailFirstMoment
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDensitiesMoments
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-! # Vanishing second moment divided by radius from finite first moment -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set Filter
open scoped Topology

/-- Finite positive first moment forces the second moment divided by y to vanish. -/
theorem bellmanAngularSecondMoment_div_tendsto (f : ℝ → ℝ)
    (_hf : LocallyIntegrable f volume)
    (hi : IntegrableOn (fun z => z * f z) (Ioi 0) volume) :
    Tendsto (fun y => bellmanAngularSecondMoment f y / y) atTop (𝓝 0) := by
  let G := fun y : ℝ => (Iic y).indicator (fun z => (z / y) * (z * f z))
  have hmeas : ∀ᶠ y : ℝ in atTop,
      AEStronglyMeasurable (G y) (volume.restrict (Ioi 0)) := by
    apply Eventually.of_forall
    intro y
    exact ((measurable_id.div_const y).aestronglyMeasurable.mul
      hi.aestronglyMeasurable).indicator measurableSet_Iic
  have hbound : ∀ᶠ y : ℝ in atTop, ∀ᵐ z ∂volume.restrict (Ioi 0),
      ‖G y z‖ ≤ ‖z * f z‖ := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    by_cases hzy : z ≤ y
    · rw [show G y z = (z / y) * (z * f z) from indicator_of_mem (show z ∈ Iic y from hzy) _]
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hz.le (by linarith))]
      apply mul_le_of_le_one_left (norm_nonneg _)
      exact (div_le_one (by linarith : 0 < y)).mpr hzy
    · rw [show G y z = 0 from indicator_of_notMem (show z ∉ Iic y from hzy) _]
      simpa only [norm_zero] using norm_nonneg (z * f z)
  have hlim : ∀ᵐ z ∂volume.restrict (Ioi 0),
      Tendsto (fun y => G y z) atTop (𝓝 (0 : ℝ)) := by
    apply ae_of_all
    intro z
    have he : (fun y => G y z) =ᶠ[atTop] (fun y => (z / y) * (z * f z)) := by
      filter_upwards [eventually_ge_atTop z] with y hy
      exact indicator_of_mem (show z ∈ Iic y from hy) _
    have hr : Tendsto (fun y : ℝ => z / y) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have ht := hr.mul_const (z * f z)
    simpa only [zero_mul] using ht.congr' he.symm
  have ht := tendsto_integral_filter_of_dominated_convergence
    (fun z => ‖z * f z‖) hmeas hbound hi.norm hlim
  simp only [integral_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
  dsimp [G]
  rw [integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
    show Iic y ∩ Ioi (0 : ℝ) = Ioc 0 y from
      Set.ext (fun z => by simp only [mem_inter_iff, mem_Iic, mem_Ioi, mem_Ioc]; tauto),
    bellmanAngularSecondMoment, intervalIntegral.integral_of_le (by linarith : 0 ≤ y)]
  rw [← integral_div]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro z _
  ring

end HypoellipticAleksandrov.KineticAleksandrov
