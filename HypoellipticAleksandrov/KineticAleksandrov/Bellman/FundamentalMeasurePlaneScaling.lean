module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureDensityScaling
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasurePositive
import Mathlib.Tactic

/-! # The determinant factor for kinetic dilation of punctured-plane volume -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- Product-plane Lebesgue measure has no point masses. -/
instance bellmanPlaneVolume_nullSingleton : NullSingletonClass (volume : Measure (ℝ × ℝ)) := by
  rw [Measure.volume_eq_prod]
  infer_instance

/-- Removing the origin does not change ambient Lebesgue measure. -/
theorem map_bellmanPuncturedVolume_coe :
    Measure.map (Subtype.val : BellmanPuncturedPlane → ℝ × ℝ) bellmanPuncturedVolume =
      volume := by
  unfold bellmanPuncturedVolume
  have hm : MeasurableSet {q : ℝ × ℝ | q ≠ (0, 0)} :=
    isOpen_compl_singleton.measurableSet
  calc
    _ = (volume : Measure (ℝ × ℝ)).restrict {q | q ≠ (0, 0)} := by
      convert! map_comap_subtype_coe hm volume using 1
    _ = _ := by
      apply Measure.restrict_eq_self_of_ae_mem
      apply ae_iff.mpr
      simpa only [Set.mem_ofPred_eq, not_not, Set.ofPred_eq_eq_singleton] using
        (measure_singleton (μ := (volume : Measure (ℝ × ℝ))) (0, 0))

/-- The ambient dilation has determinant r to the fourth power. -/
theorem map_bellmanPlaneDilation_volume (r : ℝ) (hr : 0 < r) :
    Measure.map (bellmanPlaneDilation r) (volume : Measure (ℝ × ℝ)) =
      ENNReal.ofReal (r⁻¹ ^ 4) • volume := by
  rw [Measure.volume_eq_prod]
  change Measure.map (Prod.map (fun x : ℝ => r ^ 3 * x) (fun v : ℝ => r * v))
    ((volume : Measure ℝ).prod volume) = _
  rw [← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Real.map_volume_mul_left (pow_ne_zero 3 hr.ne'), Real.map_volume_mul_left hr.ne',
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 2
  rw [abs_of_pos (inv_pos.mpr (pow_pos hr 3)), abs_of_pos (inv_pos.mpr hr)]
  ring

/-- Positive kinetic dilation of the punctured plane is measurable. -/
theorem measurable_bellmanDilation (r : ℝ) (hr : 0 < r) :
    Measurable (bellmanDilation r hr) := by
  apply Continuous.measurable
  unfold bellmanDilation
  fun_prop

/-- Punctured-plane volume has the same determinant scaling as ambient volume. -/
theorem map_bellmanPuncturedVolume_dilation (r : ℝ) (hr : 0 < r) :
    Measure.map (bellmanDilation r hr) bellmanPuncturedVolume =
      ENNReal.ofReal (r⁻¹ ^ 4) • bellmanPuncturedVolume := by
  have he : MeasurableEmbedding (Subtype.val : BellmanPuncturedPlane → ℝ × ℝ) :=
    MeasurableEmbedding.subtype_coe isOpen_compl_singleton.measurableSet
  apply he.map_injective
  rw [Measure.map_map he.measurable (measurable_bellmanDilation r hr)]
  change Measure.map ((bellmanPlaneDilation r) ∘
    (Subtype.val : BellmanPuncturedPlane → ℝ × ℝ)) bellmanPuncturedVolume = _
  rw [← Measure.map_map (by unfold bellmanPlaneDilation; fun_prop) he.measurable,
    map_bellmanPuncturedVolume_coe, map_bellmanPlaneDilation_volume r hr,
    Measure.map_smul _ he.measurable.aemeasurable, map_bellmanPuncturedVolume_coe]

end HypoellipticAleksandrov.KineticAleksandrov
