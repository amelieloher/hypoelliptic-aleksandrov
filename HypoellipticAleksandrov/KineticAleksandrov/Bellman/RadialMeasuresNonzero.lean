module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.RadialMeasuresProper
import Mathlib.Tactic

/-! # Nonvanishing of radial measures constructed from a probability -/

@[expose] public section
noncomputable section
open MeasureTheory Set
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- Positive subtype volume is nonzero, as witnessed by its real pushforward. -/
theorem bellmanPositiveTimeVolume_ne_zero : bellmanPositiveTimeVolume ≠ 0 := by
  intro hz
  have hm := map_bellmanPositiveTimeVolume_coe
  rw [hz, Measure.map_zero] at hm
  have he := congrArg (fun mu : Measure ℝ => mu (Icc 1 2)) hm
  have hi : Icc (1 : ℝ) 2 ∩ Ioi 0 = Icc 1 2 :=
    inter_eq_left.mpr (fun x hx => lt_of_lt_of_le (by norm_num) hx.1)
  norm_num [Measure.restrict_apply measurableSet_Icc, hi] at he

/-- The strictly positive radial density cannot annihilate positive radial volume. -/
theorem bellmanRadiusMeasure_ne_zero (alpha : ℝ) : bellmanRadiusMeasure alpha ≠ 0 := by
  intro hz
  have hae := (withDensity_eq_zero_iff
    (measurable_bellmanRadiusWeight alpha).aemeasurable).mp hz
  have hf : ∀ r : BellmanPositiveTime, bellmanRadiusWeight alpha r ≠ 0 := by
    intro r
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos r.property _))
  have hempty : (∅ : Set BellmanPositiveTime) ∈ ae bellmanPositiveTimeVolume := by
    filter_upwards [hae] with r hr
    exact (hf r hr).elim
  exact bellmanPositiveTimeVolume_ne_zero (by
    apply MeasureTheory.ae_eq_bot.mp
    exact Filter.empty_mem_iff_bot.mp hempty)

/-- The radius marginal of the first projected measure is the original weighted radial volume. -/
theorem radialMu_radius_marginal {lam Lam : ℝ} (alpha : ℝ)
    (pi : Measure (BellmanSphere × BellmanCoefficient lam Lam)) [IsProbabilityMeasure pi] :
    Measure.map bellmanGaugeRadius (radialMu alpha pi) = bellmanRadiusMeasure alpha := by
  unfold radialMu
  rw [Measure.map_map continuous_bellmanGaugeRadius.measurable
    (continuous_sphereRadialPoint lam Lam).measurable]
  have he : bellmanGaugeRadius ∘ (sphereRadialPoint (lam := lam) (Lam := Lam)) =
      Prod.fst := by
    funext w
    exact Subtype.ext (sphereRadialPoint_gauge w)
  rw [he, Measure.map_fst_prod, measure_univ, one_smul]

/-- A probability on the sphere produces a genuinely nonzero first adjoint measure. -/
theorem radialMu_ne_zero {lam Lam : ℝ} (alpha : ℝ)
    (pi : Measure (BellmanSphere × BellmanCoefficient lam Lam)) [IsProbabilityMeasure pi] :
    radialMu alpha pi ≠ 0 := by
  intro hz
  have hm := radialMu_radius_marginal alpha pi
  rw [hz, Measure.map_zero] at hm
  exact bellmanRadiusMeasure_ne_zero alpha hm.symm

end HypoellipticAleksandrov.KineticAleksandrov
