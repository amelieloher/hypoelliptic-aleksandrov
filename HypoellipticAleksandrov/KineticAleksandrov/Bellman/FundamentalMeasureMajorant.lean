module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureTime
import Mathlib.Tactic

/-! # A uniform integrable time majorant away from the Gaussian pole -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- Time decomposition of the Gaussian bound, for a squared-distance lower bound a. -/
def bellmanTimeMajorant (a : ℝ) (t : ℝ) : ℝ :=
  (Ioc (0 : ℝ) 1).indicator
    (fun _ => 64 * Real.sqrt 3 / (Real.pi * a ^ 2)) t +
  (Ioi (1 : ℝ)).indicator (fun s => Real.sqrt 3 / (2 * Real.pi) * s ^ (-2 : ℝ)) t

/-- The time majorant is integrable on the positive half-line. -/
theorem integrable_bellmanTimeMajorant (a : ℝ) :
    Integrable (fun t : BellmanPositiveTime => bellmanTimeMajorant a t.val)
      bellmanPositiveTimeVolume := by
  have hsmall : IntegrableOn (fun _ : ℝ => 64 * Real.sqrt 3 / (Real.pi * a ^ 2))
      (Ioc (0 : ℝ) 1) := integrableOn_const measure_Ioc_lt_top.ne
  have hlarge : IntegrableOn (fun s : ℝ => Real.sqrt 3 / (2 * Real.pi) *
      s ^ (-2 : ℝ)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1)
      (by norm_num : (0 : ℝ) < 1)).const_mul _
  have hi : Integrable (bellmanTimeMajorant a) (volume : Measure ℝ) :=
    (hsmall.integrable_indicator measurableSet_Ioc).add
      (hlarge.integrable_indicator measurableSet_Ioi)
  have hmap : Measure.map (Subtype.val : BellmanPositiveTime → ℝ)
      bellmanPositiveTimeVolume = volume.restrict (Ioi (0 : ℝ)) := by
    unfold bellmanPositiveTimeVolume
    convert! map_comap_subtype_coe (s := Ioi (0 : ℝ)) measurableSet_Ioi
      (volume.restrict (Ioi (0 : ℝ))) using 1
    rw [Measure.restrict_restrict measurableSet_Ioi, inter_self]
  have h : Integrable (bellmanTimeMajorant a)
      (Measure.map (Subtype.val : BellmanPositiveTime → ℝ) bellmanPositiveTimeVolume) := by
    rw [hmap]
    exact hi.restrict
  exact (MeasurableEmbedding.subtype_coe (s := Ioi (0 : ℝ))
    measurableSet_Ioi).integrable_map_iff.mp h

/-- The majorant is nonnegative at positive time. -/
theorem bellmanTimeMajorant_nonneg (a : ℝ) (t : BellmanPositiveTime) :
    0 ≤ bellmanTimeMajorant a t.val := by
  unfold bellmanTimeMajorant
  apply add_nonneg
  · exact indicator_nonneg (fun _ _ => by positivity) _
  · apply indicator_nonneg _ _
    intro s hs
    have hspos : 0 < s := lt_trans (by norm_num) hs
    positivity

/-- The same time majorant bounds every point with squared distance at least a. -/
theorem bellmanGaussianKernel_le_timeMajorant (a : ℝ) (ha : 0 < a)
    (q : ℝ × ℝ) (hq : a ≤ q.1 ^ 2 + q.2 ^ 2) (t : BellmanPositiveTime) :
    bellmanGaussianKernel t q ≤ bellmanTimeMajorant a t.val := by
  by_cases ht : t.val ≤ 1
  · simp only [bellmanTimeMajorant, indicator_of_mem (show t.val ∈ Ioc (0 : ℝ) 1
      from ⟨t.property, ht⟩), indicator_of_notMem (show t.val ∉ Ioi (1 : ℝ)
      from not_lt.mpr ht), add_zero]
    exact bellmanGaussianKernel_le_smallTime t ht q a ha hq
  · have h1 : 1 < t.val := lt_of_not_ge ht
    simp only [bellmanTimeMajorant, indicator_of_notMem
      (show t.val ∉ Ioc (0 : ℝ) 1 from fun h => ht h.2),
      indicator_of_mem (show t.val ∈ Ioi (1 : ℝ) from h1), zero_add]
    convert bellmanGaussianKernel_le t q using 1
    rw [Real.rpow_neg t.property.le, Real.rpow_two]
    ring

/-- Uniform bound on the actual time-integrated density away from the origin. -/
theorem bellmanFundamentalDensity_le_majorant (a : ℝ) (ha : 0 < a)
    (q : BellmanPuncturedPlane) (hq : a ≤ q.val.1 ^ 2 + q.val.2 ^ 2) :
    bellmanFundamentalDensity q ≤
      ∫⁻ t : BellmanPositiveTime, ENNReal.ofReal (bellmanTimeMajorant a t.val)
        ∂bellmanPositiveTimeVolume := by
  exact lintegral_mono fun t => ENNReal.ofReal_le_ofReal
    (bellmanGaussianKernel_le_timeMajorant a ha q.val hq t)

/-- The integrated majorant is a finite uniform bound. -/
theorem bellmanTimeMajorant_lintegral_ne_top (a : ℝ) :
    (∫⁻ t : BellmanPositiveTime, ENNReal.ofReal (bellmanTimeMajorant a t.val)
      ∂bellmanPositiveTimeVolume) ≠ ⊤ := by
  have h := integrable_bellmanTimeMajorant a
  exact (lintegral_ofReal_ne_top_iff_integrable h.aestronglyMeasurable
    (ae_of_all _ (bellmanTimeMajorant_nonneg a))).mpr h

end HypoellipticAleksandrov.KineticAleksandrov
