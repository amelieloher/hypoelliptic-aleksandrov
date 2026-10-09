module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularCoordinatesMeasure
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic

/-! # Density transport and locally finite continuous weights for radial factorization -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

variable {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
  [MeasurableSpace A] [MeasurableSpace B] [BorelSpace A] [BorelSpace B]

/-- A homeomorphism transports a measurable density by its actual inverse. -/
theorem bellman_map_withDensity (T : A ≃ₜ B) (μ : Measure A)
    (f : A → ENNReal) (hf : Measurable f) :
    Measure.map T (μ.withDensity f) =
      (Measure.map T μ).withDensity (fun q => f (T.symm q)) := by
  ext S hS
  rw [Measure.map_apply T.measurable hS, withDensity_apply _ (T.measurable hS),
    withDensity_apply _ hS]
  rw [setLIntegral_map hS (show Measurable (fun q => f (T.symm q)) from
    hf.comp T.symm.measurable) T.measurable]
  simp only [T.symm_apply_apply]

/-- A continuous real weight preserves finiteness on compact sets. -/
theorem bellman_withDensity_finiteOnCompacts [T2Space A] (μ : Measure A)
    [IsFiniteMeasureOnCompacts μ] (f : A → ℝ) (hf : Continuous f) :
    IsFiniteMeasureOnCompacts (μ.withDensity (fun q => ENNReal.ofReal (f q))) where
  lt_top_of_isCompact K hK := by
    obtain ⟨M, hM⟩ := hK.bddAbove_image hf.continuousOn
    calc
      μ.withDensity (fun q => ENNReal.ofReal (f q)) K =
          ∫⁻ q in K, ENNReal.ofReal (f q) ∂μ := withDensity_apply _ hK.measurableSet
      _ ≤ ∫⁻ _q in K, ENNReal.ofReal M ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hK.measurableSet] with q hq
        exact ENNReal.ofReal_le_ofReal (hM ⟨q, hq, rfl⟩)
      _ = ENNReal.ofReal M * μ K := by
        rw [lintegral_const, Measure.restrict_apply_univ]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_ne_top.lt_top hK.measure_lt_top

/-- A homeomorphism preserves finiteness on compact sets. -/
theorem bellman_map_homeomorph_finiteOnCompacts [T2Space A] [T2Space B]
    (T : A ≃ₜ B) (μ : Measure A) [IsFiniteMeasureOnCompacts μ] :
    IsFiniteMeasureOnCompacts (Measure.map T μ) where
  lt_top_of_isCompact K hK := by
    rw [Measure.map_apply T.measurable hK.measurableSet]
    have he : T ⁻¹' K = T.symm '' K := by
      ext q
      constructor
      · intro hq
        exact ⟨T q, hq, T.symm_apply_apply q⟩
      · rintro ⟨z, hz, rfl⟩
        change T (T.symm z) ∈ K
        rw [T.apply_symm_apply]
        exact hz
    rw [he]
    exact (hK.image T.symm.continuous).measure_lt_top

/-- A positive position scale acts as an actual homeomorphism of the positive radial carrier. -/
def bellmanRadialScale (r : ℝ) (hr : 0 < r) :
    BellmanPositiveTime ≃ₜ BellmanPositiveTime where
  toFun s := ⟨r * s.val, mul_pos hr s.property⟩
  invFun s := ⟨r⁻¹ * s.val, mul_pos (inv_pos.mpr hr) s.property⟩
  left_inv s := by
    apply Subtype.ext
    simp only [inv_mul_cancel_left₀ hr.ne']
  right_inv s := by
    apply Subtype.ext
    simp only [mul_inv_cancel_left₀ hr.ne']
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Positive radial volume transforms by the inverse radial factor. -/
theorem map_bellmanPositiveTimeVolume_radialScale (r : ℝ) (hr : 0 < r) :
    Measure.map (bellmanRadialScale r hr) bellmanPositiveTimeVolume =
      ENNReal.ofReal r⁻¹ • bellmanPositiveTimeVolume := by
  have he : MeasurableEmbedding (Subtype.val : BellmanPositiveTime → ℝ) :=
    MeasurableEmbedding.subtype_coe measurableSet_Ioi
  apply he.map_injective
  rw [Measure.map_map he.measurable (bellmanRadialScale r hr).measurable]
  change Measure.map ((fun t : ℝ => r * t) ∘
    (Subtype.val : BellmanPositiveTime → ℝ)) bellmanPositiveTimeVolume = _
  rw [← Measure.map_map (by fun_prop) he.measurable,
    map_bellmanPositiveTimeVolume_coe, map_positiveVolume_mul r hr,
    Measure.map_smul _ he.measurable.aemeasurable, map_bellmanPositiveTimeVolume_coe]

end HypoellipticAleksandrov.KineticAleksandrov
