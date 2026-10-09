module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.HomogeneousTestLiftSupport
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-! # Compact positive-radius windows and their literal integral restrictions -/

@[expose] public section
noncomputable section
open Set MeasureTheory
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- A closed interval of positive radii is compact on the source radial subtype. -/
theorem bellmanRadiusWindow_isCompact (a b : ℝ) (ha : 0 < a) :
    IsCompact {r : BellmanPositiveTime | r.val ∈ Icc a b} := by
  apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
  have he : (Subtype.val : BellmanPositiveTime → ℝ) '' {r | r.val ∈ Icc a b} =
      Icc a b := by
    ext r
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact hs
    · intro hr
      exact ⟨⟨r, lt_of_lt_of_le ha hr.1⟩, hr, rfl⟩
  rw [he]
  exact isCompact_Icc

/-- Restricting a test to a compact radial window is exactly a subtype integral. -/
theorem bellman_integral_compact_radius_subtype {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (K : Set BellmanPositiveTime) (hK : IsCompact K)
    (f : BellmanPositiveTime → F) (hf : ∀ r, r ∉ K → f r = 0) :
    (∫ r, f r ∂bellmanPositiveTimeVolume) =
      ∫ r : K, f r.val ∂Measure.comap Subtype.val bellmanPositiveTimeVolume := by
  rw [← (MeasurableEmbedding.subtype_coe hK.measurableSet).integral_map,
    map_comap_subtype_coe hK.measurableSet]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero hf).symm

/-- Pullback radial volume is finite on a compact radius window. -/
theorem bellman_radius_window_volume_finite (K : Set BellmanPositiveTime)
    (hK : IsCompact K) :
    IsFiniteMeasure (Measure.comap (Subtype.val : K → BellmanPositiveTime)
      bellmanPositiveTimeVolume) := by
  have hm : IsFiniteMeasure (bellmanPositiveTimeVolume.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  let := hm
  have he : Measure.comap (Subtype.val : K → BellmanPositiveTime)
      bellmanPositiveTimeVolume = Measure.comap Subtype.val
      (bellmanPositiveTimeVolume.restrict K) := by
    apply (MeasurableEmbedding.subtype_coe hK.measurableSet).map_injective
    rw [map_comap_subtype_coe hK.measurableSet,
      map_comap_subtype_coe hK.measurableSet, Measure.restrict_restrict hK.measurableSet,
      inter_self]
  rw [he]
  infer_instance

end HypoellipticAleksandrov.KineticAleksandrov
