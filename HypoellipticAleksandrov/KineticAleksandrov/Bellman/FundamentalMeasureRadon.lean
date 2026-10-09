module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureMajorant
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.PairSetting
public import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-! # Compact-uniform bounds and Radon regularity of the fundamental measure -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- Squared Euclidean distance is positive on the actual punctured plane. -/
theorem bellmanPunctured_sq_pos (q : BellmanPuncturedPlane) :
    0 < q.val.1 ^ 2 + q.val.2 ^ 2 := by
  refine lt_of_le_of_ne (add_nonneg (sq_nonneg _) (sq_nonneg _)) ?_
  intro h
  apply q.property
  have hx : q.val.1 = 0 := by nlinarith only [h, sq_nonneg q.val.2]
  have hv : q.val.2 = 0 := by nlinarith only [h, sq_nonneg q.val.1]
  exact Prod.ext hx hv

/-- A punctured compact set has a positive uniform squared-distance lower bound. -/
theorem bellmanPunctured_compact_lower_bound (K : Set BellmanPuncturedPlane)
    (hK : IsCompact K) : ∃ a : ℝ, 0 < a ∧ ∀ q ∈ K, a ≤ q.val.1 ^ 2 + q.val.2 ^ 2 := by
  by_cases hne : K.Nonempty
  · have hc : Continuous (fun q : BellmanPuncturedPlane => q.val.1 ^ 2 + q.val.2 ^ 2) := by
      fun_prop
    obtain ⟨q, hq, hmin⟩ := hK.exists_isMinOn hne hc.continuousOn
    exact ⟨_, bellmanPunctured_sq_pos q, fun z hz => hmin hz⟩
  · refine ⟨1, by norm_num, ?_⟩
    intro q hq
    exact (hne ⟨q, hq⟩).elim

/-- Lebesgue measure pulled back to the punctured plane is finite on compact sets. -/
instance bellmanPuncturedVolume_finiteOnCompacts :
    IsFiniteMeasureOnCompacts bellmanPuncturedVolume := by
  apply IsFiniteMeasureOnCompacts.comap' _ continuous_subtype_val
  exact MeasurableEmbedding.subtype_coe (isOpen_compl_singleton.measurableSet)

/-- The time-integrated fundamental measure is finite on punctured compact sets. -/
instance bellmanFundamentalMeasure_finiteOnCompacts :
    IsFiniteMeasureOnCompacts bellmanFundamentalMeasure where
  lt_top_of_isCompact K hK := by
    obtain ⟨a, ha, hbound⟩ := bellmanPunctured_compact_lower_bound K hK
    let C : ENNReal := ∫⁻ t : BellmanPositiveTime,
      ENNReal.ofReal (bellmanTimeMajorant a t.val) ∂bellmanPositiveTimeVolume
    have hC : C ≠ ⊤ := bellmanTimeMajorant_lintegral_ne_top a
    calc
      bellmanFundamentalMeasure K = ∫⁻ q in K, bellmanFundamentalDensity q
          ∂bellmanPuncturedVolume := withDensity_apply _ hK.measurableSet
      _ ≤ ∫⁻ _q in K, C ∂bellmanPuncturedVolume := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hK.measurableSet] with q hq
        exact bellmanFundamentalDensity_le_majorant a ha q (hbound q hq)
      _ = C * bellmanPuncturedVolume K := by rw [lintegral_const, Measure.restrict_apply_univ]
      _ < ⊤ := ENNReal.mul_lt_top hC.lt_top hK.measure_lt_top

/-- Inner regularity follows from local finiteness on the locally compact punctured plane. -/
instance bellmanFundamentalMeasure_innerRegular :
    Measure.InnerRegular bellmanFundamentalMeasure := by
  let : LocallyCompactSpace BellmanPuncturedPlane :=
    isOpen_compl_singleton.locallyCompactSpace
  infer_instance

/-- Both source Radon requirements hold for the actual time-integrated measure. -/
theorem bellmanFundamentalMeasure_radon : IsBellmanRadon bellmanFundamentalMeasure :=
  ⟨inferInstance, inferInstance⟩

end HypoellipticAleksandrov.KineticAleksandrov
