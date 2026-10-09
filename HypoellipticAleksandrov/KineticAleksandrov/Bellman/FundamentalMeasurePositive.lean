module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureRadon
import Mathlib.Tactic

/-! # Nontriviality of the literal time-integrated Gaussian measure -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- Positive-time Lebesgue measure has infinite total mass. -/
theorem bellmanPositiveTimeVolume_univ : bellmanPositiveTimeVolume univ = ⊤ := by
  unfold bellmanPositiveTimeVolume
  calc
    _ = (volume.restrict (Ioi (0 : ℝ)))
        (Subtype.val '' (univ : Set BellmanPositiveTime)) := by
      convert! (MeasurableEmbedding.subtype_coe (s := Ioi (0 : ℝ))
        measurableSet_Ioi).comap_apply (volume.restrict (Ioi (0 : ℝ))) univ using 1
    _ = ⊤ := by
      simp only [image_univ, Subtype.range_val_subtype]
      change (volume.restrict (Ioi (0 : ℝ))) (Ioi 0) = ⊤
      rw [Measure.restrict_apply measurableSet_Ioi, inter_self, Real.volume_Ioi]

/-- The time-integrated Gaussian density is strictly positive off its pole. -/
theorem bellmanFundamentalDensity_pos (q : BellmanPuncturedPlane) :
    0 < bellmanFundamentalDensity q := by
  have hf : Measurable (fun t : BellmanPositiveTime =>
      ENNReal.ofReal (bellmanGaussianKernel t q.val)) :=
    ENNReal.measurable_ofReal.comp
      (continuous_bellmanGaussianKernel.comp
        (continuous_id.prodMk continuous_const)).measurable
  have hs : Function.support (fun t : BellmanPositiveTime =>
      ENNReal.ofReal (bellmanGaussianKernel t q.val)) = univ := by
    apply eq_univ_of_forall
    intro t
    exact (ENNReal.ofReal_pos.mpr (bellmanGaussianKernel_pos t q.val)).ne'
  apply (lintegral_pos_iff_support hf).mpr
  rw [hs, bellmanPositiveTimeVolume_univ]
  exact ENNReal.zero_lt_top

/-- Punctured-plane Lebesgue measure retains the infinite mass of the whole plane. -/
theorem bellmanPuncturedVolume_univ : bellmanPuncturedVolume univ = ⊤ := by
  unfold bellmanPuncturedVolume
  calc
    _ = (volume : Measure (ℝ × ℝ))
        (Subtype.val '' (univ : Set BellmanPuncturedPlane)) := by
      convert! (MeasurableEmbedding.subtype_coe
        (s := ({(0, 0)} : Set (ℝ × ℝ))ᶜ)
        isOpen_compl_singleton.measurableSet).comap_apply volume univ using 1
    _ = ⊤ := by
      simp only [image_univ, Subtype.range_val_subtype]
      change (volume : Measure (ℝ × ℝ)) ({(0, 0)}ᶜ) = ⊤
      have h := measure_add_measure_compl
        (μ := (volume : Measure (ℝ × ℝ))) (measurableSet_singleton (0, 0))
      have h0 : (volume : Measure (ℝ × ℝ)) {(0, 0)} = 0 := by
        rw [Measure.volume_eq_prod]
        have hs : ({(0, 0)} : Set (ℝ × ℝ)) = ({0} : Set ℝ) ×ˢ {0} := by
          ext q
          simp only [mem_singleton_iff, mem_prod]
          exact Prod.ext_iff
        rw [hs, Measure.prod_prod, Real.volume_singleton, zero_mul]
      have hu : (volume : Measure (ℝ × ℝ)) univ = ⊤ := by
        rw [Measure.volume_eq_prod, ← univ_prod_univ, Measure.prod_prod,
          Real.volume_univ, ENNReal.top_mul_top]
      rw [h0, zero_add, hu] at h
      exact h

/-- The actual fundamental measure is nonzero, without assuming a solution exists. -/
theorem bellmanFundamentalMeasure_ne_zero : bellmanFundamentalMeasure ≠ 0 := by
  intro h
  have hz : ∫⁻ q, bellmanFundamentalDensity q ∂bellmanPuncturedVolume = 0 := by
    have h0 := congrArg (fun μ : Measure BellmanPuncturedPlane => μ univ) h
    simpa only [bellmanFundamentalMeasure, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ, Measure.coe_zero, Pi.zero_apply] using h0
  have hs : Function.support bellmanFundamentalDensity = univ := by
    apply eq_univ_of_forall
    intro q
    exact (bellmanFundamentalDensity_pos q).ne'
  have hp := (lintegral_pos_iff_support measurable_bellmanFundamentalDensity).mpr
    (show 0 < bellmanPuncturedVolume (Function.support bellmanFundamentalDensity) by
      rw [hs, bellmanPuncturedVolume_univ]; exact ENNReal.zero_lt_top)
  exact hp.ne' hz

end HypoellipticAleksandrov.KineticAleksandrov
