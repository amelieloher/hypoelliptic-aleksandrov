module

public import HypoellipticAleksandrov.Parabolic.SpatialDifferenceQuotientBound
public import HypoellipticAleksandrov.Topology.Support

/-!
# Cutoff-localized spatial difference-quotient fields

This module turns local `C¹` scalar data near a compact carrier into globally
continuous, compactly supported cutoff localizations of its small forward
spatial translates and totalized spatial difference quotients.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

/-- Local `C¹` data near a compact carrier have uniformly bounded,
continuous, compactly supported cutoff localizations of their small signed
spatial translates and difference quotients. -/
theorem IsCompact.exists_cutoff_mul_spatialFields_of_contDiffOn_one
    {d : ℕ} {S U : Set (TimeVelocity d)}
    (hS : IsCompact S) (hU : IsOpen U) (hSU : S ⊆ U)
    (q : TimeVelocity d → ℝ) (hq : ContDiffOn ℝ 1 q U) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧
      ∀ (β : TimeVelocity d → ℝ),
        Continuous β →
        HasCompactSupport β →
        tsupport β ⊆ S →
        (∀ z, ‖β z‖ ≤ 1) →
        ∀ (k : Fin d) (h : ℝ), |h| ≤ δ →
          (Continuous (fun z => β z * spatialTranslate k h q z) ∧
            HasCompactSupport (fun z => β z * spatialTranslate k h q z) ∧
            ∀ z, ‖β z * spatialTranslate k h q z‖ ≤ C) ∧
          (Continuous (fun z => β z * spatialDifferenceQuotient k h q z) ∧
            HasCompactSupport
              (fun z => β z * spatialDifferenceQuotient k h q z) ∧
            ∀ z, ‖β z * spatialDifferenceQuotient k h q z‖ ≤ C) := by
  obtain ⟨δ, D, hδ, hD, hδU, _, hmaps, hdq⟩ :=
    IsCompact.exists_spatialDifferenceQuotient_bound_of_contDiffOn_one hS hU hSU hq
  have hqcollar : ContinuousOn q (Metric.cthickening δ S) :=
    hq.continuousOn.mono hδU
  obtain ⟨Q, hQ⟩ := hS.cthickening.exists_bound_of_continuousOn hqcollar
  have hC : 0 ≤ max Q D := hD.trans (le_max_right _ _)
  refine ⟨δ, max Q D, hδ, hC, ?_⟩
  intro β hβ hβcompact hβS hβunit k h hh
  let W : Set (TimeVelocity d) := U ∩ (spatialShift k h) ⁻¹' U
  have hshiftcont : Continuous (spatialShift k h) := by
    change Continuous (fun z => z + (0, h • PDE.basisVec k))
    simpa only [Homeomorph.coe_addRight] using
      (Homeomorph.addRight ((0, h • PDE.basisVec k) : TimeVelocity d)).continuous
  have hW : IsOpen W := hU.inter (hshiftcont.isOpen_preimage U hU)
  have hβW : tsupport β ⊆ W := by
    intro z hz
    exact ⟨hSU (hβS hz), hmaps k h hh (hβS hz)⟩
  have hqW : ContinuousOn q W := hq.continuousOn.mono fun z hz => hz.1
  have htranslateW : ContinuousOn (spatialTranslate k h q) W := by
    change ContinuousOn (fun z => q (spatialShift k h z)) W
    exact hq.continuousOn.comp' hshiftcont.continuousOn fun z hz => hz.2
  have hdqW : ContinuousOn (spatialDifferenceQuotient k h q) W := by
    rw [show spatialDifferenceQuotient k h q =
      fun z => (spatialTranslate k h q z - q z) / h from rfl]
    exact (htranslateW.sub hqW).div_const h
  have htranslatebound : ∀ z ∈ tsupport β, ‖spatialTranslate k h q z‖ ≤ max Q D := by
    intro z hz
    have hshiftcollar : spatialShift k h z ∈ Metric.cthickening δ S :=
      Metric.mem_cthickening_of_dist_le (spatialShift k h z) z δ S (hβS hz)
        (by simpa only [dist_spatialShift] using hh)
    exact (hQ (spatialShift k h z) hshiftcollar).trans (le_max_left _ _)
  have hdqbound : ∀ z ∈ tsupport β, ‖spatialDifferenceQuotient k h q z‖ ≤ max Q D := by
    intro z hz
    rw [Real.norm_eq_abs]
    exact (hdq k h z hh (hβS hz)).trans (le_max_right _ _)
  constructor
  · simpa only [max_eq_left hC] using
      (HypoellipticAleksandrov.continuous_hasCompactSupport_norm_le_cutoff_mul hW
        hβ.continuousOn hβcompact hβW hβunit htranslateW htranslatebound)
  · simpa only [max_eq_left hC] using
      (HypoellipticAleksandrov.continuous_hasCompactSupport_norm_le_cutoff_mul hW
        hβ.continuousOn hβcompact hβW hβunit hdqW hdqbound)

end HypoellipticAleksandrov.Parabolic
