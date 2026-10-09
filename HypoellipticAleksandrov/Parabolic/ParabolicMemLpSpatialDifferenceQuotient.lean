module

public import HypoellipticAleksandrov.Parabolic.SpatialTranslationWeakDerivatives
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Restricted Lp membership under spatial quotients

This module transports restricted `Lᵖ` membership through spatial translations
and totalized spatial difference quotients at a fixed signed step.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped ENNReal

private theorem spatialShift_measurableEmbedding_for_memLp
    {d : ℕ} (k : Fin d) (h : ℝ) :
    MeasurableEmbedding (spatialShift k h) := by
  change MeasurableEmbedding (fun z : TimeVelocity d => z + (0, h • PDE.basisVec k))
  simpa only [Homeomorph.coe_addRight] using
    (Homeomorph.addRight
      ((0, h • PDE.basisVec k) : TimeVelocity d)).measurableEmbedding

/-- Restricted `Lᵖ` membership transports through a spatial translation from
a domain mapped into the original carrier. -/
theorem ParabolicMemLpOn.spatialTranslate_of_mapsTo
    {d : ℕ} {U V : Set (TimeVelocity d)}
    {p : ℝ≥0∞} {f : TimeVelocity d → ℝ}
    (hf : ParabolicMemLpOn U p f)
    (k : Fin d) (h : ℝ)
    (hshift : Set.MapsTo (spatialShift k h) V U) :
    ParabolicMemLpOn V p (spatialTranslate k h f) := by
  have hpre : MemLp (f ∘ spatialShift k h) p
      ((volume : Measure (TimeVelocity d)).restrict
        (spatialShift k h ⁻¹' U)) :=
    hf.comp_measurePreserving
      ((spatialShift_measurePreserving k h).restrict_preimage_emb
        (spatialShift_measurableEmbedding_for_memLp k h) U)
  have hsub : V ⊆ spatialShift k h ⁻¹' U := hshift
  exact hpre.mono_measure (Measure.restrict_mono_set volume hsub)

/-- Restricted `Lᵖ` membership transports to a totalized signed spatial
difference quotient on a shifted subdomain. -/
theorem ParabolicMemLpOn.spatialDifferenceQuotient_of_subset_mapsTo
    {d : ℕ} {U V : Set (TimeVelocity d)}
    {p : ℝ≥0∞} {f : TimeVelocity d → ℝ}
    (hf : ParabolicMemLpOn U p f)
    (k : Fin d) (h : ℝ)
    (hVU : V ⊆ U)
    (hshift : Set.MapsTo (spatialShift k h) V U) :
    ParabolicMemLpOn V p (spatialDifferenceQuotient k h f) := by
  have ht := hf.spatialTranslate_of_mapsTo k h hshift
  have ho := hf.mono_measure (Measure.restrict_mono_set volume hVU)
  have hs := ht.sub ho
  convert hs.const_smul h⁻¹ using 1
  funext z
  simp only [Pi.smul_apply, smul_eq_mul, spatialDifferenceQuotient_apply,
    Pi.sub_apply, div_eq_mul_inv]
  ring_nf

end HypoellipticAleksandrov.Parabolic
