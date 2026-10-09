module

public import HypoellipticAleksandrov.Parabolic.SpatialTranslationWeakDerivatives
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Local integrability under spatial translation

This module transports raw-set local integrability through native spatial
translations on domains mapped forward into the original domain.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory

/-- Raw-set local integrability transports through a spatial translation on
any domain sent into the original domain. -/
theorem LocallyIntegrableOn.spatialTranslate_of_mapsTo
    {d : ℕ} {U V : Set (TimeVelocity d)}
    {f : TimeVelocity d → ℝ}
    (hf : LocallyIntegrableOn f U volume) (k : Fin d) (h : ℝ)
    (hshift : Set.MapsTo (spatialShift k h) V U) :
    LocallyIntegrableOn (spatialTranslate k h f) V volume := by
  intro x hx
  rcases hf (spatialShift k h x) (hshift hx) with ⟨s, hs, hfs⟩
  refine ⟨spatialShift k h ⁻¹' s, ?_, ?_⟩
  · have hcontinuous : Continuous (spatialShift k h) := by
      change Continuous (fun z : TimeVelocity d => z + (0, h • PDE.basisVec k))
      simpa only [Homeomorph.coe_addRight] using
        (Homeomorph.addRight ((0, h • PDE.basisVec k) : TimeVelocity d)).continuous
    exact hcontinuous.continuousWithinAt.preimage_mem_nhdsWithin'
      (nhdsWithin_mono _ hshift.image_subset hs)
  · have hembed : MeasurableEmbedding (spatialShift k h) := by
      change MeasurableEmbedding (fun z : TimeVelocity d => z + (0, h • PDE.basisVec k))
      simpa only [Homeomorph.coe_addRight] using
        (Homeomorph.addRight ((0, h • PDE.basisVec k) : TimeVelocity d)).measurableEmbedding
    change IntegrableOn (fun z => f (spatialShift k h z)) (spatialShift k h ⁻¹' s) volume
    simpa only [Function.comp_def] using
      (spatialShift_measurePreserving k h).integrableOn_comp_preimage hembed |>.2 hfs

end HypoellipticAleksandrov.Parabolic
