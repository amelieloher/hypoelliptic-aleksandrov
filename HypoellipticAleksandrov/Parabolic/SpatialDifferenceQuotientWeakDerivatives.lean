module

public import HypoellipticAleksandrov.Parabolic.SpatialTranslationLocalIntegrability
public import HypoellipticAleksandrov.Parabolic.WeakDerivativesAlgebra

/-!
# Weak derivatives of spatial difference quotients

This module combines raw spatial translation, local-integrability transport,
restriction, and weak-derivative algebra on arbitrary time--velocity sets.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory

/-- Weak time differentiation commutes with a spatial difference quotient on
a domain supporting both the original and translated relations. -/
theorem HasWeakTimeDerivOn.spatialDifferenceQuotient_of_subset_mapsTo
    {d : ℕ} {U V : Set (TimeVelocity d)}
    {u du : TimeVelocity d → ℝ}
    (hu : HasWeakTimeDerivOn U u du)
    (huLoc : LocallyIntegrableOn u U volume)
    (hduLoc : LocallyIntegrableOn du U volume)
    (k : Fin d) (h : ℝ)
    (hVU : V ⊆ U)
    (hshift : Set.MapsTo (spatialShift k h) V U) :
    HasWeakTimeDerivOn V
      (spatialDifferenceQuotient k h u)
      (spatialDifferenceQuotient k h du) := by
  have htranslated := hu.spatialTranslate_of_mapsTo k h hshift
  have horiginal := hu.restrict hVU
  have huTranslatedLoc :=
    LocallyIntegrableOn.spatialTranslate_of_mapsTo huLoc k h hshift
  have hduTranslatedLoc :=
    LocallyIntegrableOn.spatialTranslate_of_mapsTo hduLoc k h hshift
  have huOriginalLoc := huLoc.mono_set hVU
  have hduOriginalLoc := hduLoc.mono_set hVU
  have hsub := htranslated.sub horiginal huTranslatedLoc hduTranslatedLoc
    huOriginalLoc hduOriginalLoc
  have hsmul := hsub.smul h⁻¹
  convert hsmul using 1 <;> ext z <;>
    simp only [spatialDifferenceQuotient_apply, Pi.smul_apply, smul_eq_mul,
      div_eq_mul_inv] <;> ring

/-- A weak velocity derivative commutes with a spatial difference quotient
on a domain supporting both the original and translated relations. -/
theorem HasWeakVelocityPartialDerivOn.spatialDifferenceQuotient_of_subset_mapsTo
    {d : ℕ} {U V : Set (TimeVelocity d)} {i : Fin d}
    {u dui : TimeVelocity d → ℝ}
    (hu : HasWeakVelocityPartialDerivOn U i u dui)
    (huLoc : LocallyIntegrableOn u U volume)
    (hduiLoc : LocallyIntegrableOn dui U volume)
    (k : Fin d) (h : ℝ)
    (hVU : V ⊆ U)
    (hshift : Set.MapsTo (spatialShift k h) V U) :
    HasWeakVelocityPartialDerivOn V i
      (spatialDifferenceQuotient k h u)
      (spatialDifferenceQuotient k h dui) := by
  have htranslated := hu.spatialTranslate_of_mapsTo k h hshift
  have horiginal := hu.restrict hVU
  have huTranslatedLoc :=
    LocallyIntegrableOn.spatialTranslate_of_mapsTo huLoc k h hshift
  have hduiTranslatedLoc :=
    LocallyIntegrableOn.spatialTranslate_of_mapsTo hduiLoc k h hshift
  have huOriginalLoc := huLoc.mono_set hVU
  have hduiOriginalLoc := hduiLoc.mono_set hVU
  have hsub := htranslated.sub horiginal huTranslatedLoc hduiTranslatedLoc
    huOriginalLoc hduiOriginalLoc
  have hsmul := hsub.smul h⁻¹
  convert hsmul using 1 <;> ext z <;>
    simp only [spatialDifferenceQuotient_apply, Pi.smul_apply, smul_eq_mul,
      div_eq_mul_inv] <;> ring

end HypoellipticAleksandrov.Parabolic
