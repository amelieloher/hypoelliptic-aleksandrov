module

public import HypoellipticAleksandrov.Parabolic.SpatialDifferenceQuotientCollar

/-!
# Compact support for spatial difference quotients

This module proves the compact-support and topological-support facts needed to
use spatial difference quotients as raw parabolic tests.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

/-- Compact support is preserved by a spatial translation. -/
theorem HasCompactSupport.spatialTranslate
    {d : ℕ} {α : Type*} [Zero α] {k : Fin d} {h : ℝ}
    {f : TimeVelocity d → α} (hf : HasCompactSupport f) :
    HasCompactSupport (spatialTranslate k h f) := by
  have heq : HypoellipticAleksandrov.Parabolic.spatialTranslate k h f =
      f ∘ Homeomorph.addRight ((0, h • PDE.basisVec k) : TimeVelocity d) := by
    funext z
    exact congrArg f (show spatialShift k h z =
      Homeomorph.addRight ((0, h • PDE.basisVec k) : TimeVelocity d) z from rfl)
  rw [heq]
  exact hf.comp_homeomorph
    (Homeomorph.addRight ((0, h • PDE.basisVec k) : TimeVelocity d))

/-- Compact support is preserved by a spatial difference quotient. -/
theorem HasCompactSupport.spatialDifferenceQuotient
    {d : ℕ} {k : Fin d} {h : ℝ} {f : TimeVelocity d → ℝ}
    (hf : HasCompactSupport f) :
    HasCompactSupport (spatialDifferenceQuotient k h f) := by
  have htranslate : HasCompactSupport (HypoellipticAleksandrov.Parabolic.spatialTranslate k h f) :=
    HasCompactSupport.spatialTranslate hf
  have hsub : HasCompactSupport (HypoellipticAleksandrov.Parabolic.spatialTranslate k h f - f) :=
    htranslate.sub hf
  have hquotient : HypoellipticAleksandrov.Parabolic.spatialDifferenceQuotient k h f =
      h⁻¹ • (HypoellipticAleksandrov.Parabolic.spatialTranslate k h f - f) := by
    funext z
    simp only [spatialDifferenceQuotient_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [div_eq_mul_inv, mul_comm]
  rw [hquotient]
  exact hsub.smul_left

/-- The quotient support lies in the union of the translated and original supports. -/
theorem tsupport_spatialDifferenceQuotient_subset
    {d : ℕ} (k : Fin d) (h : ℝ) (f : TimeVelocity d → ℝ) :
    tsupport (spatialDifferenceQuotient k h f) ⊆
      tsupport (spatialTranslate k h f) ∪ tsupport f := by
  have hquotient : spatialDifferenceQuotient k h f =
      h⁻¹ • (spatialTranslate k h f - f) := by
    funext z
    simp only [spatialDifferenceQuotient_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [div_eq_mul_inv, mul_comm]
  rw [hquotient]
  exact (tsupport_smul_subset_right (fun _ : TimeVelocity d => h⁻¹)
    (spatialTranslate k h f - f)).trans (tsupport_sub _ _)

/-- A quotient is supported in `U` when the original carrier lies in `U` and
the corresponding backward shift maps that carrier into `U`. -/
theorem tsupport_spatialDifferenceQuotient_subset_of_mapsTo_spatialShift_neg
    {d : ℕ} {K U : Set (TimeVelocity d)}
    (k : Fin d) (h : ℝ) (f : TimeVelocity d → ℝ)
    (hfK : tsupport f ⊆ K) (hKU : K ⊆ U)
    (hshift : Set.MapsTo (spatialShift k (-h)) K U) :
    tsupport (spatialDifferenceQuotient k h f) ⊆ U := by
  intro z hz
  rcases tsupport_spatialDifferenceQuotient_subset k h f hz with hz | hz
  · exact tsupport_spatialTranslate_subset_of_mapsTo_spatialShift_neg k h f hfK hshift hz
  · exact hKU (hfK hz)

end HypoellipticAleksandrov.Parabolic
