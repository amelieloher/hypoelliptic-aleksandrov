module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonLocalSpatialSlices
public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonLocalSpatialIntegrability
import HypoellipticAleksandrov.Measure.TimeVelocity
import Mathlib.MeasureTheory.Integral.Prod

/-! # Spacetime spatial value-energy identity

Fubini integrates the exact classical slice identity. Compact support supplies all
integrability needed before exchanging the spatial and temporal integrals.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open MeasureTheory Set
open scoped Matrix.Norms.Elementwise

/-- The spatial value-energy identity holds on the literal product-volume cylinder. -/
theorem integral_scalar_local_spatial_value_energy_spacetime {d : ℕ}
    (a T : ℝ) (O : Set (PDE.Vec d)) (hO : IsOpen O)
    (u ρ : TimeVelocity d → ℝ) (hu : IsScalarC12On u (Ioo a T ×ˢ O))
    (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hc : HasCompactSupport ρ)
    (hsub : tsupport ρ ⊆ Ioo a T ×ˢ O)
    (A : CoefficientField d) (hA : IsSmoothCoefficient A) (i j : Fin d) :
    (∫ z in Ioo a T ×ˢ O, A z.1 z.2 i j * scalarSpatialGradient u z j *
      (ρ z ^ 2 * scalarSpatialGradient u z i +
        2 * ρ z * scalarSpatialGradient ρ z i * u z)) =
    -(∫ z in Ioo a T ×ˢ O,
      (spatialPartial i (fun y => A z.1 y i j) z.2 * scalarSpatialGradient u z j +
        A z.1 z.2 i j * scalarSpatialHessian u z i j) * (u z * ρ z ^ 2)) := by
  let left : TimeVelocity d → ℝ := fun z =>
    A z.1 z.2 i j * scalarSpatialGradient u z j *
      (ρ z ^ 2 * scalarSpatialGradient u z i +
        2 * ρ z * scalarSpatialGradient ρ z i * u z)
  let right : TimeVelocity d → ℝ := fun z =>
    (spatialPartial i (fun y => A z.1 y i j) z.2 * scalarSpatialGradient u z j +
      A z.1 z.2 i j * scalarSpatialHessian u z i j) * (u z * ρ z ^ 2)
  have hint := integrable_scalar_local_spatial_value_energy_terms (isOpen_Ioo.prod hO)
    u ρ hu hρ hc hsub A hA i j
  have hprod : (volume.restrict (Ioo a T)).prod (volume.restrict O) =
      volume.restrict (Ioo a T ×ˢ O : Set (TimeVelocity d)) := by
    rw [volume_timeVelocity_eq_prod]
    exact Measure.prod_restrict (Ioo a T) O
  have hl : Integrable left ((volume.restrict (Ioo a T)).prod (volume.restrict O)) := by
    rw [hprod]
    exact hint.1.restrict
  have hr : Integrable right ((volume.restrict (Ioo a T)).prod (volume.restrict O)) := by
    rw [hprod]
    exact hint.2.restrict
  change (∫ z in Ioo a T ×ˢ O, left z) = -(∫ z in Ioo a T ×ˢ O, right z)
  rw [← hprod, integral_prod left hl, integral_prod right hr, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have hcoeff : ContDiff ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => A z.1 z.2 i j) :=
    (contDiff_apply ℝ ℝ j).comp ((contDiff_apply ℝ (Fin d → ℝ) i).comp hA)
  have hslice : ContDiffOn ℝ 1 (fun y => A t y i j) O :=
    ((hcoeff.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)).contDiffOn
  exact integral_scalar_local_spatial_value_energy_slice a T O hO u ρ hu hρ hc hsub
    A t ht i j hslice

end HypoellipticAleksandrov.Parabolic.LocalHolder
