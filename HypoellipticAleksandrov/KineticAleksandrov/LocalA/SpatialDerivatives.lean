module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.SpatialDerivativesReflection

/-! # The exact uniform spatial derivative theorem for smooth time-velocity coefficients -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory Parabolic SectionTwo

/-- Smooth time-velocity coefficients give all spatial derivatives with structural constants. -/
theorem smooth_timeVelocity_spatial_bounds
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    (d : ℕ) (hd : 1 ≤ d) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ C_m : ℕ → ℝ, (∀ m, 0 ≤ C_m m) ∧
      ∀ (A : CoefficientField d), IsSectionTwoCoefficient lam Lam A →
      ∀ (P₀ : KineticPoint d) (R : ℝ), 0 < R →
      ∀ (u : KineticPoint d → ℝ),
      ContinuousOn u (closure (backwardCylinder P₀ R)) →
      IsKineticC112On u (backwardCylinder P₀ R) →
      (∀ᵐ P ∂volume.restrict (backwardCylinder P₀ R),
        backwardOperatorOfTimeVelocityCoefficient A u P = 0) →
      (∀ P ∈ backwardCylinder P₀ R,
        ContDiffAt ℝ (⊤ : ℕ∞) (physicalPositionSlice u P) P.position) ∧
      ∀ (m : ℕ), 1 ≤ m → ∀ P ∈ backwardCylinder P₀ (3 * R / 4),
        R ^ (3 * m) * ‖iteratedFDeriv ℝ m (physicalPositionSlice u P) P.position‖ ≤
          C_m m * Holder.oscillationOn u (backwardCylinder P₀ R) := by
  obtain ⟨C, hC, hkernel⟩ :=
    spatialDensity_uniform_integral_bound hH hLE d hd lam Lam hlam hLam
  refine ⟨C, hC, ?_⟩
  intro A hA P₀ R hR u huc hus hue
  let B := kineticReflectedCoefficient A
  let U := u ∘ kineticReflection
  let Z₀ := kineticReflection P₀
  have hB : IsSectionTwoCoefficient lam Lam B := sectionTwo_coefficient_reflection hA
  obtain ⟨hUc, hUs, hUe⟩ := spatial_reflected_data A hA P₀ hR u huc hus hue
  refine ⟨?_, ?_⟩
  · intro P hP
    have hp : kineticReflection P ∈ forwardCylinder Z₀ R hR := by
      rw [← kineticReflection_image_backwardCylinder P₀ R hR]
      exact ⟨P, hP, rfl⟩
    have hs := spatial_forward_slice_smooth hH B hB Z₀ hR U hUs hUe
      (kineticReflection P) hp
    rw [spatial_slice_reflection]
    exact hs.comp P.position contDiffAt_id.neg
  · intro m hm P hP
    have hri : 0 < 3 * R / 4 := by positivity
    have hQi : kineticReflection P ∈ forwardCylinder Z₀ (3 * R / 4) hri := by
      rw [← kineticReflection_image_backwardCylinder P₀ (3 * R / 4) hri]
      exact ⟨P, hP, rfl⟩
    let Q := kineticReflection P
    have hQo := spatial_inner_subset_outer Z₀ hR hQi
    let p : LocalBallStart Z₀.velocity R := ⟨Q, hQo.2.2.1⟩
    let T : {t : ℝ // p.1.time < t} :=
      ⟨p.1.time + R ^ 2 / 8, by nlinarith only [sq_pos_of_pos hR]⟩
    have hT : T.1 - p.1.time = R ^ 2 / 8 := by dsimp only [T]; ring
    have hfb := spatial_forward_derivative_bound hH hLE hd hlam hLam B hB Z₀ hR
      U hUc hUs hUe p hQi T hT m hm
    have hki := hkernel B hB Z₀.velocity R hR p T hQi.2.2.1 hT m
    have hM : 0 ≤ Holder.oscillationOn U (forwardCylinder Z₀ R hR) :=
      (spatialData_local_extension Z₀ Q hR hQo U hUc).1
    have hbound := hfb.trans (mul_le_mul_of_nonneg_left hki hM)
    have hscale : R ^ (3 * m) * R ^ (-3 * (m : ℝ)) = 1 := by
      rw [← Real.rpow_natCast R (3 * m), ← Real.rpow_add hR]
      have he : ((3 * m : ℕ) : ℝ) + -3 * (m : ℝ) = 0 := by push_cast; ring
      rw [he, Real.rpow_zero]
    rw [spatial_derivative_norm_reflection]
    calc
      _ ≤ R ^ (3 * m) * (Holder.oscillationOn U (forwardCylinder Z₀ R hR) *
          (C m * R ^ (-3 * (m : ℝ)))) :=
        mul_le_mul_of_nonneg_left hbound (pow_nonneg hR.le _)
      _ = (C m * Holder.oscillationOn U (forwardCylinder Z₀ R hR)) *
          (R ^ (3 * m) * R ^ (-3 * (m : ℝ))) := by ring
      _ = C m * Holder.oscillationOn u (backwardCylinder P₀ R) := by
        rw [hscale, mul_one, spatial_oscillation_reflection P₀ hR u]

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
