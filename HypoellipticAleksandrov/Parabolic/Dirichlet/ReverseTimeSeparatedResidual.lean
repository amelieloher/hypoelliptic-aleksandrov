module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.VariationalEnergy
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGelfandPairing
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSourcePairing

/-!
# Reverse-time separated variational residual

This module records the separated-test residual supplied directly by the reverse-time
variational energy solution.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

private theorem integrable_reverseTimeNegativeSourceRaw_mul_test
    {d : ℕ} {Ω : Set (PDE.Vec d)} (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (F : ℝ → PDE.Vec d → ℝ)
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (eta : ReverseTimeScalarTest (r₁ - r₀)) (v : H10HilbertGraph hΩ) :
    Integrable
      (fun tau => reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau v * eta tau)
      (reverseTimeVolume (r₁ - r₀)) := by
  let S := reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth
  let z := reverseTimeSeparatedVTest hΩ eta v
  have hPair : Integrable (fun tau => S tau (z tau)) (reverseTimeVolume (r₁ - r₀)) :=
    integrable_reverseTimeDualPairing hΩ (r₁ - r₀) z S
  refine hPair.congr ?_
  filter_upwards
    [(memLp_reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth).coeFn_toLp,
      ae_reverseTimeSeparatedVTest hΩ eta v] with tau hS hz
  dsimp only [S, z]
  calc
    reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau
        (reverseTimeSeparatedVTest hΩ eta v tau) =
        reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau (eta tau • v) :=
      congrArg (reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau) hz
    _ = eta tau * reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau v := by
      rw [ContinuousLinearMap.map_smul]
      rfl
    _ = eta tau * reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau v :=
      congrArg (fun q => eta tau * q v) hS
    _ = reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau v * eta tau :=
      mul_comm _ _

private theorem integral_sub_add_eq_zero_of_pairing
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (mass form source dual : α → ℝ)
    (hmass : Integrable mass μ) (hform : Integrable form μ)
    (hsource : Integrable source μ)
    (hmassEq : (∫ x, mass x ∂μ) = -(∫ x, dual x ∂μ))
    (hformEq : (∫ x, form x ∂μ) = (∫ x, source x ∂μ) - ∫ x, dual x ∂μ) :
    (∫ x, mass x - form x + source x ∂μ) = 0 := by
  change (∫ x, (mass - form) x + source x ∂μ) = 0
  rw [integral_add (hmass.sub hform) hsource]
  change (∫ x, mass x - form x ∂μ) + ∫ x, source x ∂μ = 0
  rw [integral_sub hmass hform, hmassEq, hformEq]
  ring

/-- A reverse-time variational energy solution satisfies the separated-test residual identity. -/
theorem reverseTime_separated_residual_of_variationalEnergy
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c F : ℝ → PDE.Vec d → ℝ)
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (u : ReverseTimeL2V hΩ (r₁ - r₀))
    (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) u g)
    (hu : IsReverseTimeVariationalEnergySolution r₀ r₁ h₀₁ hΩ hΩbounded
      a b c F hFSmooth initial u g hdu)
    (eta : ReverseTimeScalarTest (r₁ - r₀))
    (v : H10HilbertGraph hΩ) :
    Integrable (fun tau =>
      inner ℝ (valueCLM hΩ v) (valueCLM hΩ (u tau)) * eta.deriv tau -
        reverseTimeSpatialForm hΩ r₁ tau a b c (u tau) v * eta tau +
        reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau v * eta tau)
      (reverseTimeVolume (r₁ - r₀)) ∧
    (∫ tau,
      inner ℝ (valueCLM hΩ v) (valueCLM hΩ (u tau)) * eta.deriv tau -
        reverseTimeSpatialForm hΩ r₁ tau a b c (u tau) v * eta tau +
        reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau v * eta tau
      ∂reverseTimeVolume (r₁ - r₀)) = 0 := by
  obtain ⟨hmassLift, hg, hmassLiftEq⟩ := hdu v eta
  have hmass : Integrable (fun tau =>
      inner ℝ (valueCLM hΩ v) (valueCLM hΩ (u tau)) * eta.deriv tau)
      (reverseTimeVolume (r₁ - r₀)) := by
    refine hmassLift.congr ?_
    filter_upwards [coeFn_reverseTimeValueCLM hΩ (r₁ - r₀) u] with tau huValue
    rw [huValue]
  have hmassEq : (∫ tau,
      inner ℝ (valueCLM hΩ v) (valueCLM hΩ (u tau)) * eta.deriv tau
      ∂reverseTimeVolume (r₁ - r₀)) =
      -(∫ tau, (g tau) v * eta tau ∂reverseTimeVolume (r₁ - r₀)) := by
    calc
      _ = ∫ tau,
          inner ℝ (valueCLM hΩ v) (reverseTimeValueCLM hΩ (r₁ - r₀) u tau) * eta.deriv tau
          ∂reverseTimeVolume (r₁ - r₀) := by
        apply integral_congr_ae
        filter_upwards [coeFn_reverseTimeValueCLM hΩ (r₁ - r₀) u] with tau huValue
        rw [huValue]
      _ = _ := hmassLiftEq
  have hsource := integrable_reverseTimeNegativeSourceRaw_mul_test r₀ r₁ h₀₁ hΩ hΩbounded F
    hFSmooth eta v
  have hformEq : ∀ᵐ tau ∂reverseTimeVolume (r₁ - r₀),
      reverseTimeSpatialForm hΩ r₁ tau a b c (u tau) v * eta tau =
        reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau v * eta tau -
          (g tau) v * eta tau := by
    filter_upwards [hu.2, ae_restrict_mem measurableSet_Ioo] with tau hEquation htau
    have hRaw : reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau =
        reverseTimeSourceFunctional hΩ
          (reverseTimeSourceSlice r₁ tau F
            (reverseTimeSourceSlice_memLp_of_smoothOnNeighborhood r₀ r₁ hΩ hΩbounded F hFSmooth
              tau ⟨le_of_lt htau.1, le_of_lt htau.2⟩)) :=
      reverseTimeNegativeSourceRaw_eq_sourceFunctional_of_mem_Icc r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth
        tau ⟨le_of_lt htau.1, le_of_lt htau.2⟩
    have hPoint := hEquation htau v
    rw [← hRaw] at hPoint
    calc
      reverseTimeSpatialForm hΩ r₁ tau a b c (u tau) v * eta tau =
          ((g tau) v + reverseTimeSpatialForm hΩ r₁ tau a b c (u tau) v - (g tau) v) * eta tau := by
            ring
      _ = (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau v -
          (g tau) v) * eta tau := by
            rw [hPoint]
      _ = _ := sub_mul _ _ _
  have hform : Integrable (fun tau =>
      reverseTimeSpatialForm hΩ r₁ tau a b c (u tau) v * eta tau)
      (reverseTimeVolume (r₁ - r₀)) :=
    (hsource.sub hg).congr (by
      filter_upwards [hformEq] with tau htau
      exact htau.symm)
  have hformEqIntegral : (∫ tau,
      reverseTimeSpatialForm hΩ r₁ tau a b c (u tau) v * eta tau
      ∂reverseTimeVolume (r₁ - r₀)) =
      (∫ tau, reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau v * eta tau
        ∂reverseTimeVolume (r₁ - r₀)) -
        ∫ tau, (g tau) v * eta tau ∂reverseTimeVolume (r₁ - r₀) := by
    calc
      _ = ∫ tau, reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau v * eta tau -
          (g tau) v * eta tau ∂reverseTimeVolume (r₁ - r₀) := integral_congr_ae hformEq
      _ = _ := integral_sub hsource hg
  constructor
  · exact (hmass.sub hform).add hsource
  · exact integral_sub_add_eq_zero_of_pairing (reverseTimeVolume (r₁ - r₀)) _ _ _ _
      hmass hform hsource hmassEq hformEqIntegral

end HypoellipticAleksandrov.Parabolic.Dirichlet
