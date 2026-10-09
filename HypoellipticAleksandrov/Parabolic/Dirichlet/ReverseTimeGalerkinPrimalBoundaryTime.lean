module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinPrimalBase

/-!
# Boundary-time identity for a finite reverse-time Galerkin curve

This file keeps the finite Galerkin calculation at the raw Sobolev level.  In
particular, its endpoint is the actual finite initial projection, rather than
an endpoint value of a quotient-valued limiting curve.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open MeasureTheory Set
open scoped ENNReal Matrix Matrix.Norms.Elementwise MatrixOrder RealInnerProductSpace

private theorem hasDerivWithinAt_boundary_pairing
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (N : ℕ)
    (x : ℝ → Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ)
    (xdot : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ)
    (v : galerkinSpace hΩ N) {s : Set ℝ} {τ : ℝ}
    (hx : HasDerivWithinAt x xdot s τ) :
    HasDerivWithinAt
      (fun t =>
        inner ℝ (valueCLM hΩ (v : H10HilbertGraph hΩ))
          (valueCLM hΩ
            (galerkinReconstruct hΩ N (x t) : H10HilbertGraph hΩ)))
      (inner ℝ (valueCLM hΩ (v : H10HilbertGraph hΩ))
        (valueCLM hΩ
          (galerkinReconstruct hΩ N xdot : H10HilbertGraph hΩ))) s τ := by
  let R : (Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) →L[ℝ]
      H10HilbertGraph hΩ :=
    (galerkinSpace hΩ N).subtypeL.comp
      (LinearMap.toContinuousLinearMap (galerkinReconstruct hΩ N))
  let V : (Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) →L[ℝ]
      PDE.ScalarLp Ω (2 : ℝ≥0∞) :=
    (valueCLM hΩ).comp R
  let I : PDE.ScalarLp Ω (2 : ℝ≥0∞) →L[ℝ] ℝ :=
    innerSL ℝ (valueCLM hΩ (v : H10HilbertGraph hΩ))
  have hV := (V.hasFDerivAt).comp_hasDerivWithinAt τ hx
  have hI := (I.hasFDerivAt).comp_hasDerivWithinAt τ hV
  simpa only [I, V, R, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_coe,
    Submodule.subtypeL_apply, innerSL_apply_apply, Function.comp_def,
    LinearMap.coe_toContinuousLinearMap'] using hI

private theorem continuousOn_boundary_pairing
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (N : ℕ)
    (x : ℝ → Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ)
    (v : galerkinSpace hΩ N) (s : Set ℝ) (hx : ContinuousOn x s) :
    ContinuousOn
      (fun t =>
        inner ℝ (valueCLM hΩ (v : H10HilbertGraph hΩ))
          (valueCLM hΩ
            (galerkinReconstruct hΩ N (x t) : H10HilbertGraph hΩ))) s := by
  let R : (Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) →L[ℝ]
      H10HilbertGraph hΩ :=
    (galerkinSpace hΩ N).subtypeL.comp
      (LinearMap.toContinuousLinearMap (galerkinReconstruct hΩ N))
  let V : (Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) →L[ℝ]
      PDE.ScalarLp Ω (2 : ℝ≥0∞) :=
    (valueCLM hΩ).comp R
  let I : PDE.ScalarLp Ω (2 : ℝ≥0∞) →L[ℝ] ℝ :=
    innerSL ℝ (valueCLM hΩ (v : H10HilbertGraph hΩ))
  have hV : ContinuousOn (fun t => V (x t)) s :=
    V.continuous.continuousOn.comp hx fun _ _ => Set.mem_univ _
  simpa only [I, V, R, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_coe,
    Submodule.subtypeL_apply, innerSL_apply_apply, Function.comp_def,
    LinearMap.coe_toContinuousLinearMap'] using
    I.continuous.continuousOn.comp hV fun _ _ => Set.mem_univ _

private theorem continuousOn_boundary_reconstruct
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (N : ℕ)
    (x : ℝ → Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ)
    (s : Set ℝ) (hx : ContinuousOn x s) :
    ContinuousOn
      (fun t => (galerkinReconstruct hΩ N (x t) : H10HilbertGraph hΩ)) s := by
  let R : (Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) →L[ℝ]
      H10HilbertGraph hΩ :=
    (galerkinSpace hΩ N).subtypeL.comp
      (LinearMap.toContinuousLinearMap (galerkinReconstruct hΩ N))
  have hR : ContinuousOn (fun t => R (x t)) s :=
    R.continuous.continuousOn.comp hx fun _ _ => Set.mem_univ _
  simpa only [R, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_coe,
    Submodule.subtypeL_apply, LinearMap.coe_toContinuousLinearMap'] using hR

private theorem boundaryTime_scalar_identity
    (T : ℝ) (hT : 0 < T) (pairing residual eta etaDeriv : ℝ → ℝ)
    (hpairing : ContinuousOn pairing (Icc 0 T))
    (hresidual : IntegrableOn residual (Icc 0 T) volume)
    (hderivPairing : ∀ τ ∈ Icc 0 T,
      HasDerivWithinAt pairing (residual τ) (Icc 0 T) τ)
    (hEta : ∀ τ ∈ Icc 0 T,
      HasDerivWithinAt eta (etaDeriv τ) (Icc 0 T) τ)
    (hDerivCont : ContinuousOn etaDeriv (Icc 0 T))
    (hEtaT : eta T = 0) :
    Integrable (fun τ => pairing τ * etaDeriv τ) (reverseTimeVolume T) ∧
    Integrable (fun τ => residual τ * eta τ) (reverseTimeVolume T) ∧
    (∫ τ, pairing τ * etaDeriv τ ∂reverseTimeVolume T) =
      -(∫ τ, residual τ * eta τ ∂reverseTimeVolume T) - pairing 0 * eta 0 := by
  have hEtaCont : ContinuousOn eta (Icc 0 T) := fun τ hτ =>
    (hEta τ hτ).continuousWithinAt
  have hresidualInterval : IntervalIntegrable residual volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hT.le).mpr hresidual
  have hderivInterval : IntervalIntegrable etaDeriv volume 0 T :=
    hDerivCont.intervalIntegrable_of_Icc hT.le
  have hinterval := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt
    (a := 0) (b := T) (u := pairing) (u' := residual) (v := eta) (v' := etaDeriv)
    (by rw [uIcc_of_le hT.le]; exact hderivPairing)
    (by rw [uIcc_of_le hT.le]; exact hEta) hresidualInterval hderivInterval
  have hintervalBoundary : (∫ τ in 0..T, pairing τ * etaDeriv τ) =
      -(∫ τ in 0..T, residual τ * eta τ) - pairing 0 * eta 0 := by
    calc
      (∫ τ in 0..T, pairing τ * etaDeriv τ) =
          pairing T * eta T - pairing 0 * eta 0 - ∫ τ in 0..T, residual τ * eta τ :=
        hinterval
      _ = -(∫ τ in 0..T, residual τ * eta τ) - pairing 0 * eta 0 := by
        rw [hEtaT]
        ring
  have hleftIcc : IntegrableOn (fun τ => pairing τ * etaDeriv τ) (Icc 0 T) volume :=
    (hpairing.mul hDerivCont).integrableOn_Icc
  have hEtaBounded : Bornology.IsBounded (eta '' Icc 0 T) :=
    (isCompact_Icc.image_of_continuousOn hEtaCont).isBounded
  obtain ⟨C, hC⟩ := hEtaBounded.exists_norm_le
  have hrightIcc : IntegrableOn (fun τ => residual τ * eta τ) (Icc 0 T) volume := by
    apply hresidual.mul_bdd (hEtaCont.aestronglyMeasurable measurableSet_Icc)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
    exact hC (eta τ) ⟨τ, hτ, rfl⟩
  have hleft : Integrable (fun τ => pairing τ * etaDeriv τ) (reverseTimeVolume T) := by
    simpa only [reverseTimeVolume, reverseTimeOpenInterval, restrict_Ioo_eq_restrict_Icc,
      IntegrableOn]
      using hleftIcc
  have hright : Integrable (fun τ => residual τ * eta τ) (reverseTimeVolume T) := by
    simpa only [reverseTimeVolume, reverseTimeOpenInterval, restrict_Ioo_eq_restrict_Icc,
      IntegrableOn]
      using hrightIcc
  have hboundary : (∫ τ, pairing τ * etaDeriv τ ∂reverseTimeVolume T) =
      -(∫ τ, residual τ * eta τ ∂reverseTimeVolume T) - pairing 0 * eta 0 := by
    simpa only [reverseTimeVolume, reverseTimeOpenInterval, restrict_Ioo_eq_restrict_Icc,
      restrict_Ioc_eq_restrict_Icc, intervalIntegral.integral_of_le hT.le]
      using hintervalBoundary
  exact ⟨hleft, hright, hboundary⟩

/-- The selected finite reverse-time Galerkin raw curve obeys the terminal-zero
boundary-time identity, including its initial projected datum. -/
theorem reverseTimeGalerkinPrimal_boundaryTime
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ lam : ℝ) (h₀₁ : r₀ < r₁) (hlam : 0 < lam)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c F : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hFSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hLower : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
        lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
    (hcNonpos : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → c z.1 z.2 ≤ 0)
    (N : ℕ) (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (v : galerkinSpace hΩ N)
    (eta etaDeriv : ℝ → ℝ)
    (hEta : ∀ tau ∈ Set.Icc 0 (r₁ - r₀),
      HasDerivWithinAt eta (etaDeriv tau) (Set.Icc 0 (r₁ - r₀)) tau)
    (hDerivCont : ContinuousOn etaDeriv (Set.Icc 0 (r₁ - r₀)))
    (hEtaT : eta (r₁ - r₀) = 0) :
    MeasureTheory.Integrable
      (fun tau =>
        inner ℝ (valueCLM hΩ (v : H10HilbertGraph hΩ))
          (valueCLM hΩ
            (reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
              haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial tau)) *
          etaDeriv tau)
      (reverseTimeVolume (r₁ - r₀)) ∧
    MeasureTheory.Integrable
      (fun tau =>
        (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau
            (v : H10HilbertGraph hΩ) -
          reverseTimeSpatialForm hΩ r₁ tau a b c
            (reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
              haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial tau)
            (v : H10HilbertGraph hΩ)) * eta tau)
      (reverseTimeVolume (r₁ - r₀)) ∧
    (∫ tau,
      inner ℝ (valueCLM hΩ (v : H10HilbertGraph hΩ))
        (valueCLM hΩ
          (reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
            haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial tau)) *
        etaDeriv tau ∂reverseTimeVolume (r₁ - r₀)) =
      -(∫ tau,
        (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau
            (v : H10HilbertGraph hΩ) -
          reverseTimeSpatialForm hΩ r₁ tau a b c
            (reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
              haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial tau)
            (v : H10HilbertGraph hΩ)) * eta tau
        ∂reverseTimeVolume (r₁ - r₀)) -
      inner ℝ (valueCLM hΩ (v : H10HilbertGraph hΩ))
        (valueCLM hΩ (galerkinInitialProjection hΩ N initial :
          H10HilbertGraph hΩ)) * eta 0 := by
  let selected :=
    ((exists_reverseTimeGalerkin_uniform_energy_solution r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos).choose_spec.2).choose_spec.2
      N initial
  let curveSpec := selected.choose_spec
  have hspec := curveSpec.choose_spec
  let x := reverseTimeGalerkinPrimalCoordinate r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
    a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial
  let T : ℝ := r₁ - r₀
  have hT : 0 ≤ T := sub_nonneg.mpr h₀₁.le
  let A : ℝ → (Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) →L[ℝ]
      (Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) := fun τ =>
    reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth N (Set.projIcc 0 T hT τ)
  let f : ℝ → Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ := fun τ =>
    reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N
      (Set.projIcc 0 T hT τ)
  let xdot : ℝ → Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ := fun τ =>
    A τ (x τ) + f τ
  have hx : ContinuousOn x (Icc 0 T) := by
    simpa only [x, T, reverseTimeGalerkinPrimalCoordinate] using hspec.2.2.1
  have hxdot : ContinuousOn xdot (Icc 0 T) := by
    have hA : Continuous A :=
      (continuous_reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth N).comp continuous_projIcc
    have hf : Continuous f :=
      (continuous_reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N).comp
        continuous_projIcc
    exact (hA.continuousOn.clm_apply hx).add hf.continuousOn
  have hderiv : ∀ τ ∈ Icc 0 T,
      HasDerivWithinAt x (xdot τ) (Icc 0 T) τ := by
    intro τ hτ
    let τ' : Icc 0 (r₁ - r₀) := ⟨τ, by simpa only [T] using hτ⟩
    have hproj : Set.projIcc 0 T hT τ = τ' := Set.projIcc_of_mem hT hτ
    simpa only [x, xdot, A, f, T, hproj, reverseTimeGalerkinPrimalCoordinate] using
      (hspec.2.2.2.2.1 τ').1
  have hrows : ∀ τ : Icc 0 T,
      ∀ i : Fin (Module.finrank ℝ (galerkinSpace hΩ N)),
        inner ℝ
            (valueCLM hΩ (galerkinReconstruct hΩ N (xdot τ.1) :
              H10HilbertGraph hΩ))
            (valueCLM hΩ (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ)) +
          reverseTimeSpatialForm hΩ r₁ τ.1 a b c
            (galerkinReconstruct hΩ N (x τ.1) : H10HilbertGraph hΩ)
            (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) =
          reverseTimeGalerkinSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N
            ⟨τ.1, by simpa only [T] using τ.2⟩ i := by
    intro τ i
    let τ' : Icc 0 (r₁ - r₀) := ⟨τ.1, by simpa only [T] using τ.2⟩
    have hproj : Set.projIcc 0 T hT τ.1 = τ' := Set.projIcc_of_mem hT τ.2
    have hu := hspec.2.1
    simpa only [x, xdot, A, f, T, hproj, reverseTimeGalerkinPrimalCoordinate, hu] using
      (hspec.2.2.2.2.1 τ').2 i
  let pairing : ℝ → ℝ := fun τ =>
    inner ℝ (valueCLM hΩ (v : H10HilbertGraph hΩ))
      (valueCLM hΩ (galerkinReconstruct hΩ N (x τ) : H10HilbertGraph hΩ))
  let residual : ℝ → ℝ := fun τ =>
    reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ
      (v : H10HilbertGraph hΩ) -
    reverseTimeSpatialForm hΩ r₁ τ a b c
      (galerkinReconstruct hΩ N (x τ) : H10HilbertGraph hΩ)
      (v : H10HilbertGraph hΩ)
  let clampedResidual : ℝ → ℝ := fun τ =>
    reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ
      (v : H10HilbertGraph hΩ) -
    reverseTimeSpatialFormOperatorClamp r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth τ
      (galerkinReconstruct hΩ N (x τ) : H10HilbertGraph hΩ)
      (v : H10HilbertGraph hΩ)
  have hTpos : 0 < T := by dsimp only [T]; linarith
  have hpairing : ContinuousOn pairing (Icc 0 T) := by
    simpa only [pairing] using continuousOn_boundary_pairing hΩ N x v (Icc 0 T) hx
  have hrec : ContinuousOn
      (fun τ => (galerkinReconstruct hΩ N (x τ) : H10HilbertGraph hΩ)) (Icc 0 T) :=
    continuousOn_boundary_reconstruct hΩ N x (Icc 0 T) hx
  have hsource : Continuous
      (fun τ => reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ
        (v : H10HilbertGraph hΩ)) :=
    (continuous_reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth).clm_apply
      continuous_const
  have hclampedForm : ContinuousOn
      (fun τ => reverseTimeSpatialFormOperatorClamp r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth τ
        (galerkinReconstruct hΩ N (x τ) : H10HilbertGraph hΩ)
        (v : H10HilbertGraph hΩ)) (Icc 0 T) :=
    ((continuous_reverseTimeSpatialFormOperatorClamp r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth).continuousOn.clm_apply hrec).clm_apply
      continuous_const.continuousOn
  have hclampedResidual : ContinuousOn clampedResidual (Icc 0 T) := by
    simpa only [clampedResidual, Pi.sub_def] using hsource.continuousOn.sub hclampedForm
  have hformAE : ∀ᵐ τ ∂volume.restrict (Icc 0 T),
      reverseTimeSpatialFormOperatorClamp r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth τ
        (galerkinReconstruct hΩ N (x τ) : H10HilbertGraph hΩ)
        (v : H10HilbertGraph hΩ) =
      reverseTimeSpatialForm hΩ r₁ τ a b c
        (galerkinReconstruct hΩ N (x τ) : H10HilbertGraph hΩ)
        (v : H10HilbertGraph hΩ) := by
    have hformAEall : ∀ᵐ τ ∂volume.restrict (Icc 0 T), ∀ u v : H10HilbertGraph hΩ,
        reverseTimeSpatialFormOperatorClamp r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth τ u v =
        reverseTimeSpatialForm hΩ r₁ τ a b c u v := by
      simpa only [T, reverseTimeVolume, reverseTimeOpenInterval, restrict_Ioo_eq_restrict_Icc]
        using ae_reverseTimeSpatialFormOperatorClamp_apply r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth
    filter_upwards [hformAEall] with τ hτ
    exact hτ _ _
  have hresidualIcc : IntegrableOn residual (Icc 0 T) volume := by
    apply Integrable.congr hclampedResidual.integrableOn_Icc
    filter_upwards [hformAE] with τ hτ
    dsimp only [residual, clampedResidual]
    exact congrArg
      (fun z : ℝ => reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ
        (v : H10HilbertGraph hΩ) - z) hτ
  have hderivPairing : ∀ τ ∈ Icc 0 T,
      HasDerivWithinAt pairing (residual τ) (Icc 0 T) τ := by
    intro τ hτ
    have hfixed := hasDerivWithinAt_boundary_pairing hΩ N x (xdot τ) v (hderiv τ hτ)
    let τT : Icc 0 T := ⟨τ, hτ⟩
    let τ' : Icc 0 (r₁ - r₀) := ⟨τ, by simpa only [T] using hτ⟩
    have hrow := reverseTimeGalerkin_basisRows_forall r₀ r₁ h₀₁ hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth N τ' (x τ) (xdot τ) (hrows τT) v
    have hrate :
        inner ℝ (valueCLM hΩ (v : H10HilbertGraph hΩ))
          (valueCLM hΩ (galerkinReconstruct hΩ N (xdot τ) : H10HilbertGraph hΩ)) =
        residual τ := by
      rw [real_inner_comm]
      dsimp only [residual]
      linarith
    rw [← hrate]
    simpa only [pairing] using hfixed
  have hscalar := boundaryTime_scalar_identity T hTpos pairing residual eta etaDeriv hpairing
    hresidualIcc hderivPairing (by simpa only [T] using hEta)
    (by simpa only [T] using hDerivCont) (by simpa only [T] using hEtaT)
  have hpairingZero : pairing 0 =
      inner ℝ (valueCLM hΩ (v : H10HilbertGraph hΩ))
        (valueCLM hΩ (galerkinInitialProjection hΩ N initial : H10HilbertGraph hΩ)) := by
    simpa only [pairing, reverseTimeGalerkinPrimalRaw, x] using congrArg
      (fun w : H10HilbertGraph hΩ =>
        inner ℝ (valueCLM hΩ (v : H10HilbertGraph hΩ)) (valueCLM hΩ w))
      (reverseTimeGalerkinPrimalRaw_zero r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
        haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial)
  rw [hpairingZero] at hscalar
  simpa only [reverseTimeGalerkinPrimalRaw, x, pairing, residual, T] using hscalar

/-- A fixed lower Galerkin test pairs the higher initial projection exactly as
it pairs the original spatial initial datum. -/
theorem inner_value_galerkinInitialProjection_eq
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) {M N : ℕ} (hMN : M ≤ N)
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (v : galerkinSpace hΩ M) :
    inner ℝ (valueCLM hΩ (v : H10HilbertGraph hΩ))
      (valueCLM hΩ (galerkinInitialProjection hΩ N initial :
        H10HilbertGraph hΩ)) =
      inner ℝ (valueCLM hΩ (v : H10HilbertGraph hΩ)) initial := by
  let K := galerkinValueSpace hΩ N
  have hvN : (v : H10HilbertGraph hΩ) ∈ galerkinSpace hΩ N :=
    galerkinSpace_mono hΩ hMN v.property
  let u : K := ⟨valueCLM hΩ (v : H10HilbertGraph hΩ), ⟨v, hvN, rfl⟩⟩
  rw [value_galerkinInitialProjection]
  change inner ℝ (u : PDE.ScalarLp Ω (2 : ℝ≥0∞)) (K.orthogonalProjection initial) =
    inner ℝ (u : PDE.ScalarLp Ω (2 : ℝ≥0∞)) initial
  exact Submodule.inner_orthogonalProjection_eq_of_mem_left u initial

end HypoellipticAleksandrov.Parabolic.Dirichlet
