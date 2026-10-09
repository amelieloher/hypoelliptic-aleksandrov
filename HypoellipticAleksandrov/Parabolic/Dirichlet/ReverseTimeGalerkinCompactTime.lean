module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinWeakForm
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeTests
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Compactly supported time tests for finite reverse-time Galerkin curves

This module turns the finite Galerkin row equation into its scalar
compact-time identity.  It remains entirely finite dimensional in the spatial
test and does not construct a weak time derivative or a limiting solution.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open MeasureTheory Set
open scoped ENNReal Matrix Matrix.Norms.Elementwise MatrixOrder RealInnerProductSpace

private theorem hasDerivWithinAt_fixed_galerkin_pairing
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
        (valueCLM hΩ (galerkinReconstruct hΩ N xdot : H10HilbertGraph hΩ))) s τ := by
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

private theorem continuousOn_fixed_galerkin_pairing
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

private theorem continuousOn_galerkin_reconstruct
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

private theorem compactTime_scalar_identity
    (T : ℝ) (hT : 0 < T) (pairing residual : ℝ → ℝ)
    (hpairing : ContinuousOn pairing (Icc 0 T))
    (hresidual : IntegrableOn residual (Icc 0 T) volume)
    (hderivPairing : ∀ τ ∈ Icc 0 T,
      HasDerivWithinAt pairing (residual τ) (Icc 0 T) τ)
    (eta : ReverseTimeScalarTest T) :
    Integrable (fun τ => pairing τ * eta.deriv τ) (reverseTimeVolume T) ∧
    Integrable (fun τ => residual τ * eta τ) (reverseTimeVolume T) ∧
    (∫ τ, pairing τ * eta.deriv τ ∂reverseTimeVolume T) =
      -(∫ τ, residual τ * eta τ ∂reverseTimeVolume T) := by
  have hetaDeriv : ∀ τ ∈ Icc 0 T,
      HasDerivWithinAt (eta : ℝ → ℝ) (eta.deriv τ) (Icc 0 T) τ := by
    intro τ _
    rw [ReverseTimeScalarTest.deriv_apply]
    exact ((eta.contDiff.differentiable (by simp)).differentiableAt.hasDerivAt).hasDerivWithinAt
  have hpairingIntegrable : IntervalIntegrable residual volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hT.le).mpr hresidual
  have hetaIntegrable : IntervalIntegrable eta.deriv volume 0 T :=
    eta.contDiff_deriv.continuous.continuousOn.intervalIntegrable_of_Icc hT.le
  have heta0 : eta 0 = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hsupport
    have hmem := eta.tsupport_subset hsupport
    have hmem' : (0 : ℝ) < 0 ∧ 0 < T := by
      simpa only [reverseTimeOpenInterval, mem_Ioo] using hmem
    exact lt_irrefl 0 hmem'.1
  have hetaT : eta T = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hsupport
    have hmem := eta.tsupport_subset hsupport
    exact lt_irrefl T hmem.2
  have hinterval := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt
    (a := 0) (b := T) (u := pairing) (u' := residual) (v := eta) (v' := eta.deriv)
    (by rw [uIcc_of_le hT.le]; exact hderivPairing)
    (by rw [uIcc_of_le hT.le]; exact hetaDeriv) hpairingIntegrable hetaIntegrable
  have hintervalZero : (∫ τ in 0..T, pairing τ * eta.deriv τ) =
      -(∫ τ in 0..T, residual τ * eta τ) := by
    calc
      (∫ τ in 0..T, pairing τ * eta.deriv τ) =
          pairing T * eta T - pairing 0 * eta 0 - ∫ τ in 0..T, residual τ * eta τ := hinterval
      _ = -(∫ τ in 0..T, residual τ * eta τ) := by
        rw [heta0, hetaT]
        ring
  have hleftIcc : IntegrableOn (fun τ => pairing τ * eta.deriv τ) (Icc 0 T) volume :=
    (hpairing.mul eta.contDiff_deriv.continuous.continuousOn).integrableOn_Icc
  obtain ⟨C, hC⟩ := eta.exists_norm_le
  have hrightIcc : IntegrableOn (fun τ => residual τ * eta τ) (Icc 0 T) volume :=
    hresidual.mul_bdd eta.contDiff.continuous.aestronglyMeasurable (ae_of_all _ hC)
  have hleft : Integrable (fun τ => pairing τ * eta.deriv τ) (reverseTimeVolume T) := by
    simpa only [reverseTimeVolume, reverseTimeOpenInterval,
      restrict_Ioo_eq_restrict_Icc, IntegrableOn] using
      hleftIcc
  have hright : Integrable (fun τ => residual τ * eta τ) (reverseTimeVolume T) := by
    simpa only [reverseTimeVolume, reverseTimeOpenInterval,
      restrict_Ioo_eq_restrict_Icc, IntegrableOn] using
      hrightIcc
  have hcompact : (∫ τ, pairing τ * eta.deriv τ ∂reverseTimeVolume T) =
      -(∫ τ, residual τ * eta τ ∂reverseTimeVolume T) := by
    simpa only [reverseTimeVolume, reverseTimeOpenInterval, restrict_Ioo_eq_restrict_Icc,
      restrict_Ioc_eq_restrict_Icc,
      intervalIntegral.integral_of_le hT.le] using hintervalZero
  exact ⟨hleft, hright, hcompact⟩

/-- The finite Galerkin row equation yields the compactly supported scalar time identity. -/
theorem reverseTimeGalerkin_compactTime_identity_of_basisRows
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c F : ℝ → PDE.Vec d → ℝ)
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
    (N : ℕ)
    (x xdot : ℝ → Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ)
    (hx : ContinuousOn x (Set.Icc 0 (r₁ - r₀)))
    (hderiv : ∀ τ ∈ Set.Icc 0 (r₁ - r₀),
      HasDerivWithinAt x (xdot τ) (Set.Icc 0 (r₁ - r₀)) τ)
    (hrows : ∀ τ : Set.Icc 0 (r₁ - r₀),
      ∀ i : Fin (Module.finrank ℝ (galerkinSpace hΩ N)),
        inner ℝ
            (valueCLM hΩ (galerkinReconstruct hΩ N (xdot τ.1) :
              H10HilbertGraph hΩ))
            (valueCLM hΩ (galerkinSpaceBasis hΩ N i :
              H10HilbertGraph hΩ)) +
          reverseTimeSpatialForm hΩ r₁ τ.1 a b c
            (galerkinReconstruct hΩ N (x τ.1) : H10HilbertGraph hΩ)
            (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) =
          reverseTimeGalerkinSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ i)
    (v : galerkinSpace hΩ N)
    (eta : ReverseTimeScalarTest (r₁ - r₀)) :
    MeasureTheory.Integrable
      (fun τ =>
        inner ℝ (valueCLM hΩ (v : H10HilbertGraph hΩ))
          (valueCLM hΩ
            (galerkinReconstruct hΩ N (x τ) : H10HilbertGraph hΩ)) *
          eta.deriv τ)
      (reverseTimeVolume (r₁ - r₀)) ∧
    MeasureTheory.Integrable
      (fun τ =>
        (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ
            (v : H10HilbertGraph hΩ) -
          reverseTimeSpatialForm hΩ r₁ τ a b c
            (galerkinReconstruct hΩ N (x τ) : H10HilbertGraph hΩ)
            (v : H10HilbertGraph hΩ)) * eta τ)
      (reverseTimeVolume (r₁ - r₀)) ∧
    (∫ τ,
      inner ℝ (valueCLM hΩ (v : H10HilbertGraph hΩ))
        (valueCLM hΩ
          (galerkinReconstruct hΩ N (x τ) : H10HilbertGraph hΩ)) *
        eta.deriv τ ∂reverseTimeVolume (r₁ - r₀)) =
      -(∫ τ,
        (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ
            (v : H10HilbertGraph hΩ) -
          reverseTimeSpatialForm hΩ r₁ τ a b c
            (galerkinReconstruct hΩ N (x τ) : H10HilbertGraph hΩ)
            (v : H10HilbertGraph hΩ)) * eta τ
        ∂reverseTimeVolume (r₁ - r₀)) := by
  let T : ℝ := r₁ - r₀
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
  have hT : 0 < T := by
    dsimp only [T]
    linarith
  have hpairing : ContinuousOn pairing (Icc 0 T) := by
    simpa only [pairing, T] using continuousOn_fixed_galerkin_pairing hΩ N x v
      (Icc 0 (r₁ - r₀)) hx
  have hrec : ContinuousOn
      (fun τ => (galerkinReconstruct hΩ N (x τ) : H10HilbertGraph hΩ)) (Icc 0 T) := by
    simpa only [T] using continuousOn_galerkin_reconstruct hΩ N x (Icc 0 (r₁ - r₀)) hx
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
  have hclampedResidualIcc : IntegrableOn clampedResidual (Icc 0 T) volume :=
    hclampedResidual.integrableOn_Icc
  have hresidualIcc : IntegrableOn residual (Icc 0 T) volume := by
    apply Integrable.congr hclampedResidualIcc
    filter_upwards [hformAE] with τ hτ
    dsimp only [residual, clampedResidual]
    exact congrArg
      (fun z : ℝ => reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ
        (v : H10HilbertGraph hΩ) - z) hτ
  have hderivPairing : ∀ τ ∈ Icc 0 T,
      HasDerivWithinAt pairing (residual τ) (Icc 0 T) τ := by
    intro τ hτ
    have hfixed := hasDerivWithinAt_fixed_galerkin_pairing hΩ N x (xdot τ) v
      (hderiv τ (by simpa only [T] using hτ))
    have hrow := reverseTimeGalerkin_basisRows_forall r₀ r₁ h₀₁ hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth N ⟨τ, by simpa only [T] using hτ⟩
      (x τ) (xdot τ) (hrows ⟨τ, by simpa only [T] using hτ⟩) v
    have hrate :
        inner ℝ (valueCLM hΩ (v : H10HilbertGraph hΩ))
          (valueCLM hΩ (galerkinReconstruct hΩ N (xdot τ) : H10HilbertGraph hΩ)) =
        residual τ := by
      rw [real_inner_comm]
      dsimp only [residual, T]
      linarith
    rw [← hrate]
    simpa only [pairing] using hfixed
  exact compactTime_scalar_identity T hT pairing residual hpairing hresidualIcc
    hderivPairing eta

end HypoellipticAleksandrov.Parabolic.Dirichlet
