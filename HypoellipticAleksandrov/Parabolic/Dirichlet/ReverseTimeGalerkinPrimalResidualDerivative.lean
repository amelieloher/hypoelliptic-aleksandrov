module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeFormResidual
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGelfandPairing
public import HypoellipticAleksandrov.Parabolic.Dirichlet.WeakTimeDerivative
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinPrimalArbitraryTestLimit

/-!
# Residual weak derivative of the reverse-time Galerkin limit

This module identifies the concrete Bochner residual as the Gelfand weak time
derivative of the common reverse-time Galerkin limit.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped ENNReal Matrix Matrix.Norms.Elementwise MatrixOrder RealInnerProductSpace

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

local instance instResidualDerivativeReverseTimeL2VStarModule
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) :
    Module ℝ (ReverseTimeL2VStar hΩ T) :=
  MeasureTheory.Lp.instModule

private theorem reverseTimeDualPairingRightCLM_sub
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ)
    (z : ReverseTimeL2V hΩ T) (g₁ g₂ : ReverseTimeL2VStar hΩ T) :
    reverseTimeDualPairingRightCLM hΩ T z (g₁ - g₂) =
      reverseTimeDualPairingRightCLM hΩ T z g₁ -
        reverseTimeDualPairingRightCLM hΩ T z g₂ :=
  (reverseTimeDualPairingRightCLM hΩ T z).map_sub g₁ g₂

private theorem reverseTimeDualPairingRightCLM_reverseTimeFormResidual
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
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
    (u : ReverseTimeL2V hΩ (r₁ - r₀))
    (z : ReverseTimeL2V hΩ (r₁ - r₀)) :
    reverseTimeDualPairingRightCLM hΩ (r₁ - r₀) z
        (reverseTimeFormResidual r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth F hFSmooth u) =
      reverseTimeDualPairingRightCLM hΩ (r₁ - r₀) z
        (reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth) -
      reverseTimeDualPairingRightCLM hΩ (r₁ - r₀) z
        (reverseTimeSpatialFormBochnerAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth u) := by
  rw [reverseTimeFormResidual]
  exact reverseTimeDualPairingRightCLM_sub hΩ (r₁ - r₀) z _ _

private theorem residual_pairing_algebra {m s a q : ℝ}
    (hm : m = -s + a) (hq : q = s - a) : m = -q := by
  linarith

variable {d : ℕ} {Ω : Set (PDE.Vec d)}
variable
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

/-- A common weak Galerkin subsequence converges to a curve whose Gelfand weak
time derivative is the concrete reverse-time form residual. -/
theorem exists_strictMono_tendsto_clm_reverseTimeGalerkinPrimal_residual_derivative
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    ∃ (U : ReverseTimeL2V hΩ (r₁ - r₀)) (φ : ℕ → ℕ),
      StrictMono φ ∧
      (∀ ell : ReverseTimeL2V hΩ (r₁ - r₀) →L[ℝ] ℝ,
        Tendsto
          (fun n => ell
            (reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
              a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos
              (φ n) initial))
          atTop (𝓝 (ell U))) ∧
      HasGelfandWeakTimeDerivative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) U
        (reverseTimeFormResidual r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth F hFSmooth U) := by
  obtain ⟨U, φ, hφ, hclm, hidentity⟩ :=
    exists_strictMono_tendsto_clm_reverseTimeGalerkinPrimal_arbitraryTests
      r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial
  let T := r₁ - r₀
  let S := reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth
  let A := reverseTimeSpatialFormBochnerAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth U
  refine ⟨U, φ, hφ, hclm, ?_⟩
  intro v eta
  let g := reverseTimeFormResidual r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth F hFSmooth U
  let z := reverseTimeSeparatedVTest hΩ eta v
  let G := reverseTimeGelfandCLM hΩ T U
  have hEtaDeriv : MemLp eta.deriv (∞ : ℝ≥0∞) (reverseTimeVolume T) :=
    eta.memLp_deriv ∞
  refine ⟨integrable_reverseTimeWeakDerivative_left hΩ T U v eta,
    integrable_reverseTimeWeakDerivative_right hΩ T g v eta, ?_⟩
  have hmass := reverseTimeGelfand_pairing_multiplier_eq_integral
    hΩ U eta.deriv hEtaDeriv v
  have hleft :
      (∫ tau, inner ℝ (valueCLM hΩ v)
        (reverseTimeValueCLM hΩ T U tau) * eta.deriv tau
        ∂reverseTimeVolume T) =
      (∫ tau, inner ℝ (valueCLM hΩ v) (valueCLM hΩ (U tau)) * eta.deriv tau
        ∂reverseTimeVolume T) := by
    apply integral_congr_ae
    filter_upwards [coeFn_reverseTimeValueCLM hΩ T U] with tau hU
    rw [hU]
  have hright :
      reverseTimeDualPairingRightCLM hΩ T z g =
        ∫ tau, (g tau) v * eta tau ∂reverseTimeVolume T := by
    rw [reverseTimeDualPairingRightCLM_apply,
      reverseTimeDualPairingCLM_apply]
    apply integral_congr_ae
    filter_upwards [ae_reverseTimeSeparatedVTest hΩ eta v] with tau hz
    rw [hz, ContinuousLinearMap.map_smul]
    exact mul_comm _ _
  let m : ℝ := reverseTimeDualPairingRightCLM hΩ T
    (reverseTimeSeparatedVTestOfMemLp hΩ eta.deriv hEtaDeriv v) G
  let s : ℝ := reverseTimeDualPairingRightCLM hΩ T z S
  let f : ℝ := reverseTimeDualPairingRightCLM hΩ T z A
  let q : ℝ := reverseTimeDualPairingRightCLM hΩ T z g
  have hid : m = -s + f := by
    simpa only [m, s, f, T, S, A, z, G,
      reverseTimeGalerkinPrimal_arbitrary_test_identity_prop] using hidentity v eta
  have hres := reverseTimeDualPairingRightCLM_reverseTimeFormResidual
    r₀ r₁ h₀₁ hΩ hΩbounded a b c F
    haSmooth hbSmooth hcSmooth hFSmooth U z
  have hq : q = s - f := by
    dsimp only [q, s, f, g]
    exact hres
  have hpairScalar : m = -q := residual_pairing_algebra hid hq
  have hpair :
      reverseTimeDualPairingRightCLM hΩ T
          (reverseTimeSeparatedVTestOfMemLp hΩ eta.deriv hEtaDeriv v) G =
        -reverseTimeDualPairingRightCLM hΩ T z g := by
    change m = -q
    exact hpairScalar
  calc
    (∫ tau, inner ℝ (valueCLM hΩ v)
        (reverseTimeValueCLM hΩ T U tau) * eta.deriv tau
        ∂reverseTimeVolume T) =
        ∫ tau, inner ℝ (valueCLM hΩ v) (valueCLM hΩ (U tau)) * eta.deriv tau
          ∂reverseTimeVolume T := hleft
    _ = reverseTimeDualPairingRightCLM hΩ T
          (reverseTimeSeparatedVTestOfMemLp hΩ eta.deriv hEtaDeriv v) G := hmass.symm
    _ = -reverseTimeDualPairingRightCLM hΩ T z g := hpair
    _ = -(∫ tau, (g tau) v * eta tau ∂reverseTimeVolume T) := congrArg Neg.neg hright

end HypoellipticAleksandrov.Parabolic.Dirichlet
