module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinPrimalPairingIdentity
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinPrimalWeakSeqCLM

/-!
# Fixed actual-test reverse-time Galerkin limit identity

This module passes the common weak subsequence to every fixed actual
Galerkin vector and scalar time test.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped ENNReal Matrix Matrix.Norms.Elementwise MatrixOrder RealInnerProductSpace
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.Dirichlet

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

/-- The quotient-level reverse-time identity against a fixed actual Galerkin test. -/
def reverseTimeGalerkinPrimal_fixed_test_identity_prop
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
    (U : ReverseTimeL2V hΩ (r₁ - r₀))
    (k : ℕ) (eta : ReverseTimeScalarTest (r₁ - r₀)) : Prop :=
  reverseTimeDualPairingRightCLM hΩ (r₁ - r₀)
      (reverseTimeSeparatedVTestOfMemLp hΩ eta.deriv
        (eta.memLp_deriv ∞) (galerkinVector hΩ k))
      (reverseTimeGelfandCLM hΩ (r₁ - r₀) U) =
    -reverseTimeDualPairingRightCLM hΩ (r₁ - r₀)
        (reverseTimeSeparatedVTest hΩ eta (galerkinVector hΩ k))
        (reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth) +
      reverseTimeDualPairingRightCLM hΩ (r₁ - r₀)
        (reverseTimeSeparatedVTest hΩ eta (galerkinVector hΩ k))
        (reverseTimeSpatialFormBochnerAction r₀ r₁ h₀₁ hΩ hΩbounded
          a b c haSmooth hbSmooth hcSmooth U)

/-- One common weakly convergent Galerkin subsequence satisfies the identity for every
fixed actual Galerkin vector and scalar time test. -/
theorem exists_strictMono_tendsto_clm_reverseTimeGalerkinPrimal_fixedTests
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
      ∀ (k : ℕ) (eta : ReverseTimeScalarTest (r₁ - r₀)),
        reverseTimeGalerkinPrimal_fixed_test_identity_prop
          r₀ r₁ h₀₁ hΩ hΩbounded a b c F
          haSmooth hbSmooth hcSmooth hFSmooth U k eta := by
  obtain ⟨U, φ, hφ, hclm⟩ :=
    exists_strictMono_tendsto_clm_reverseTimeGalerkinPrimal
      r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial
  refine ⟨U, φ, hφ, hclm, ?_⟩
  intro k eta
  let hEtaDeriv : MemLp eta.deriv (∞ : ℝ≥0∞) (reverseTimeVolume (r₁ - r₀)) :=
    eta.memLp_deriv ∞
  let massEll : ReverseTimeL2V hΩ (r₁ - r₀) →L[ℝ] ℝ :=
    (reverseTimeDualPairingRightCLM hΩ (r₁ - r₀)
      (reverseTimeSeparatedVTestOfMemLp hΩ eta.deriv hEtaDeriv
        (galerkinVector hΩ k))).comp (reverseTimeGelfandCLM hΩ (r₁ - r₀))
  let formEll : ReverseTimeL2V hΩ (r₁ - r₀) →L[ℝ] ℝ :=
    (reverseTimeDualPairingRightCLM hΩ (r₁ - r₀)
      (reverseTimeSeparatedVTest hΩ eta (galerkinVector hΩ k))).comp
      (reverseTimeSpatialFormBochnerAction r₀ r₁ h₀₁ hΩ hΩbounded
        a b c haSmooth hbSmooth hcSmooth)
  let source : ℝ := reverseTimeDualPairingRightCLM hΩ (r₁ - r₀)
    (reverseTimeSeparatedVTest hΩ eta (galerkinVector hΩ k))
    (reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth)
  have hMass := hclm massEll
  have hForm := hclm formEll
  have hIndex : ∀ᶠ n in atTop, k + 1 ≤ φ n := by
    filter_upwards [eventually_ge_atTop (k + 1)] with n hn
    exact hn.trans (hφ.id_le n)
  have hFinite :
      (fun n => massEll
        (reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
          a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos
          (φ n) initial)) =ᶠ[atTop]
      fun n => -source + formEll
        (reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
          a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos
          (φ n) initial) := by
    filter_upwards [hIndex] with n hn
    let v : galerkinSpace hΩ (φ n) := ⟨galerkinVector hΩ k,
      galerkinSpace_mono hΩ hn (by
        change galerkinVector hΩ k ∈ Submodule.span ℝ
          (Set.range fun i : Fin (k + 1) => galerkinVector hΩ i)
        apply Submodule.subset_span
        exact ⟨⟨k, Nat.lt_succ_self k⟩, rfl⟩)⟩
    have h := reverseTimeGalerkinPrimal_pairing_identity
      r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos (φ n) initial v eta
    simpa only [reverseTimeGalerkinPrimal_pairing_identity_prop, massEll, formEll,
      source, ContinuousLinearMap.comp_apply, v, hEtaDeriv] using h
  have hMass' : Tendsto
      (fun n => massEll
        (reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
          a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos
          (φ n) initial)) atTop (𝓝 (massEll U)) := hMass
  have hForm' : Tendsto
      (fun n => formEll
        (reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
          a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos
          (φ n) initial)) atTop (𝓝 (formEll U)) := hForm
  have hRight : Tendsto
      (fun n => -source + formEll
        (reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
          a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos
          (φ n) initial)) atTop (𝓝 (-source + formEll U)) :=
    (tendsto_const_nhds.neg).add hForm'
  have hLimit : massEll U = -source + formEll U :=
    tendsto_nhds_unique_of_eventuallyEq hMass' hRight hFinite
  simpa only [reverseTimeGalerkinPrimal_fixed_test_identity_prop, massEll, formEll,
    source, ContinuousLinearMap.comp_apply, hEtaDeriv] using hLimit

end HypoellipticAleksandrov.Parabolic.Dirichlet
