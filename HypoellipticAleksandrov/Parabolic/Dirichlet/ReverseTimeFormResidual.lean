module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormBochner
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSourceBochner

/-!
# Reverse-time form residual

This module records the literal Bochner-dual residual obtained by subtracting
the reverse-time spatial-form action from the negative source.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal RealInnerProductSpace Matrix.Norms.Elementwise MatrixOrder

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- The reverse-time residual candidate in the Bochner dual carrier. -/
noncomputable def reverseTimeFormResidual
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (F : ℝ → PDE.Vec d → ℝ)
    (hFSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (u : ReverseTimeL2V hΩ (r₁ - r₀)) :
    ReverseTimeL2VStar hΩ (r₁ - r₀) :=
  reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth -
    reverseTimeSpatialFormBochnerAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth u

/-- On one event, the residual plus the literal spatial form is the
negative reverse-time source functional, simultaneously for all spatial tests. -/
theorem ae_reverseTimeFormResidual_apply
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (F : ℝ → PDE.Vec d → ℝ)
    (hFSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (u : ReverseTimeL2V hΩ (r₁ - r₀)) :
    ∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀),
      ∀ hτ : τ ∈ Set.Ioo 0 (r₁ - r₀),
        ∀ v : H10HilbertGraph hΩ,
          reverseTimeFormResidual r₀ r₁ h₀₁ hΩ hΩbounded a b c
            haSmooth hbSmooth hcSmooth F hFSmooth u τ v +
            reverseTimeSpatialForm hΩ r₁ τ a b c (u τ) v =
          reverseTimeSourceFunctional hΩ
            (reverseTimeSourceSlice r₁ τ F
              (reverseTimeSourceSlice_memLp_of_smoothOnNeighborhood
                r₀ r₁ hΩ hΩbounded F hFSmooth τ
                ⟨le_of_lt hτ.1, le_of_lt hτ.2⟩)) v := by
  filter_upwards [
    ae_reverseTimeNegativeSource_apply r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth,
    ae_reverseTimeSpatialFormBochnerAction_apply r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth u,
    Lp.coeFn_sub
      (reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth)
      (reverseTimeSpatialFormBochnerAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth u)] with τ hSource hAction hSub
  intro hτ v
  rw [reverseTimeFormResidual, hSub, Pi.sub_apply, ContinuousLinearMap.sub_apply,
    hSource hτ, hAction v]
  abel

end HypoellipticAleksandrov.Parabolic.Dirichlet
