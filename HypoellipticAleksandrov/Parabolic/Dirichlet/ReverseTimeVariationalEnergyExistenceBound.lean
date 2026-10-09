module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.VariationalEnergy
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinPrimalInitialTraceNorm

/-!
# Reverse-time variational energy existence with radius bound

This module assembles the same reverse-time Galerkin limit's canonical initial
trace, literal residual equation, and inherited uniform Bochner-radius bound.
-/

@[expose] public section

open Set Topology
open scoped ENNReal Matrix.Norms.Elementwise MatrixOrder RealInnerProductSpace

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- The homogeneous-lateral reverse-time Dirichlet problem has a variational
energy solution with the prescribed canonical initial trace and explicit
uniform Bochner-radius bound. -/
theorem exists_reverseTime_variational_energy_solution_norm_le_radius
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ lam Lam : ℝ) (h₀₁ : r₀ < r₁)
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
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
    (hLower : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
        lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
    (hUpper : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
        a z.1 z.2 ≤ Lam • (1 : PDE.Mat d))
    (hcNonpos : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → c z.1 z.2 ≤ 0)
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    ∃ (u : ReverseTimeL2V hΩ (r₁ - r₀)),
      ∃ (g : ReverseTimeL2VStar hΩ (r₁ - r₀)),
        ∃ hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀)
          (sub_pos.mpr h₀₁) u g,
          IsReverseTimeVariationalEnergySolution
              r₀ r₁ h₀₁ hΩ hΩbounded a b c F hFSmooth initial u g hdu ∧
            ‖u‖ ≤
              reverseTimeGalerkinPrimalRadius r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
                a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial := by
  obtain ⟨U, hdu, htrace, hNorm⟩ :=
    exists_reverseTimeGalerkinPrimal_initialTrace_norm_le_radius
      r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial
  refine ⟨U,
    reverseTimeFormResidual r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth F hFSmooth U,
    hdu, ?_, hNorm⟩
  exact ⟨htrace,
    ae_reverseTimeFormResidual_apply r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth F hFSmooth U⟩

end HypoellipticAleksandrov.Parabolic.Dirichlet
