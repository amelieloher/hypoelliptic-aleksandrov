module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.GlobalLinearODE
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinCoordinates

/-!
# Reverse-time finite Galerkin ODE solutions

This module lifts the finite-coordinate ODE to the Galerkin space and
records its exact basis-row weak equation.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open scoped BigOperators ENNReal Matrix Matrix.Norms.Elementwise RealInnerProductSpace

/-- A reverse-time finite Galerkin coordinate solution and its reconstruction exist. -/
theorem exists_reverseTimeGalerkin_solution
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c F : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (N : ℕ) (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    ∃ x : ℝ → Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ,
      ∃ u : ℝ → galerkinSpace hΩ N,
        x 0 = (galerkinSpaceBasis hΩ N).equivFun
          (galerkinInitialProjection hΩ N initial) ∧
        u = (fun τ => galerkinReconstruct hΩ N (x τ)) ∧
        ContinuousOn x (Set.Icc 0 (r₁ - r₀)) ∧
        ContinuousOn u (Set.Icc 0 (r₁ - r₀)) ∧
        (∀ τ : Set.Icc 0 (r₁ - r₀),
          HasDerivWithinAt x
            (reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c
              haSmooth hbSmooth hcSmooth N τ (x τ) +
            reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ)
            (Set.Icc 0 (r₁ - r₀)) τ ∧
          ∀ i : Fin (Module.finrank ℝ (galerkinSpace hΩ N)),
            inner ℝ
                (valueCLM hΩ (galerkinReconstruct hΩ N
                  (reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c
                    haSmooth hbSmooth hcSmooth N τ (x τ) +
                  reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ) :
                    H10HilbertGraph hΩ))
                (valueCLM hΩ (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ)) +
              reverseTimeSpatialForm hΩ r₁ τ.1 a b c
                (u τ : H10HilbertGraph hΩ)
                (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) =
              reverseTimeGalerkinSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ i) := by
  let T := r₁ - r₀
  have hT : 0 ≤ T := sub_nonneg.mpr h₀₁.le
  let x0 : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ :=
    (galerkinSpaceBasis hΩ N).equivFun (galerkinInitialProjection hΩ N initial)
  let A : ℝ → (Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) →L[ℝ]
      (Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) :=
    fun τ => reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth N (Set.projIcc 0 T hT τ)
  let f : ℝ → Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ :=
    fun τ => reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N
      (Set.projIcc 0 T hT τ)
  have hA : ContinuousOn A (Set.Icc 0 T) := by
    exact ((continuous_reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth N).comp continuous_projIcc).continuousOn
  have hf : ContinuousOn f (Set.Icc 0 T) := by
    exact ((continuous_reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N).comp
      continuous_projIcc).continuousOn
  have hode := exists_linear_ode_on_Icc hT A f hA hf x0
  let x := hode.choose
  have hx0 : x 0 = x0 := hode.choose_spec.1
  have hxcont : ContinuousOn x (Set.Icc 0 T) := hode.choose_spec.2.1
  have hdx : ∀ τ ∈ Set.Icc 0 T, HasDerivWithinAt x (A τ (x τ) + f τ)
      (Set.Icc 0 T) τ := hode.choose_spec.2.2
  let u : ℝ → galerkinSpace hΩ N := fun τ => galerkinReconstruct hΩ N (x τ)
  have hucont : ContinuousOn u (Set.Icc 0 T) := by
    exact (LinearMap.toContinuousLinearMap (galerkinReconstruct hΩ N)).continuous.continuousOn
      |>.comp hxcont (fun _ _ => Set.mem_univ _)
  refine ⟨x, u, ?_, rfl, hxcont, hucont, ?_⟩
  · simpa only [x0] using hx0
  intro τ
  have hproj : Set.projIcc 0 T hT (τ : ℝ) = τ := Set.projIcc_of_mem hT τ.2
  constructor
  · simpa only [A, f, hproj] using hdx τ τ.2
  · simpa only [u] using
      (reverseTimeGalerkin_coordinateEquation_iff r₀ r₁ h₀₁ hΩ hΩbounded a b c F
        haSmooth hbSmooth hcSmooth hFSmooth N τ (x τ)
        (reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth N τ (x τ) +
        reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ)).mpr rfl

end HypoellipticAleksandrov.Parabolic.Dirichlet
