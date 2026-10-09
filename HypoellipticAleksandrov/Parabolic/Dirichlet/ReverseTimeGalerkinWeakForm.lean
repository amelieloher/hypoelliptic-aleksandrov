module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinCoordinatesBase

/-!
# Reverse-time finite Galerkin weak form

This module extends an exact finite Galerkin basis-row equation to every test
vector in that same finite Galerkin space.  It makes no limiting or time-
integrated assertion.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open scoped BigOperators ENNReal Matrix Matrix.Norms.Elementwise RealInnerProductSpace

private theorem map_galerkinReconstruct_sum
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (N : ℕ) {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (Q : H10HilbertGraph hΩ →L[ℝ] Z)
    (x : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) :
    Q (galerkinReconstruct hΩ N x : H10HilbertGraph hΩ) =
      ∑ i, x i • Q (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) := by
  calc
    Q (galerkinReconstruct hΩ N x : H10HilbertGraph hΩ) =
        Q (↑(∑ i, x i • galerkinSpaceBasis hΩ N i) : H10HilbertGraph hΩ) := by
      exact congrArg Q (congrArg (fun w : galerkinSpace hΩ N =>
        (w : H10HilbertGraph hΩ)) (galerkinReconstruct_apply hΩ N x))
    _ = Q (∑ i, x i • (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ)) := by
      have hcoe : (↑(∑ i, x i • galerkinSpaceBasis hΩ N i) : H10HilbertGraph hΩ) =
          ∑ i, x i • (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) := by
        simpa only [Submodule.coe_smul] using
          (Submodule.coe_sum (p := galerkinSpace hΩ N)
            (fun i => x i • galerkinSpaceBasis hΩ N i) Finset.univ)
      exact congrArg Q hcoe
    _ = ∑ i, x i • Q (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) := by
      calc
        Q (∑ i, x i • (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ)) =
            ∑ i, Q (x i • (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ)) :=
          map_sum Q (fun i => x i • (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ))
            Finset.univ
        _ = _ := by
          apply Finset.sum_congr rfl
          intro i _
          exact Q.map_smul (x i) (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ)

/-- Exact finite Galerkin basis rows hold against every finite Galerkin test. -/
theorem reverseTimeGalerkin_basisRows_forall
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
    (N : ℕ) (τ : Set.Icc 0 (r₁ - r₀))
    (x xdot : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ)
    (hrows : ∀ i : Fin (Module.finrank ℝ (galerkinSpace hΩ N)),
      inner ℝ
          (valueCLM hΩ (galerkinReconstruct hΩ N xdot : H10HilbertGraph hΩ))
          (valueCLM hΩ (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ)) +
        reverseTimeSpatialForm hΩ r₁ τ.1 a b c
          (galerkinReconstruct hΩ N x : H10HilbertGraph hΩ)
          (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) =
        reverseTimeGalerkinSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ i)
    (v : galerkinSpace hΩ N) :
    inner ℝ
        (valueCLM hΩ (galerkinReconstruct hΩ N xdot : H10HilbertGraph hΩ))
        (valueCLM hΩ (v : H10HilbertGraph hΩ)) +
      reverseTimeSpatialForm hΩ r₁ τ.1 a b c
        (galerkinReconstruct hΩ N x : H10HilbertGraph hΩ)
        (v : H10HilbertGraph hΩ) =
      reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ.1
        (v : H10HilbertGraph hΩ) := by
  let q : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ :=
    (galerkinSpaceBasis hΩ N).equivFun v
  let u : H10HilbertGraph hΩ := galerkinReconstruct hΩ N x
  let udot : PDE.ScalarLp Ω (2 : ℝ≥0∞) :=
    valueCLM hΩ (galerkinReconstruct hΩ N xdot : H10HilbertGraph hΩ)
  let e : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → H10HilbertGraph hΩ :=
    fun i => galerkinSpaceBasis hΩ N i
  let B : H10HilbertGraph hΩ →L[ℝ] ℝ :=
    reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth τ u
  let A : H10HilbertGraph hΩ →L[ℝ] ℝ :=
    (innerSL ℝ udot).comp (valueCLM hΩ)
  let T : H10HilbertGraph hΩ →L[ℝ] ℝ := A + B
  let S : H10HilbertGraph hΩ →L[ℝ] ℝ :=
    reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ.1
  have hu : (galerkinReconstruct hΩ N q : H10HilbertGraph hΩ) = v := by
    exact congrArg (fun w : galerkinSpace hΩ N => (w : H10HilbertGraph hΩ))
      (galerkinReconstruct_equivFun hΩ N v)
  have hrow : ∀ i, T (e i) = S (e i) := by
    intro i
    simpa only [T, A, B, S, e, udot, u, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply, innerSL_apply_apply,
      reverseTimeSpatialFormOperator_apply, reverseTimeGalerkinSource] using hrows i
  have hsum : ∑ i, q i • T (e i) = ∑ i, q i • S (e i) := by
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun z => q i • z) (hrow i)
  have hT := map_galerkinReconstruct_sum hΩ N T q
  have hS := map_galerkinReconstruct_sum hΩ N S q
  have hresult : T (galerkinReconstruct hΩ N q : H10HilbertGraph hΩ) =
      S (galerkinReconstruct hΩ N q : H10HilbertGraph hΩ) :=
    hT.trans (hsum.trans hS.symm)
  rw [hu] at hresult
  simpa only [T, A, B, S, udot, u, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, reverseTimeSpatialFormOperator_apply]
    using hresult

end HypoellipticAleksandrov.Parabolic.Dirichlet
