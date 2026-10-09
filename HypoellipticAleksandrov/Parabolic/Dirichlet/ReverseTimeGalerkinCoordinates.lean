module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinCoordinatesBase

/-!
# Reverse-time finite Galerkin coordinate equation

This module proves the exact finite-coordinate reverse-time Galerkin equation.
It does not assert existence, uniqueness, differentiability, or an energy estimate.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open scoped BigOperators ENNReal Matrix Matrix.Norms.Elementwise RealInnerProductSpace

private theorem bilinear_mulVec_eq_coe_submodule_sum
    {I E : Type} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : Submodule ℝ E) (L : E →L[ℝ] E →L[ℝ] ℝ)
    (e : I → p) (x : I → ℝ) (i : I) :
    ((fun i j => L (e j : E) (e i : E)) *ᵥ x) i =
      L (↑(∑ j, x j • e j) : E) (e i : E) := by
  have hcoe : (↑(∑ j, x j • e j) : E) = ∑ j, x j • (e j : E) := by
    simpa only [Submodule.coe_smul] using
      (Submodule.coe_sum (p := p) (fun j => x j • e j) Finset.univ)
  change (∑ j, L (e j : E) (e i : E) * x j) =
    L (↑(∑ j, x j • e j) : E) (e i : E)
  calc
    _ = ∑ j, L (x j • (e j : E)) (e i : E) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [L.map_smul, ContinuousLinearMap.smul_apply]
      exact mul_comm _ _
    _ = (∑ j, L (x j • (e j : E))) (e i : E) := by
      exact (map_sum (ContinuousLinearMap.apply ℝ ℝ (e i : E))
        (fun j => L (x j • (e j : E))) Finset.univ).symm
    _ = L (∑ j, x j • (e j : E)) (e i : E) := by rw [← map_sum]
    _ = _ := congrArg (fun u => L u (e i : E)) hcoe.symm

private theorem coe_galerkinReconstruct_eq_sum
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (N : ℕ)
    (x : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) :
    (galerkinReconstruct hΩ N x : H10HilbertGraph hΩ) =
      (↑(∑ j, x j • galerkinSpaceBasis hΩ N j) : H10HilbertGraph hΩ) := by
  exact congrArg (fun u : galerkinSpace hΩ N => (u : H10HilbertGraph hΩ))
    (galerkinReconstruct_apply hΩ N x)

private theorem stiffness_mulVec_eq_operator_sum
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (N : ℕ) (τ : Set.Icc 0 (r₁ - r₀))
    (x : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ)
    (i : Fin (Module.finrank ℝ (galerkinSpace hΩ N))) :
    (reverseTimeGalerkinStiffness r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth N τ *ᵥ
      x) i =
      reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth τ
        (↑(∑ j, x j • galerkinSpaceBasis hΩ N j) : H10HilbertGraph hΩ)
        (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) := by
  let L : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ →L[ℝ] ℝ :=
    reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth τ
  let e : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → galerkinSpace hΩ N :=
    galerkinSpaceBasis hΩ N
  change ((fun r s => L (e s : H10HilbertGraph hΩ) (e r : H10HilbertGraph hΩ)) *ᵥ x) i = _
  exact bilinear_mulVec_eq_coe_submodule_sum (galerkinSpace hΩ N) L e x i

private theorem operator_sum_eq_operator_reconstruct
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (N : ℕ) (τ : Set.Icc 0 (r₁ - r₀))
    (x : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ)
    (i : Fin (Module.finrank ℝ (galerkinSpace hΩ N))) :
    reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth τ
        (↑(∑ j, x j • galerkinSpaceBasis hΩ N j) : H10HilbertGraph hΩ)
        (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) =
      reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth τ
        (galerkinReconstruct hΩ N x : H10HilbertGraph hΩ)
        (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) := by
  let L : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ →L[ℝ] ℝ :=
    reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth τ
  let v : H10HilbertGraph hΩ := galerkinSpaceBasis hΩ N i
  exact congrArg (fun u => L u v) (coe_galerkinReconstruct_eq_sum hΩ N x).symm

private theorem operator_reconstruct_eq_raw_form
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (N : ℕ) (τ : Set.Icc 0 (r₁ - r₀))
    (x : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ)
    (i : Fin (Module.finrank ℝ (galerkinSpace hΩ N))) :
    reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth τ
        (galerkinReconstruct hΩ N x : H10HilbertGraph hΩ)
        (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) =
      reverseTimeSpatialForm hΩ r₁ τ.1 a b c
        (galerkinReconstruct hΩ N x : H10HilbertGraph hΩ)
        (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) := by
  exact reverseTimeSpatialFormOperator_apply r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth
    τ _ _

private theorem stiffness_mulVec_eq_form
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (N : ℕ) (τ : Set.Icc 0 (r₁ - r₀))
    (x : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ)
    (i : Fin (Module.finrank ℝ (galerkinSpace hΩ N))) :
    (reverseTimeGalerkinStiffness r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth N τ *ᵥ
      x) i = reverseTimeSpatialForm hΩ r₁ τ.1 a b c
        (galerkinReconstruct hΩ N x : H10HilbertGraph hΩ)
        (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) := by
  calc
    _ = reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth τ
        (↑(∑ j, x j • galerkinSpaceBasis hΩ N j) : H10HilbertGraph hΩ)
        (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) :=
      stiffness_mulVec_eq_operator_sum r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth
        N τ x i
    _ = reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth τ
        (galerkinReconstruct hΩ N x : H10HilbertGraph hΩ)
        (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) :=
      operator_sum_eq_operator_reconstruct r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth
        N τ x i
    _ = _ :=
      operator_reconstruct_eq_raw_form r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth
        N τ x i

private theorem map_galerkinBasis_sum
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (N : ℕ) {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (L : H10HilbertGraph hΩ →L[ℝ] W)
    (x : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) :
    L (↑(∑ j, x j • galerkinSpaceBasis hΩ N j) : H10HilbertGraph hΩ) =
      ∑ j, x j • L (galerkinSpaceBasis hΩ N j : H10HilbertGraph hΩ) := by
  have hcoe : (↑(∑ j, x j • galerkinSpaceBasis hΩ N j) : H10HilbertGraph hΩ) =
      ∑ j, x j • (galerkinSpaceBasis hΩ N j : H10HilbertGraph hΩ) := by
    simpa only [Submodule.coe_smul] using
      (Submodule.coe_sum (p := galerkinSpace hΩ N)
        (fun j => x j • galerkinSpaceBasis hΩ N j) Finset.univ)
  calc
    L (↑(∑ j, x j • galerkinSpaceBasis hΩ N j) : H10HilbertGraph hΩ) =
        L (∑ j, x j • (galerkinSpaceBasis hΩ N j : H10HilbertGraph hΩ)) := congrArg L hcoe
    _ = ∑ j, L (x j • (galerkinSpaceBasis hΩ N j : H10HilbertGraph hΩ)) :=
      map_sum L (fun j => x j • (galerkinSpaceBasis hΩ N j : H10HilbertGraph hΩ)) Finset.univ
    _ = ∑ j, x j • L (galerkinSpaceBasis hΩ N j : H10HilbertGraph hΩ) := by
      apply Finset.sum_congr rfl
      intro j _
      exact L.map_smul (x j) (galerkinSpaceBasis hΩ N j : H10HilbertGraph hΩ)

private theorem gram_mulVec_eq_inner_sum
    {I E : Type} [Fintype I] [DecidableEq I] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (v : I → E) (x : I → ℝ) (i : I) :
    (Matrix.gram ℝ v *ᵥ x) i = inner ℝ (∑ j, x j • v j) (v i) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.gram_apply, sum_inner, inner_smul_left,
    starRingEnd_apply, star_trivial]
  apply Finset.sum_congr rfl
  intro j _
  rw [real_inner_comm]
  exact mul_comm _ _

private theorem galerkinMass_mulVec_eq_inner_reconstruct
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (N : ℕ)
    (x : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ)
    (i : Fin (Module.finrank ℝ (galerkinSpace hΩ N))) :
    (galerkinMassGram hΩ N *ᵥ x) i =
      inner ℝ
        (valueCLM hΩ (galerkinReconstruct hΩ N x : H10HilbertGraph hΩ))
        (valueCLM hΩ (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ)) := by
  rw [galerkinReconstruct_apply]
  let v : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → PDE.ScalarLp Ω (2 : ℝ≥0∞) :=
    fun j => valueCLM hΩ (galerkinSpaceBasis hΩ N j : H10HilbertGraph hΩ)
  calc
    (galerkinMassGram hΩ N *ᵥ x) i = (Matrix.gram ℝ v *ᵥ x) i := rfl
    _ = inner ℝ (∑ j, x j • v j) (v i) := gram_mulVec_eq_inner_sum v x i
    _ = inner ℝ
        (valueCLM hΩ (↑(∑ j, x j • galerkinSpaceBasis hΩ N j) : H10HilbertGraph hΩ))
        (v i) := congrArg (fun z => inner ℝ z (v i))
          (map_galerkinBasis_sum hΩ N (valueCLM hΩ) x).symm

private theorem weak_rows_iff_matrix_rows
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
    (N : ℕ) (τ : Set.Icc 0 (r₁ - r₀))
    (x xdot : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) :
    (∀ i,
      inner ℝ
          (valueCLM hΩ (galerkinReconstruct hΩ N xdot : H10HilbertGraph hΩ))
          (valueCLM hΩ (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ)) +
        reverseTimeSpatialForm hΩ r₁ τ.1 a b c
          (galerkinReconstruct hΩ N x : H10HilbertGraph hΩ)
          (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) =
        reverseTimeGalerkinSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ i) ↔
      ∀ i, (galerkinMassGram hΩ N *ᵥ xdot) i +
        (reverseTimeGalerkinStiffness r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth N τ *ᵥ
          x) i =
        reverseTimeGalerkinSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ i := by
  constructor <;> intro h i
  · simpa only [galerkinMass_mulVec_eq_inner_reconstruct, stiffness_mulVec_eq_form] using h i
  · simpa only [galerkinMass_mulVec_eq_inner_reconstruct, stiffness_mulVec_eq_form] using h i

private theorem matrix_coordinateEquation_iff
    {I : Type} [Fintype I] [DecidableEq I]
    (M K : Matrix I I ℝ) (q x xdot : I → ℝ) (hdet : IsUnit M.det) :
    (∀ i, (M *ᵥ xdot) i + (K *ᵥ x) i = q i) ↔
      xdot = -(M⁻¹ *ᵥ (K *ᵥ x)) + M⁻¹ *ᵥ q := by
  constructor
  · intro h
    have hmk : M *ᵥ xdot + K *ᵥ x = q := by
      ext i
      exact h i
    have hsolve : M *ᵥ xdot = q - K *ᵥ x := (eq_sub_iff_add_eq).2 hmk
    calc
      xdot = (1 : Matrix I I ℝ) *ᵥ xdot := (Matrix.one_mulVec _).symm
      _ = (M⁻¹ * M) *ᵥ xdot := by rw [Matrix.nonsing_inv_mul M hdet]
      _ = M⁻¹ *ᵥ (M *ᵥ xdot) := (Matrix.mulVec_mulVec xdot M⁻¹ M).symm
      _ = M⁻¹ *ᵥ (q - K *ᵥ x) := by rw [hsolve]
      _ = -(M⁻¹ *ᵥ (K *ᵥ x)) + M⁻¹ *ᵥ q := by
        rw [Matrix.mulVec_sub]
        abel
  · intro h
    have hmul : M *ᵥ xdot + K *ᵥ x = q := by
      have hstiff : M *ᵥ (M⁻¹ *ᵥ (K *ᵥ x)) = K *ᵥ x := by
        rw [Matrix.mulVec_mulVec (K *ᵥ x) M M⁻¹, Matrix.mul_nonsing_inv M hdet,
          Matrix.one_mulVec]
      have hsource : M *ᵥ (M⁻¹ *ᵥ q) = q := by
        rw [Matrix.mulVec_mulVec q M M⁻¹, Matrix.mul_nonsing_inv M hdet,
          Matrix.one_mulVec]
      rw [h, Matrix.mulVec_add, Matrix.mulVec_neg, hstiff, hsource]
      abel
    intro i
    exact congrFun hmul i

private theorem matrix_solution_eq_continuousMulVec_rhs
    {I : Type} [Fintype I] [DecidableEq I]
    (M K : Matrix I I ℝ) (q x : I → ℝ) :
    -(M *ᵥ (K *ᵥ x)) + M *ᵥ q =
      (- LinearMap.toContinuousLinearMap (Matrix.mulVecLin (M * K))) x + M *ᵥ q := by
  change -(M *ᵥ (K *ᵥ x)) + M *ᵥ q =
    -((M * K) *ᵥ x) + M *ᵥ q
  rw [Matrix.mulVec_mulVec]

private theorem matrix_solution_eq_reverseTimeGalerkin_rhs
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
    (N : ℕ) (τ : Set.Icc 0 (r₁ - r₀))
    (x : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) :
    -((galerkinMassGram hΩ N)⁻¹ *ᵥ
      (reverseTimeGalerkinStiffness r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth N τ *ᵥ
        x)) +
      (galerkinMassGram hΩ N)⁻¹ *ᵥ
        reverseTimeGalerkinSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ =
      reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth N τ x +
        reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ := by
  change -((galerkinMassGram hΩ N)⁻¹ *ᵥ
      (reverseTimeGalerkinStiffness r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth N τ *ᵥ
        x)) +
      (galerkinMassGram hΩ N)⁻¹ *ᵥ
        reverseTimeGalerkinSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ =
      (- LinearMap.toContinuousLinearMap (Matrix.mulVecLin
        ((galerkinMassGram hΩ N)⁻¹ *
          reverseTimeGalerkinStiffness r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth
            N τ))) x +
        (galerkinMassGram hΩ N)⁻¹ *ᵥ
          reverseTimeGalerkinSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ
  exact matrix_solution_eq_continuousMulVec_rhs (galerkinMassGram hΩ N)⁻¹
    (reverseTimeGalerkinStiffness r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth N τ)
    (reverseTimeGalerkinSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ) x

private theorem eq_iff_eq_of_eq_right {E : Type} (x y z : E) (hyz : y = z) :
    (x = y ↔ x = z) := by
  rw [hyz]

private theorem matrix_rows_iff_reverseTimeGalerkin_rhs
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
    (N : ℕ) (τ : Set.Icc 0 (r₁ - r₀))
    (x xdot : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) :
    (∀ i, (galerkinMassGram hΩ N *ᵥ xdot) i +
        (reverseTimeGalerkinStiffness r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth N τ *ᵥ x) i =
        reverseTimeGalerkinSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ i) ↔
      xdot =
        reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth N τ x +
        reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ := by
  let M : Matrix (Fin (Module.finrank ℝ (galerkinSpace hΩ N)))
      (Fin (Module.finrank ℝ (galerkinSpace hΩ N))) ℝ := galerkinMassGram hΩ N
  let K : Matrix (Fin (Module.finrank ℝ (galerkinSpace hΩ N)))
      (Fin (Module.finrank ℝ (galerkinSpace hΩ N))) ℝ :=
    reverseTimeGalerkinStiffness r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth N τ
  let q : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ :=
    reverseTimeGalerkinSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ
  have hdet : IsUnit M.det := (M.isUnit_iff_isUnit_det).mp (isUnit_galerkinMassGram hΩ N)
  have hrhs := matrix_solution_eq_reverseTimeGalerkin_rhs r₀ r₁ h₀₁ hΩ hΩbounded a b c F
    haSmooth hbSmooth hcSmooth hFSmooth N τ x
  exact (matrix_coordinateEquation_iff M K q x xdot hdet).trans
    (eq_iff_eq_of_eq_right xdot (-(M⁻¹ *ᵥ (K *ᵥ x)) + M⁻¹ *ᵥ q)
      (reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth N τ x +
        reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ) hrhs)

private theorem reverseTimeGalerkin_coordinateEquation_iff_aux
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
    (N : ℕ) (τ : Set.Icc 0 (r₁ - r₀))
    (x xdot : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) :
    (∀ i,
      inner ℝ
          (valueCLM hΩ (galerkinReconstruct hΩ N xdot : H10HilbertGraph hΩ))
          (valueCLM hΩ (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ)) +
        reverseTimeSpatialForm hΩ r₁ τ.1 a b c
          (galerkinReconstruct hΩ N x : H10HilbertGraph hΩ)
          (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) =
        reverseTimeGalerkinSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ i) ↔
      xdot =
        reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth N τ
          x +
        reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ := by
  exact (weak_rows_iff_matrix_rows r₀ r₁ h₀₁ hΩ hΩbounded a b c F haSmooth hbSmooth hcSmooth
    hFSmooth N τ x xdot).trans
    (matrix_rows_iff_reverseTimeGalerkin_rhs r₀ r₁ h₀₁ hΩ hΩbounded a b c F haSmooth hbSmooth
      hcSmooth hFSmooth N τ x xdot)

/-- The finite weak-coordinate equation is exactly the mass-inverted local linear ODE.
This theorem neither constructs nor solves a curve. -/
theorem reverseTimeGalerkin_coordinateEquation_iff
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
    (N : ℕ) (τ : Set.Icc 0 (r₁ - r₀))
    (x xdot : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) :
    (∀ i,
      inner ℝ
          (valueCLM hΩ (galerkinReconstruct hΩ N xdot : H10HilbertGraph hΩ))
          (valueCLM hΩ (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ)) +
        reverseTimeSpatialForm hΩ r₁ τ.1 a b c
          (galerkinReconstruct hΩ N x : H10HilbertGraph hΩ)
          (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) =
        reverseTimeGalerkinSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ i) ↔
      xdot =
        reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth N τ
          x +
        reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ := by
  exact reverseTimeGalerkin_coordinateEquation_iff_aux r₀ r₁ h₀₁ hΩ hΩbounded a b c F haSmooth
    hbSmooth hcSmooth hFSmooth N τ x xdot

end HypoellipticAleksandrov.Parabolic.Dirichlet
