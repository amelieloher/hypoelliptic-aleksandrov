module

public import HypoellipticAleksandrov.Parabolic.ScalarClassical

@[expose] public section

noncomputable section

/-!
# Scalar parabolic Dirichlet data

This module records the supplied-data language for the bounded scalar
parabolic Dirichlet problem.  It defines neighbourhood smoothness, the
zero-order operator, terminal-corner compatibility, and the classical
solution predicate; it proves no existence or regularity result.
-/

namespace HypoellipticAleksandrov.Parabolic

/-- A supplied ambient function is C^∞ on an open neighbourhood of `K`. -/
def IsSmoothOnNeighborhood
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (K : Set E) : Prop :=
  ∃ V : Set E, IsOpen V ∧ K ⊆ V ∧ ContDiffOn ℝ (⊤ : ℕ∞) f V

/-- The backward scalar operator with its source zero-order term. -/
def scalarParabolicZeroOrderOperator {n : ℕ}
    (a : CoefficientField n)
    (b : ℝ → PDE.Vec n → PDE.Vec n)
    (c : ℝ → PDE.Vec n → ℝ)
    (u : TimeVelocity n → ℝ)
    (z : TimeVelocity n) : ℝ :=
  scalarParabolicOperator a b u z + c z.1 z.2 * u z

/-- Evaluation of the scalar parabolic operator with its zero-order term. -/
@[simp] theorem scalarParabolicZeroOrderOperator_apply {n : ℕ}
    (a : CoefficientField n)
    (b : ℝ → PDE.Vec n → PDE.Vec n)
    (c : ℝ → PDE.Vec n → ℝ)
    (u : TimeVelocity n → ℝ)
    (z : TimeVelocity n) :
    scalarParabolicZeroOrderOperator a b c u z =
      scalarTimeDerivative u z +
        matrixContraction (a z.1 z.2) (scalarSpatialHessian u z) +
        PDE.vecDot (b z.1 z.2) (scalarSpatialGradient u z) +
        c z.1 z.2 * u z :=
  rfl

/-- Zero-lateral terminal-corner compatibility. -/
def IsHomogeneousTerminalCornerCompatible {n : ℕ}
    (Ω : Set (PDE.Vec n)) (phi : PDE.Vec n → ℝ) : Prop :=
  ∀ y ∈ frontier Ω, phi y = 0

/-- Value compatibility of terminal and lateral data at their common corner. -/
def IsTerminalCornerCompatible {n : ℕ}
    (r₁ : ℝ) (Ω : Set (PDE.Vec n))
    (phi : PDE.Vec n → ℝ) (h : TimeVelocity n → ℝ) : Prop :=
  ∀ y ∈ frontier Ω, h (r₁, y) = phi y

/-- A supplied classical solution of the backward scalar Dirichlet problem. -/
def IsClassicalBackwardDirichletSolution {n : ℕ}
    (r₀ r₁ : ℝ) (Ω : Set (PDE.Vec n))
    (a : CoefficientField n)
    (b : ℝ → PDE.Vec n → PDE.Vec n)
    (c F : ℝ → PDE.Vec n → ℝ)
    (phi : PDE.Vec n → ℝ) (h u : TimeVelocity n → ℝ) : Prop :=
  ContinuousOn u (scalarParabolicClosedCylinder r₀ r₁ Ω) ∧
    IsScalarC12On u (scalarParabolicOpenCylinder r₀ r₁ Ω) ∧
    (∀ z ∈ scalarParabolicOpenCylinder r₀ r₁ Ω,
      scalarParabolicZeroOrderOperator a b c u z = F z.1 z.2) ∧
    (∀ y ∈ closure Ω, u (r₁, y) = phi y) ∧
    (∀ z ∈ scalarParabolicLateralFace r₀ r₁ Ω, u z = h z)

end HypoellipticAleksandrov.Parabolic
