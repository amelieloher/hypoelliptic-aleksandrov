module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Forward.Elapsed

/-!
# Admissible test functions of the forward equation

Admissible test functions: a test function `φ(τ, y)` on `(0, T) × ℝ^{2d}` is admissible if it is
`C¹` in `τ`, `C²` in `y`, vanishes for `τ ∉ [a, b]` with `0 < a < b < T`, and `φ`, `∂_τ φ`,
`∇_y φ`, the velocity second partials and `|v| |∇_z φ|` are bounded and continuous.  This
module also records the integrand `∂_τ φ + B : D_v² φ + v · ∇_z φ` of the forward equation
(the forward equation) and its identification with the joint expression for smooth `φ`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

open Set

variable {d : ℕ}

/-- A function of `(τ, y)` is bounded and (jointly) continuous. -/
def IsBoundedContinuous (f : ℝ × EvolutionAmbientState d → ℝ) : Prop :=
  Continuous f ∧ ∃ C : ℝ, ∀ q, |f q| ≤ C

/-- **Admissible test functions**, on the slab `(0, T)`. -/
structure IsAdmissibleTest (T : ℝ) (φ : ℝ → EvolutionAmbientState d → ℝ) : Prop where
  /-- `C¹` in `τ`. -/
  contDiff_time : ∀ y, ContDiff ℝ 1 (fun τ => φ τ y)
  /-- `C²` in `y`. -/
  contDiff_space : ∀ τ, ContDiff ℝ 2 (φ τ)
  /-- Vanishing outside `[a, b]` with `0 < a < b < T`. -/
  support : ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < T ∧ ∀ τ, τ ∉ Icc a b → φ τ = 0
  /-- `φ` is bounded and continuous. -/
  value : IsBoundedContinuous (fun q => φ q.1 q.2)
  /-- `∂_τ φ` is bounded and continuous. -/
  timeDeriv : IsBoundedContinuous (fun q => deriv (fun τ => φ τ q.2) q.1)
  /-- The velocity gradient is bounded and continuous. -/
  velocityGrad : ∀ i, IsBoundedContinuous (fun q => velocityPartial i (φ q.1) q.2)
  /-- The position gradient is bounded and continuous. -/
  positionGrad : ∀ i, IsBoundedContinuous (fun q => positionPartial i (φ q.1) q.2)
  /-- The velocity Hessian is bounded and continuous. -/
  velocityHess : ∀ i j,
    IsBoundedContinuous (fun q => velocityPartial i (velocityPartial j (φ q.1)) q.2)
  /-- The weighted transport terms `|v| |∇_z φ|` are bounded and continuous. -/
  weightedTransport : ∀ i j,
    IsBoundedContinuous (fun q => q.2.1 i * positionPartial j (φ q.1) q.2)

/-- The integrand `∂_τ φ + B : D_v² φ + v · ∇_z φ` of the forward equation, with the
coefficient evaluated at the absolute time `σ₀ + τ`. -/
def forwardIntegrand (B : FullKineticCoefficient d) (σ₀ : ℝ)
    (φ : ℝ → EvolutionAmbientState d → ℝ) (τ : ℝ) (y : EvolutionAmbientState d) : ℝ :=
  deriv (fun τ => φ τ y) τ + velocityHessianContraction (B (σ₀ + τ) y.1 y.2) (φ τ) y +
    transportDerivative (φ τ) y

/-- For jointly smooth `φ` the slice integrand is the joint forward expression. -/
theorem forwardIntegrand_eq_forwardReprAt (B : FullKineticCoefficient d) (σ₀ : ℝ)
    {φ : ℝ → EvolutionAmbientState d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × EvolutionAmbientState d => φ q.1 q.2))
    (τ : ℝ) (y : EvolutionAmbientState d) :
    forwardIntegrand B σ₀ φ τ y = forwardReprAt B σ₀ (fun q => φ q.1 q.2) (τ, y) := by
  have hd : Differentiable ℝ (fun q : ℝ × EvolutionAmbientState d => φ q.1 q.2) :=
    hφ.differentiable (by simp)
  unfold forwardIntegrand forwardReprAt velocityHessianContraction transportDerivative
  rw [deriv_slice_time _ τ y (hd _)]
  simp only [velocityPartial_velocityPartial_slice hφ τ y,
    positionPartial_slice _ τ y (hd _)]

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
