module

public import HypoellipticAleksandrov.Parabolic.KineticClassical

/-!
# Kinetic Aleksandrov operators

This module records the three operator surfaces used by the kinetic
Aleksandrov source.  `backwardOperator` is the full kinetic operator
`∂ₜ + v · ∇ₓ - A : Dᵥ²`, while `transportedForwardOperator` is the forward
operator `∂σ + B : Dᵧ² + b(y) · ∇z`.

For the transported operator, `KineticPoint n` is read as the ordered triple
`(σ, y, z)`: its `position` field is the diffused `y` coordinate and its
`velocity` field is the transported `z` coordinate.  The derivative APIs are
the existing ones on `KineticPoint`; no second point or derivative hierarchy
is introduced.  The W/I domain and structural alternatives belong to a
separate setting conditions, not to these literal operator definitions.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov
open HypoellipticAleksandrov.Parabolic

/-- A full matrix coefficient depending on time, position, and velocity. -/
abbrev FullKineticCoefficient (d : ℕ) :=
  ℝ → PDE.Vec d → PDE.Vec d → PDE.Mat d

/-- Evaluation of a full kinetic coefficient at an explicit kinetic point. -/
def fullKineticCoefficientAt {d : ℕ} (A : FullKineticCoefficient d)
    (z : KineticPoint d) : PDE.Mat d :=
  A z.time z.position z.velocity

@[simp] theorem fullKineticCoefficientAt_apply {d : ℕ}
    (A : FullKineticCoefficient d) (z : KineticPoint d) :
    fullKineticCoefficientAt A z = A z.time z.position z.velocity :=
  rfl

/-- The backward kinetic operator with full coefficient dependence. -/
def backwardOperator {d : ℕ} (A : FullKineticCoefficient d)
    (u : KineticPoint d → ℝ) (z : KineticPoint d) : ℝ :=
  Parabolic.kineticTimeDerivative u z +
    PDE.vecDot z.velocity (Parabolic.kineticPositionGradient u z) -
      matrixContraction (fullKineticCoefficientAt A z)
        (Parabolic.kineticVelocityHessian u z)

@[simp] theorem backwardOperator_apply {d : ℕ}
    (A : FullKineticCoefficient d) (u : KineticPoint d → ℝ)
    (z : KineticPoint d) :
    backwardOperator A u z =
      Parabolic.kineticTimeDerivative u z +
        PDE.vecDot z.velocity (Parabolic.kineticPositionGradient u z) -
          matrixContraction (fullKineticCoefficientAt A z)
            (Parabolic.kineticVelocityHessian u z) :=
  rfl

/-- Lift a time--velocity coefficient without introducing position dependence. -/
def ofTimeVelocityCoefficient {d : ℕ} (A : CoefficientField d) :
    FullKineticCoefficient d :=
  fun t _x v => A t v

@[simp] theorem ofTimeVelocityCoefficient_apply {d : ℕ}
    (A : CoefficientField d) (t : ℝ) (x v : PDE.Vec d) :
    ofTimeVelocityCoefficient A t x v = A t v :=
  rfl

/-- The backward operator specialized to a coefficient independent of position. -/
def backwardOperatorOfTimeVelocityCoefficient {d : ℕ}
    (A : CoefficientField d) (u : KineticPoint d → ℝ)
    (z : KineticPoint d) : ℝ :=
  backwardOperator (ofTimeVelocityCoefficient A) u z

@[simp] theorem backwardOperatorOfTimeVelocityCoefficient_apply {d : ℕ}
    (A : CoefficientField d) (u : KineticPoint d → ℝ)
    (z : KineticPoint d) :
    backwardOperatorOfTimeVelocityCoefficient A u z =
      Parabolic.kineticTimeDerivative u z +
        PDE.vecDot z.velocity (Parabolic.kineticPositionGradient u z) -
          matrixContraction (A z.time z.velocity)
            (Parabolic.kineticVelocityHessian u z) :=
  rfl

/-- The autonomous scalar backward operator on the one-dimensional carrier. -/
def autonomousScalarOperator (a : ℝ → ℝ → ℝ)
    (u : KineticPoint 1 → ℝ) (z : KineticPoint 1) : ℝ :=
  Parabolic.kineticTimeDerivative u z +
    z.velocity 0 * Parabolic.kineticPositionGradient u z 0 -
      a (z.position 0) (z.velocity 0) *
        Parabolic.kineticVelocityHessian u z 0 0

@[simp] theorem autonomousScalarOperator_apply (a : ℝ → ℝ → ℝ)
    (u : KineticPoint 1 → ℝ) (z : KineticPoint 1) :
    autonomousScalarOperator a u z =
      Parabolic.kineticTimeDerivative u z +
        z.velocity 0 * Parabolic.kineticPositionGradient u z 0 -
          a (z.position 0) (z.velocity 0) *
            Parabolic.kineticVelocityHessian u z 0 0 :=
  rfl

/-- The Hessian in the diffused `y` coordinate of a transported point. -/
def diffusedHessian {n : ℕ} (u : KineticPoint n → ℝ)
    (z : KineticPoint n) : PDE.Mat n :=
  fun i j =>
    (fderiv ℝ (fun y : PDE.Vec n =>
      Parabolic.kineticPositionGradient u ⟨z.time, y, z.velocity⟩)
      z.position (PDE.basisVec i)) j

@[simp] theorem diffusedHessian_apply {n : ℕ}
    (u : KineticPoint n → ℝ) (z : KineticPoint n) (i j : Fin n) :
    diffusedHessian u z i j =
      (fderiv ℝ (fun y : PDE.Vec n =>
        Parabolic.kineticPositionGradient u ⟨z.time, y, z.velocity⟩)
        z.position (PDE.basisVec i)) j :=
  rfl

/-- The forward operator with diffusion in `y` and transport in `z`. -/
def transportedForwardOperator {n : ℕ} (B : FullKineticCoefficient n)
    (b : PDE.Vec n → PDE.Vec n) (u : KineticPoint n → ℝ)
    (z : KineticPoint n) : ℝ :=
  Parabolic.kineticTimeDerivative u z +
    matrixContraction (fullKineticCoefficientAt B z) (diffusedHessian u z) +
      PDE.vecDot (b z.position) (Parabolic.kineticVelocityGradient u z)

@[simp] theorem transportedForwardOperator_apply {n : ℕ}
    (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n)
    (u : KineticPoint n → ℝ) (z : KineticPoint n) :
    transportedForwardOperator B b u z =
      Parabolic.kineticTimeDerivative u z +
        matrixContraction (fullKineticCoefficientAt B z) (diffusedHessian u z) +
          PDE.vecDot (b z.position) (Parabolic.kineticVelocityGradient u z) :=
  rfl

/-- Lift a coefficient independent of the transported `z` coordinate. -/
def zIndependentCoefficient {n : ℕ} (B : CoefficientField n) :
    FullKineticCoefficient n :=
  fun sigma y _z => B sigma y

@[simp] theorem zIndependentCoefficient_apply {n : ℕ}
    (B : CoefficientField n) (sigma : ℝ) (y z : PDE.Vec n) :
    zIndependentCoefficient B sigma y z = B sigma y :=
  rfl

/-- The transported operator specialized to a z-independent coefficient. -/
def transportedForwardOperatorOfTimeDiffusedCoefficient {n : ℕ}
    (B : CoefficientField n) (b : PDE.Vec n → PDE.Vec n)
    (u : KineticPoint n → ℝ) (z : KineticPoint n) : ℝ :=
  transportedForwardOperator (zIndependentCoefficient B) b u z

@[simp] theorem transportedForwardOperatorOfTimeDiffusedCoefficient_apply
    {n : ℕ} (B : CoefficientField n) (b : PDE.Vec n → PDE.Vec n)
    (u : KineticPoint n → ℝ) (z : KineticPoint n) :
    transportedForwardOperatorOfTimeDiffusedCoefficient B b u z =
      Parabolic.kineticTimeDerivative u z +
        matrixContraction (B z.time z.position) (diffusedHessian u z) +
          PDE.vecDot (b z.position) (Parabolic.kineticVelocityGradient u z) :=
  rfl

end HypoellipticAleksandrov.KineticAleksandrov
