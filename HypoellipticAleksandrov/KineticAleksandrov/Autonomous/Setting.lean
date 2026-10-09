module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.GeometryAPI

/-! # Literal autonomous scalar setting and one-sign velocity intervals

Source: Section 5, `s:autonomous#smooth-setting` and `e:intervals`.
The physical field order is `(s,X,v)`; clock points have field order `(sigma,z,y)`.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous

/-- The existing physical one-dimensional spacetime carrier. -/
abbrev Point := KineticPoint 1

/-- Smooth scalar coefficients with the source pointwise ellipticity bounds. -/
structure SmoothAutonomous (lam Lam : ℝ) where
  a : ℝ → ℝ → ℝ
  smooth : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry a)
  bounds : ∀ x v, lam ≤ a x v ∧ a x v ≤ Lam

/-- A source velocity interval, with ordered finite endpoints. -/
structure Interval where
  lo : ℝ
  hi : ℝ
  ordered : lo < hi

/-- The open interval denoted by the endpoint data. -/
def Interval.carrier (H : Interval) : Set ℝ := Set.Ioo H.lo H.hi

/-- Clock data; the radius restriction is exactly that of `l:clock`. -/
structure Clock where
  vbar : ℝ
  r : ℝ
  nonzero : vbar ≠ 0
  positive : 0 < r
  radius : r ≤ (2 / 3 : ℝ) * |vbar|

/-- Closed core velocity interval. -/
def Clock.core (c : Clock) : Set ℝ :=
  Set.Icc (c.vbar - c.r / 4) (c.vbar + c.r / 4)

/-- Open entrance velocity interval. -/
def Clock.entrance (c : Clock) : Set ℝ :=
  Set.Ioo (c.vbar - c.r / 2) (c.vbar + c.r / 2)

/-- Open active velocity interval. -/
def Clock.active (c : Clock) : Set ℝ :=
  Set.Ioo (c.vbar - 3 * c.r / 4) (c.vbar + 3 * c.r / 4)

/-- Normalized active velocity interval. -/
def normalizedActive : Set ℝ := Set.Ioo (-3 / 4 : ℝ) (3 / 4)

/-- Lift the scalar autonomous coefficient to the full coefficient carrier. -/
def autonomousCoefficient (a : ℝ → ℝ → ℝ) : FullKineticCoefficient 1 :=
  fun _ x v _ _ => a (x 0) (v 0)

/-- Exchange physical position and velocity for the Section Two evolution carrier. -/
def evolutionCoefficient (a : ℝ → ℝ → ℝ) : FullKineticCoefficient 1 :=
  fun _ y z _ _ => a (z 0) (y 0)

/-- Source reflection of an autonomous coefficient. -/
def reflectedAutonomous (a : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun x v => a (-x) v

/-- The scalar forward operator, retaining the kinetic derivative evaluators. -/
def forwardScalarOperator (a : ℝ → ℝ → ℝ) (u : Point → ℝ) (p : Point) : ℝ :=
  Parabolic.kineticTimeDerivative u p +
    p.velocity 0 * Parabolic.kineticPositionGradient u p 0 +
      a (p.position 0) (p.velocity 0) * Parabolic.kineticVelocityHessian u p 0 0

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
