module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitConeTransition

/-! # Exact kinetic calculus for smooth functions of affine transport coordinates -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Parabolic
open SectionTwo TheoremA Evolution

/-- The affine transport coordinate used to detect finite-speed violations. -/
def reconstructionConeCoordinate (alpha beta gamma : ℝ) (p : Point) : ℝ :=
  alpha * p.time + beta * p.position 0 + gamma

/-- Composition with the cone transition is a genuine globally smooth physical test. -/
theorem reconstructionConeProbe_smooth (alpha beta gamma : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) ((expNegInvGlue ∘ reconstructionConeCoordinate alpha beta gamma) ∘
      reconstructionPhysicalHomeomorph) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun x => expNegInvGlue
    (alpha * Evolution.timeCoord 1 x + beta * transportedCoord 1 x 0 + gamma))
  apply expNegInvGlue.contDiff.comp
  exact ((contDiff_const.mul (Evolution.timeCoord 1).contDiff).add
    (contDiff_const.mul ((contDiff_apply ℝ ℝ (0 : Fin 1)).comp
      (transportedCoord 1).contDiff))).add contDiff_const

/-- A pure transport-coordinate probe has no velocity Hessian contribution. -/
theorem reconstructionConeProbe_operator (a : ℝ → ℝ → ℝ) (alpha beta gamma : ℝ)
    (p : Point) :
    forwardScalarOperator a (expNegInvGlue ∘ reconstructionConeCoordinate alpha beta gamma) p =
      (alpha + p.velocity 0 * beta) *
        deriv expNegInvGlue (reconstructionConeCoordinate alpha beta gamma p) := by
  have hd (x : ℝ) :=
    ((expNegInvGlue.contDiff : ContDiff ℝ (⊤ : ℕ∞) expNegInvGlue).differentiable (by simp) x)
  have ht : kineticTimeDerivative
      (expNegInvGlue ∘ reconstructionConeCoordinate alpha beta gamma) p =
      deriv expNegInvGlue (reconstructionConeCoordinate alpha beta gamma p) * alpha := by
    have hh := (hd _).hasDerivAt.comp p.time
      ((((hasDerivAt_id p.time).const_mul alpha).add_const (beta * p.position 0)).add_const gamma)
    simpa only [kineticTimeDerivative, reconstructionConeCoordinate, Function.comp_apply,
      id_eq, mul_one] using! hh.deriv
  have hx : kineticPositionGradient
      (expNegInvGlue ∘ reconstructionConeCoordinate alpha beta gamma) p 0 =
      deriv expNegInvGlue (reconstructionConeCoordinate alpha beta gamma p) * beta := by
    rw [kineticPositionGradient_scalar]
    have hh := (hd _).hasDerivAt.comp (p.position 0)
      ((((hasDerivAt_id (p.position 0)).const_mul beta).const_add (alpha * p.time)).add_const gamma)
    simpa only [reconstructionConeCoordinate, Function.comp_apply, id_eq, mul_one] using! hh.deriv
  have hv : kineticVelocityHessian
      (expNegInvGlue ∘ reconstructionConeCoordinate alpha beta gamma) p 0 0 = 0 := by
    rw [kineticVelocityHessian_scalar]
    change deriv (deriv (fun _ : ℝ => expNegInvGlue
      (alpha * p.time + beta * p.position 0 + gamma))) (p.velocity 0) = 0
    have hh : deriv (fun _ : ℝ => expNegInvGlue
        (alpha * p.time + beta * p.position 0 + gamma)) = fun _ => 0 :=
      funext (fun x => deriv_const x _)
    rw [hh]
    exact deriv_const _ _
  unfold forwardScalarOperator
  rw [ht, hx, hv]
  ring

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
