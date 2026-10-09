module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockGreenTestCoordinates

/-! # Literal operator vanishing on a late zero half-space -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Parabolic
open SectionTwo TheoremA Evolution
open scoped Topology

/-- A native function zero on a late half-space has zero transported operator strictly inside it. -/
theorem clock_transport_operator_zero_after
    (B : FullKineticCoefficient 1) (b : PDE.Vec 1 → PDE.Vec 1) (u : Point → ℝ)
    (R : ℝ) (hz : ∀ p, R ≤ p.time → u p = 0) (p : Point) (hp : R < p.time) :
    transportedForwardOperator B b u p = 0 := by
  have ht : kineticTimeDerivative u p = 0 := by
    have hn : ∀ᶠ t in 𝓝 p.time, R < t := isOpen_Ioi.mem_nhds hp
    have heq : (fun t => u ⟨t, p.position, p.velocity⟩) =ᶠ[𝓝 p.time]
        (fun _ => (0 : ℝ)) := hn.mono (fun t ht => hz _ ht.le)
    change deriv (fun t => u ⟨t, p.position, p.velocity⟩) p.time = 0
    rw [heq.deriv_eq]
    exact deriv_const _ _
  have hgrad : (fun y : PDE.Vec 1 => kineticPositionGradient u ⟨p.time, y, p.velocity⟩) =
      fun _ => 0 := by
    funext y
    ext i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    rw [kineticPositionGradient_scalar]
    have heq : (fun v : ℝ => u ⟨p.time, fun _ => v, p.velocity⟩) = fun _ => 0 :=
      funext (fun _ => hz _ hp.le)
    rw [heq]
    exact deriv_const _ _
  have hv : diffusedHessian u p 0 0 = 0 := by
    rw [diffusedHessian, hgrad, fderiv_const_apply]
    rfl
  have hx : kineticVelocityGradient u p 0 = 0 := by
    rw [kineticVelocityGradient_scalar]
    have heq : (fun z : ℝ => u ⟨p.time, p.position, fun _ => z⟩) = fun _ => 0 :=
      funext (fun _ => hz _ hp.le)
    rw [heq]
    exact deriv_const _ _
  simp only [transportedForwardOperator_apply, matrixContraction, Fin.sum_univ_one,
    PDE.vecDot, ht, hv, hx, mul_zero, add_zero]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
