module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonCalculus

/-! # Locality of the viscous kinetic operator

Equality near a point preserves every literal slice derivative in the operator.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Filter
open scoped Topology

/-- Equal scalar germs have equal classical gradient germs. -/
theorem pastGluing_gradient_germ {n : ℕ} {u v : PDE.Vec n → ℝ} {x : PDE.Vec n}
    (h : u =ᶠ[𝓝 x] v) : PDE.classicalGradient u =ᶠ[𝓝 x] PDE.classicalGradient v := by
  filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
  funext i
  exact congrArg (fun L : PDE.Vec n →L[ℝ] ℝ => L (PDE.basisVec i)) hy

/-- A scalar germ determines its gradient and differentiated-gradient values. -/
theorem pastGluing_gradient_hessian_eq {n : ℕ} {u v : PDE.Vec n → ℝ} {x : PDE.Vec n}
    (h : u =ᶠ[𝓝 x] v) :
    PDE.classicalGradient u x = PDE.classicalGradient v x ∧
      fderiv ℝ (PDE.classicalGradient u) x = fderiv ℝ (PDE.classicalGradient v) x :=
  ⟨(pastGluing_gradient_germ h).eq_of_nhds, (pastGluing_gradient_germ h).fderiv_eq⟩

/-- Equal kinetic germs have equal viscous operator values, without regularity assumptions. -/
theorem viscousTransportedOperator_congr_germ {n : ℕ}
    (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n) (ε : ℝ)
    {u v : KineticPoint n → ℝ} {p : KineticPoint n} (h : u =ᶠ[𝓝 p] v) :
    viscousTransportedOperator B b ε u p = viscousTransportedOperator B b ε v p := by
  have ht : (fun s => u ⟨s, p.position, p.velocity⟩) =ᶠ[𝓝 p.time]
      (fun s => v ⟨s, p.position, p.velocity⟩) :=
    h.comp_tendsto ((KineticPoint.continuous_mk continuous_id continuous_const
      continuous_const).tendsto p.time)
  have hy : (fun y => u ⟨p.time, y, p.velocity⟩) =ᶠ[𝓝 p.position]
      (fun y => v ⟨p.time, y, p.velocity⟩) :=
    h.comp_tendsto ((KineticPoint.continuous_mk continuous_const continuous_id
      continuous_const).tendsto p.position)
  have hz : (fun z => u ⟨p.time, p.position, z⟩) =ᶠ[𝓝 p.velocity]
      (fun z => v ⟨p.time, p.position, z⟩) :=
    h.comp_tendsto ((KineticPoint.continuous_mk continuous_const continuous_const
      continuous_id).tendsto p.velocity)
  have ey := pastGluing_gradient_hessian_eq hy
  have ez := pastGluing_gradient_hessian_eq hz
  have hd : diffusedHessian u p = diffusedHessian v p := by
    ext i j
    simp only [diffusedHessian_apply, kineticPositionGradient]
    exact congrArg (fun L : PDE.Vec n →L[ℝ] PDE.Vec n => L (PDE.basisVec i) j) ey.2
  simp only [viscousTransportedOperator, transportedForwardOperator, kineticTimeDerivative,
    kineticVelocityGradient, kineticVelocityHessian, ht.deriv_eq, hd, ez.1, ez.2]

end HypoellipticAleksandrov.KineticAleksandrov
