module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonGreenSupport

/-! # Literal late-time operator vanishing for full C112 infinite strip tests -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Parabolic
open scoped Topology

/-- Vanishing on a late open velocity strip kills every term of the physical kinetic operator. -/
theorem infinite_test_operator_zero_late (a : ℝ → ℝ → ℝ) (H : Interval)
    (u : Point → ℝ) (R : ℝ)
    (hz : ∀ p, R ≤ p.time → p.velocity 0 ∈ H.carrier → u p = 0)
    (p : Point) (ht : R < p.time) (hv : p.velocity 0 ∈ H.carrier) :
    forwardScalarOperator a u p = 0 := by
  have ht0 : kineticTimeDerivative u p = 0 := by
    have hn : ∀ᶠ t in 𝓝 p.time, R < t := isOpen_Ioi.mem_nhds ht
    have heq : (fun t => u ⟨t, p.position, p.velocity⟩) =ᶠ[𝓝 p.time]
        (fun _ => (0 : ℝ)) := hn.mono (fun t ht => hz _ ht.le hv)
    exact heq.deriv_eq.trans (deriv_const _ _)
  have hx0 : kineticPositionGradient u p 0 = 0 := by
    rw [kineticPositionGradient_scalar]
    have heq : (fun x : ℝ => u ⟨p.time, fun _ => x, p.velocity⟩) = fun _ => 0 :=
      funext (fun _ => hz _ ht.le hv)
    rw [heq]
    exact deriv_const _ _
  have hv0 : kineticVelocityHessian u p 0 0 = 0 := by
    rw [kineticVelocityHessian_scalar]
    have hn : ∀ᶠ v in 𝓝 (p.velocity 0), v ∈ H.carrier := isOpen_Ioo.mem_nhds hv
    have heq : (fun v : ℝ => u ⟨p.time, p.position, fun _ => v⟩) =ᶠ[𝓝 (p.velocity 0)]
        (fun _ => (0 : ℝ)) := hn.mono (fun v hv => hz _ ht.le hv)
    refine heq.deriv.deriv_eq.trans ?_
    have hc : deriv (fun _ : ℝ => (0 : ℝ)) = fun _ => 0 := funext (fun _ => deriv_const _ _)
    rw [hc]
    exact deriv_const _ _
  simp only [forwardScalarOperator, ht0, hx0, hv0, mul_zero, add_zero]

/-- Late interior vanishing extends to the closed velocity interval by the actual continuous
  trace. -/
theorem infinite_test_zero_late_closed (H : Interval) (lower R : ℝ) (u : Point → ℝ)
    (hc : ContinuousOn u {p | lower < p.time ∧ p.velocity 0 ∈ Icc H.lo H.hi})
    (hz : ∀ p, R ≤ p.time → p.velocity 0 ∈ H.carrier → u p = 0)
    (p : Point) (hl : lower < p.time) (ht : R ≤ p.time)
    (hv : p.velocity 0 ∈ Icc H.lo H.hi) : u p = 0 := by
  let f : ℝ → ℝ := fun v => u ⟨p.time, p.position, fun _ => v⟩
  have hm : Continuous (fun v : ℝ => (⟨p.time, p.position, fun _ => v⟩ : Point)) := by
    change Continuous ((KineticPoint.homeomorphProd 1).symm ∘
      fun v : ℝ => (p.time, p.position, fun _ : Fin 1 => v))
    exact (KineticPoint.homeomorphProd 1).symm.continuous.comp
      (continuous_const.prodMk (continuous_const.prodMk (continuous_pi (fun _ => continuous_id))))
  have hfc : ContinuousOn f (Icc H.lo H.hi) := by
    apply hc.comp hm.continuousOn
    intro v hv
    exact ⟨hl, hv⟩
  have heq : EqOn f (fun _ => (0 : ℝ)) (Ioo H.lo H.hi) := fun v hv => hz _ ht hv
  have hg := heq.of_subset_closure hfc continuousOn_const Ioo_subset_Icc_self
    (by rw [closure_Ioo H.ordered.ne])
  have h := hg hv
  have hp : (⟨p.time, p.position, fun _ => p.velocity 0⟩ : Point) = p := by
    ext i <;> try rfl
    have hi : i = 0 := Fin.eq_zero i
    subst i
    rfl
  exact (congrArg u hp).symm.trans h

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
