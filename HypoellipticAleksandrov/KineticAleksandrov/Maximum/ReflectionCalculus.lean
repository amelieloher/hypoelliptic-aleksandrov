module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ReflectionAPI

/-! # Slice-calculus identities for the kinetic reflection -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open Set
open HypoellipticAleksandrov.Parabolic

/-- Time differentiation under reflection reverses sign, including total derivative values. -/
theorem kineticTimeDerivative_reflection {d : ℕ} (u : KineticPoint d → ℝ)
    (P : KineticPoint d) :
    kineticTimeDerivative (u ∘ kineticReflection) P =
      -kineticTimeDerivative u (kineticReflection P) := by
  exact deriv_comp_neg (fun r : ℝ => u ⟨r, -P.position, P.velocity⟩) P.time

/-- Position differentiation under reflection reverses sign. -/
theorem kineticPositionGradient_reflection {d : ℕ} (u : KineticPoint d → ℝ)
    (P : KineticPoint d) :
    kineticPositionGradient (u ∘ kineticReflection) P =
      -kineticPositionGradient u (kineticReflection P) := by
  ext i
  let f : PDE.Vec d → ℝ := fun x => u ⟨-P.time,x,P.velocity⟩
  let e := ContinuousLinearEquiv.neg ℝ (M := PDE.Vec d)
  change (fderiv ℝ (f ∘ e) P.position) (PDE.basisVec i) =
    -(fderiv ℝ f (-P.position)) (PDE.basisVec i)
  rw [e.comp_right_fderiv]
  simp [e]

/-- The unchanged velocity coordinate leaves the velocity gradient unchanged. -/
theorem kineticVelocityGradient_reflection {d : ℕ} (u : KineticPoint d → ℝ)
    (P : KineticPoint d) :
    kineticVelocityGradient (u ∘ kineticReflection) P =
      kineticVelocityGradient u (kineticReflection P) := rfl

/-- The unchanged velocity coordinate leaves the velocity Hessian unchanged. -/
theorem kineticVelocityHessian_reflection {d : ℕ} (u : KineticPoint d → ℝ)
    (P : KineticPoint d) :
    kineticVelocityHessian (u ∘ kineticReflection) P =
      kineticVelocityHessian u (kineticReflection P) := rfl

/-- Reflection reverses the operator, including the total derivative evaluator convention. -/
theorem reflectedKineticOperator_reflection {d : ℕ}
    (A : CoefficientField d) (u : KineticPoint d → ℝ) (P : KineticPoint d) :
    forwardKineticOperator (ofTimeVelocityCoefficient (kineticReflectedCoefficient A))
        (u ∘ kineticReflection) P =
      -backwardOperatorOfTimeVelocityCoefficient A u (kineticReflection P) := by
  rw [forwardKineticOperator_apply, backwardOperatorOfTimeVelocityCoefficient_apply,
    kineticTimeDerivative_reflection, kineticPositionGradient_reflection,
    kineticVelocityHessian_reflection]
  simp only [ofTimeVelocityCoefficient, kineticReflectedCoefficient, kineticReflection]
  have hdot : PDE.vecDot P.velocity (-kineticPositionGradient u (kineticReflection P)) =
      -PDE.vecDot P.velocity (kineticPositionGradient u (kineticReflection P)) := by
    simp [PDE.vecDot, Finset.sum_neg_distrib]
  simp only [kineticReflection] at hdot
  rw [hdot]
  ring

/-- Anisotropic regularity is preserved by source reflection on any domain. -/
theorem isKineticC112On_kineticReflection {d : ℕ}
    (u : KineticPoint d → ℝ) (D : Set (KineticPoint d))
    (hu : IsKineticC112On u D) :
    IsKineticC112On (u ∘ kineticReflection) (kineticReflection ⁻¹' D) := by
  rcases hu with ⟨hc,ht,hx,hv,hct,hcx,hcv,hch⟩
  have hR : ContinuousOn (kineticReflection (d := d)) (kineticReflection ⁻¹' D) :=
    (continuous_kineticReflection d).continuousOn
  have hm : MapsTo (kineticReflection (d := d)) (kineticReflection ⁻¹' D) D :=
    fun _ h => h
  refine ⟨hc.comp hR hm, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro P hP
    exact (ht (kineticReflection P) hP).comp P.time differentiableAt_id.neg
  · intro P hP
    change ContDiffAt ℝ 1 (fun x : PDE.Vec d => u ⟨-P.time, -x, P.velocity⟩) P.position
    have hf : ContDiffAt ℝ 1 (fun x : PDE.Vec d => u ⟨-P.time, x, P.velocity⟩)
        (-P.position) := hx (kineticReflection P) hP
    exact hf.comp P.position
      (contDiffAt_id.neg : ContDiffAt ℝ 1 (fun x : PDE.Vec d => -x) P.position)
  · intro P hP
    exact hv (kineticReflection P) hP
  · rw [show kineticTimeDerivative (u ∘ kineticReflection) =
        fun P => -kineticTimeDerivative u (kineticReflection P) from
          funext (kineticTimeDerivative_reflection u)]
    exact (hct.comp hR hm).neg
  · rw [show kineticPositionGradient (u ∘ kineticReflection) =
        fun P => -kineticPositionGradient u (kineticReflection P) from
          funext (kineticPositionGradient_reflection u)]
    exact (hcx.comp hR hm).neg
  · exact hcv.comp hR hm
  · exact hch.comp hR hm

end HypoellipticAleksandrov.KineticAleksandrov
