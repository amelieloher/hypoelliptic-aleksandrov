module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.GeometryAPI
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonLinear
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! # Linearity on the source anisotropic classical class -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov.Parabolic Set

/-- Additivity of the kinetic time derivative under its slice differentiability. -/
theorem comparison_time_add {d : ℕ} {u v : KineticPoint d → ℝ} {P : KineticPoint d}
    (hu : DifferentiableAt ℝ (fun t => u ⟨t,P.position,P.velocity⟩) P.time)
    (hv : DifferentiableAt ℝ (fun t => v ⟨t,P.position,P.velocity⟩) P.time) :
    kineticTimeDerivative (fun Q => u Q + v Q) P =
      kineticTimeDerivative u P + kineticTimeDerivative v P := deriv_add hu hv

/-- Additivity of the kinetic velocity Hessian with only velocity-slice regularity. -/
theorem comparison_hessian_add {d : ℕ} {u v : KineticPoint d → ℝ} {P : KineticPoint d}
    (hu : ContDiffAt ℝ 2 (fun w => u ⟨P.time,P.position,w⟩) P.velocity)
    (hv : ContDiffAt ℝ 2 (fun w => v ⟨P.time,P.position,w⟩) P.velocity) :
    kineticVelocityHessian (fun Q => u Q + v Q) P =
      kineticVelocityHessian u P + kineticVelocityHessian v P := by
  simp only [kineticVelocityHessian_eq_sliceHessian]
  exact sliceHessian_add hu hv

/-- Sums preserve the exact anisotropic kinetic classical class. -/
theorem comparison_regular_add {d : ℕ} {u v : KineticPoint d → ℝ}
    {D : Set (KineticPoint d)} (hu : IsKineticC112On u D) (hv : IsKineticC112On v D) :
    IsKineticC112On (fun P => u P + v P) D := by
  refine ⟨hu.continuousOn.add hv.continuousOn,fun P hP =>
    (hu.timeSlice_differentiableAt hP).add (hv.timeSlice_differentiableAt hP),
    fun P hP => (hu.positionSlice_contDiffAt hP).add (hv.positionSlice_contDiffAt hP),
    fun P hP => (hu.velocitySlice_contDiffAt hP).add (hv.velocitySlice_contDiffAt hP),
    ?_,?_,?_,?_⟩
  · apply (hu.continuousOn_kineticTimeDerivative.add hv.continuousOn_kineticTimeDerivative).congr
    intro P hP
    exact (comparison_time_add (hu.timeSlice_differentiableAt hP)
      (hv.timeSlice_differentiableAt hP))
  · apply (hu.continuousOn_kineticPositionGradient.add
      hv.continuousOn_kineticPositionGradient).congr
    intro P hP
    exact (classicalGradient_add
      ((hu.positionSlice_contDiffAt hP).differentiableAt (by norm_num))
      ((hv.positionSlice_contDiffAt hP).differentiableAt (by norm_num)))
  · apply (hu.continuousOn_kineticVelocityGradient.add
      hv.continuousOn_kineticVelocityGradient).congr
    intro P hP
    exact (classicalGradient_add
      ((hu.velocitySlice_contDiffAt hP).differentiableAt (by norm_num))
      ((hv.velocitySlice_contDiffAt hP).differentiableAt (by norm_num)))
  · apply (hu.continuousOn_kineticVelocityHessian.add hv.continuousOn_kineticVelocityHessian).congr
    intro P hP
    exact (comparison_hessian_add (hu.velocitySlice_contDiffAt hP)
      (hv.velocitySlice_contDiffAt hP))

/-- Scalar multiplication preserves the exact anisotropic kinetic classical class. -/
theorem comparison_regular_const_mul {d : ℕ} {u : KineticPoint d → ℝ}
    {D : Set (KineticPoint d)} (hu : IsKineticC112On u D) (c : ℝ) :
    IsKineticC112On (fun P => c * u P) D := by
  refine ⟨continuousOn_const.mul hu.continuousOn,
    fun P hP => (hu.timeSlice_differentiableAt hP).const_mul c,
    fun P hP => contDiffAt_const.mul (hu.positionSlice_contDiffAt hP),
    fun P hP => contDiffAt_const.mul (hu.velocitySlice_contDiffAt hP),?_,?_,?_,?_⟩
  · apply ((continuousOn_const (c := c)).mul hu.continuousOn_kineticTimeDerivative).congr
    intro P hP
    exact (deriv_const_mul c (hu.timeSlice_differentiableAt hP))
  · apply ((continuousOn_const (c := c)).smul hu.continuousOn_kineticPositionGradient).congr
    intro P hP
    exact (classicalGradient_const_mul c
      ((hu.positionSlice_contDiffAt hP).differentiableAt (by norm_num)))
  · apply ((continuousOn_const (c := c)).smul hu.continuousOn_kineticVelocityGradient).congr
    intro P hP
    exact (classicalGradient_const_mul c
      ((hu.velocitySlice_contDiffAt hP).differentiableAt (by norm_num)))
  · apply ((continuousOn_const (c := c)).smul hu.continuousOn_kineticVelocityHessian).congr
    intro P hP
    simp only [kineticVelocityHessian_eq_sliceHessian]
    exact (sliceHessian_const_mul c (hu.velocitySlice_contDiffAt hP))

/-- The general forward operator is additive on its source classical class. -/
theorem comparison_forwardOperator_add {d : ℕ} {u v : KineticPoint d → ℝ}
    {D : Set (KineticPoint d)} (hu : IsKineticC112On u D) (hv : IsKineticC112On v D)
    (A : FullKineticCoefficient d) {P : KineticPoint d} (hP : P ∈ D) :
    forwardKineticOperator A (fun Q => u Q + v Q) P =
      forwardKineticOperator A u P + forwardKineticOperator A v P := by
  rw [forwardKineticOperator_apply,
    comparison_time_add (hu.timeSlice_differentiableAt hP) (hv.timeSlice_differentiableAt hP),
    show kineticPositionGradient (fun Q => u Q + v Q) P =
      kineticPositionGradient u P + kineticPositionGradient v P from classicalGradient_add
        ((hu.positionSlice_contDiffAt hP).differentiableAt (by norm_num))
        ((hv.positionSlice_contDiffAt hP).differentiableAt (by norm_num)),
    comparison_hessian_add (hu.velocitySlice_contDiffAt hP) (hv.velocitySlice_contDiffAt hP)]
  simp only [HypoellipticAleksandrov.matrixContraction_add_right, PDE.vecDot, Pi.add_apply, mul_add,
    Finset.sum_add_distrib, forwardKineticOperator_apply]
  ring

/-- The general forward operator is homogeneous on its source classical class. -/
theorem comparison_forwardOperator_const_mul {d : ℕ} {u : KineticPoint d → ℝ}
    {D : Set (KineticPoint d)} (hu : IsKineticC112On u D) (c : ℝ)
    (A : FullKineticCoefficient d) {P : KineticPoint d} (hP : P ∈ D) :
    forwardKineticOperator A (fun Q => c * u Q) P = c * forwardKineticOperator A u P := by
  rw [forwardKineticOperator_apply,
    show kineticTimeDerivative (fun Q => c * u Q) P = c * kineticTimeDerivative u P from
      deriv_const_mul c (hu.timeSlice_differentiableAt hP),
    show kineticPositionGradient (fun Q => c * u Q) P = c • kineticPositionGradient u P from
      classicalGradient_const_mul c
        ((hu.positionSlice_contDiffAt hP).differentiableAt (by norm_num))]
  have hh : kineticVelocityHessian (fun Q => c * u Q) P = c • kineticVelocityHessian u P := by
    simp only [kineticVelocityHessian_eq_sliceHessian]
    exact sliceHessian_const_mul c (hu.velocitySlice_contDiffAt hP)
  rw [hh]
  simp only [HypoellipticAleksandrov.matrixContraction_smul_right, PDE.vecDot, Pi.smul_apply,
    smul_eq_mul, forwardKineticOperator_apply]
  rw [show (∑ i, P.velocity i * (c * kineticPositionGradient u P i)) =
    c * ∑ i, P.velocity i * kineticPositionGradient u P i by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring]
  ring

end HypoellipticAleksandrov.KineticAleksandrov
