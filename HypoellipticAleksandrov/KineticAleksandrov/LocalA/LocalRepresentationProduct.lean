module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.LocalRepresentationCutoff
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonLinear
public import HypoellipticAleksandrov.Parabolic.ScalarClassical

/-! # The classical residual of a multiplier independent of velocity -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set Parabolic

/-- Multiplication by a smooth time-position function creates only a transport defect. -/
theorem forward_operator_position_multiplier {d : ℕ}
    (A : FullKineticCoefficient d) (η : TimeVelocity d → ℝ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    {u : KineticPoint d → ℝ} {D : Set (KineticPoint d)}
    (hu : IsKineticC112On u D) {P : KineticPoint d} (hP : P ∈ D) :
    forwardKineticOperator A (fun Q => η (Q.time, Q.position) * u Q) P =
      η (P.time, P.position) * forwardKineticOperator A u P +
        (scalarTimeDerivative η (P.time, P.position) +
          PDE.vecDot P.velocity (scalarSpatialGradient η (P.time, P.position))) * u P := by
  have hηt : DifferentiableAt ℝ (fun t => η (t, P.position)) P.time :=
    (hη.comp (contDiff_id.prodMk contDiff_const)).differentiable
      (by norm_num) |>.differentiableAt
  have hηx : DifferentiableAt ℝ (fun x => η (P.time, x)) P.position :=
    (hη.comp (contDiff_const.prodMk contDiff_id)).differentiable
      (by norm_num) |>.differentiableAt
  have hut := hu.timeSlice_differentiableAt hP
  have hux := (hu.positionSlice_contDiffAt hP).differentiableAt (by norm_num)
  have ht : kineticTimeDerivative (fun Q => η (Q.time, Q.position) * u Q) P =
      scalarTimeDerivative η (P.time, P.position) * u P +
        η (P.time, P.position) * kineticTimeDerivative u P := deriv_mul hηt hut
  have hx : kineticPositionGradient (fun Q => η (Q.time, Q.position) * u Q) P =
      η (P.time, P.position) • kineticPositionGradient u P +
        u P • scalarSpatialGradient η (P.time, P.position) := by
    ext i
    change fderiv ℝ ((fun x => η (P.time, x)) * fun x => u ⟨P.time, x, P.velocity⟩)
      P.position (PDE.basisVec i) = _
    rw [fderiv_mul hηx hux]
    simp only [add_apply, smul_apply,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, kineticPositionGradient,
      scalarSpatialGradient, PDE.classicalGradient_apply]
  have hv : kineticVelocityHessian (fun Q => η (Q.time, Q.position) * u Q) P =
      η (P.time, P.position) • kineticVelocityHessian u P := by
    simp only [kineticVelocityHessian_eq_sliceHessian]
    exact sliceHessian_const_mul _ (hu.velocitySlice_contDiffAt hP)
  rw [forwardKineticOperator_apply, ht, hx, hv, matrixContraction_smul_right,
    forwardKineticOperator_apply]
  simp only [PDE.vecDot, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
    Finset.sum_add_distrib]
  have ha : (∑ i, P.velocity i *
      (η (P.time, P.position) * kineticPositionGradient u P i)) =
      η (P.time, P.position) * ∑ i, P.velocity i * kineticPositionGradient u P i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hb : (∑ i, P.velocity i *
      (u P * scalarSpatialGradient η (P.time, P.position) i)) =
      u P * ∑ i, P.velocity i * scalarSpatialGradient η (P.time, P.position) i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [ha, hb]
  ring

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
