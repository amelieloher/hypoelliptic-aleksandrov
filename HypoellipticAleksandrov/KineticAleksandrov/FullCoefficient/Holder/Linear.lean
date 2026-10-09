module

public import HypoellipticAleksandrov.KineticAleksandrov.Operator
public import HypoellipticAleksandrov.Ambient.MatrixContraction
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonLinear
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonConstant
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonLinear
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Linearity of the full-coefficient backward operator

The backward operator `P_A` with a full coefficient
`A(t,x,v)` is additive and homogeneous on the anisotropic classical class, and so commutes with
differences and negation there. This gives `P_A(ψ - u) = P_A ψ - P_A u`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

open HypoellipticAleksandrov.Parabolic Set

/-- The full backward operator is additive on the existing `C^{1,1,2}` class. -/
theorem backwardOperator_add_of_regular {d : ℕ} {u v : KineticPoint d → ℝ}
    {D : Set (KineticPoint d)} (hu : IsKineticC112On u D) (hv : IsKineticC112On v D)
    (A : FullKineticCoefficient d) {P : KineticPoint d} (hP : P ∈ D) :
    backwardOperator A (fun Q => u Q + v Q) P =
      backwardOperator A u P + backwardOperator A v P := by
  rw [backwardOperator_apply,
    comparison_time_add (hu.timeSlice_differentiableAt hP) (hv.timeSlice_differentiableAt hP),
    show kineticPositionGradient (fun Q => u Q + v Q) P =
      kineticPositionGradient u P + kineticPositionGradient v P from classicalGradient_add
        ((hu.positionSlice_contDiffAt hP).differentiableAt (by norm_num))
        ((hv.positionSlice_contDiffAt hP).differentiableAt (by norm_num)),
    comparison_hessian_add (hu.velocitySlice_contDiffAt hP) (hv.velocitySlice_contDiffAt hP)]
  simp only [HypoellipticAleksandrov.matrixContraction_add_right, PDE.vecDot, Pi.add_apply, mul_add,
    Finset.sum_add_distrib, backwardOperator_apply]
  ring

/-- Scalar multiplication commutes with the full backward operator on `C^{1,1,2}` functions. -/
theorem backwardOperator_const_mul_of_regular {d : ℕ} {u : KineticPoint d → ℝ}
    {D : Set (KineticPoint d)} (hu : IsKineticC112On u D) (c : ℝ)
    (A : FullKineticCoefficient d) {P : KineticPoint d} (hP : P ∈ D) :
    backwardOperator A (fun Q => c * u Q) P = c * backwardOperator A u P := by
  rw [backwardOperator_apply,
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
    smul_eq_mul, backwardOperator_apply]
  rw [mul_sub, mul_add, Finset.mul_sum]
  congr 3
  funext i
  ring

/-- The operator of a difference of `C^{1,1,2}` functions is the difference of the operators. -/
theorem backwardOperator_sub_of_regular {d : ℕ} {u v : KineticPoint d → ℝ}
    {D : Set (KineticPoint d)} (hu : IsKineticC112On u D) (hv : IsKineticC112On v D)
    (A : FullKineticCoefficient d) {P : KineticPoint d} (hP : P ∈ D) :
    backwardOperator A (fun Q => u Q - v Q) P =
      backwardOperator A u P - backwardOperator A v P := by
  have hneg : IsKineticC112On (fun Q => (-1 : ℝ) * v Q) D :=
    comparison_regular_const_mul hv (-1)
  have h1 := backwardOperator_add_of_regular hu hneg A hP
  have h2 := backwardOperator_const_mul_of_regular hv (-1) A hP
  simp only [neg_one_mul, ← sub_eq_add_neg] at h1 h2
  rw [h1, h2]
  ring

/-- The operator of the negative of a `C^{1,1,2}` function is the negative of the operator. -/
theorem backwardOperator_neg_of_regular {d : ℕ} {u : KineticPoint d → ℝ}
    {D : Set (KineticPoint d)} (hu : IsKineticC112On u D)
    (A : FullKineticCoefficient d) {P : KineticPoint d} (hP : P ∈ D) :
    backwardOperator A (fun Q => -u Q) P = -backwardOperator A u P := by
  have h := backwardOperator_const_mul_of_regular hu (-1) A hP
  simpa only [neg_one_mul] using h

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
