module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ShortTimeExitPlane
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierCollar

/-! # Finite linearity of the scalar operator on smooth barriers -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open HypoellipticAleksandrov Parabolic Set

/-- The zero-drift scalar operator is additive on smooth functions. -/
theorem ballExit_operator_add {d : ℕ} (B : CoefficientField d)
    (f g : TimeVelocity d → ℝ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (p : TimeVelocity d) :
    scalarParabolicOperator B 0 (fun q => f q + g q) p =
      scalarParabolicOperator B 0 f p + scalarParabolicOperator B 0 g p := by
  have hft : DifferentiableAt ℝ (fun t => f (t, p.2)) p.1 :=
    (hf.comp (contDiff_id.prodMk contDiff_const)).differentiable (by norm_num) p.1
  have hgt : DifferentiableAt ℝ (fun t => g (t, p.2)) p.1 :=
    (hg.comp (contDiff_id.prodMk contDiff_const)).differentiable (by norm_num) p.1
  have hfy : ContDiffAt ℝ 2 (fun w => f (p.1, w)) p.2 :=
    (hf.comp (contDiff_const.prodMk contDiff_id)).contDiffAt
  have hgy : ContDiffAt ℝ 2 (fun w => g (p.1, w)) p.2 :=
    (hg.comp (contDiff_const.prodMk contDiff_id)).contDiffAt
  have hh : scalarSpatialHessian (fun q => f q + g q) p =
      scalarSpatialHessian f p + scalarSpatialHessian g p := sliceHessian_add hfy hgy
  unfold scalarParabolicOperator scalarTimeDerivative
  rw [deriv_fun_add hft hgt, hh]
  simp only [matrixContraction, Matrix.add_apply, mul_add, Finset.sum_add_distrib,
    Pi.zero_apply, PDE.vecDot, zero_mul, Finset.sum_const_zero, add_zero]
  ring

/-- Constant scalar functions have zero operator. -/
theorem ballExit_operator_const {d : ℕ} (B : CoefficientField d) (c : ℝ)
    (p : TimeVelocity d) : scalarParabolicOperator B 0 (fun _ => c) p = 0 := by
  unfold scalarParabolicOperator scalarTimeDerivative
  have hh : scalarSpatialHessian (fun _ : TimeVelocity d => c) p = 0 :=
    sliceHessian_const c p.2
  rw [deriv_const, hh]
  simp only [matrixContraction, Matrix.zero_apply, mul_zero, Finset.sum_const_zero,
    Pi.zero_apply, PDE.vecDot, zero_mul, add_zero]

/-- Scalar multiplication commutes with the zero-drift scalar operator. -/
theorem ballExit_operator_mul {d : ℕ} (B : CoefficientField d) (c : ℝ)
    (f : TimeVelocity d → ℝ) (hf : ContDiff ℝ 2 f) (p : TimeVelocity d) :
    scalarParabolicOperator B 0 (fun q => c * f q) p =
      c * scalarParabolicOperator B 0 f p := by
  have hft : DifferentiableAt ℝ (fun t => f (t, p.2)) p.1 :=
    (hf.comp (contDiff_id.prodMk contDiff_const)).differentiable (by norm_num) p.1
  have hfy : ContDiffAt ℝ 2 (fun w => f (p.1, w)) p.2 :=
    (hf.comp (contDiff_const.prodMk contDiff_id)).contDiffAt
  unfold scalarParabolicOperator scalarTimeDerivative
  have hh : scalarSpatialHessian (fun q => c * f q) p =
      c • scalarSpatialHessian f p := sliceHessian_const_mul c hfy
  rw [deriv_const_mul c hft, hh]
  simp only [matrixContraction, Matrix.smul_apply, smul_eq_mul,
    Pi.zero_apply, PDE.vecDot, zero_mul, Finset.sum_const_zero, add_zero]
  simp_rw [show ∀ a b : ℝ, a * (c * b) = c * (a * b) from fun a b => by ring]
  simp_rw [← Finset.mul_sum]
  ring

/-- The zero-drift scalar operator commutes with finite smooth sums. -/
theorem ballExit_operator_sum {d : ℕ} {ι : Type*} (B : CoefficientField d)
    (s : Finset ι) (f : ι → TimeVelocity d → ℝ)
    (hf : ∀ i ∈ s, ContDiff ℝ 2 (f i)) (p : TimeVelocity d) :
    scalarParabolicOperator B 0 (fun q => ∑ i ∈ s, f i q) p =
      ∑ i ∈ s, scalarParabolicOperator B 0 (f i) p := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using ballExit_operator_const B 0 p
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [ballExit_operator_add B (f i) (fun q => ∑ j ∈ s, f j q)
      (hf i (Finset.mem_insert_self _ _))
      (ContDiff.sum (fun j hj => hf j (Finset.mem_insert_of_mem hj)))]
    rw [ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
