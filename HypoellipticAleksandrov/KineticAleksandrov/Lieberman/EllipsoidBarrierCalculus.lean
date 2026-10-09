module

public import HypoellipticAleksandrov.Parabolic.ScalarDirichletData
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import HypoellipticAleksandrov.KineticAleksandrov.Holder.GaussianBarrierVelocity
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonLinear
import Mathlib.Tactic

/-! # Exact spatial jets of the exponential ellipsoid barrier -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Lieberman
open HypoellipticAleksandrov Parabolic
open scoped Matrix BigOperators

/-- The scaled defining quadratic is smooth at every finite order. -/
theorem contDiff_scaled_quadratic {d : ℕ} (Q : PDE.Mat d) (k : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => k * PDE.vecDot x (Q *ᵥ x)) := by
  unfold PDE.vecDot Matrix.mulVec dotProduct
  fun_prop

/-- The native gradient of the scaled symmetric quadratic. -/
theorem gradient_scaled_quadratic {d : ℕ} (Q : PDE.Mat d) (hQ : Q.IsSymm)
    (k : ℝ) (x : PDE.Vec d) :
    PDE.classicalGradient (fun y => k * PDE.vecDot y (Q *ᵥ y)) x =
      (2 * k) • (Q *ᵥ x) := by
  have h := (HasFDerivAt.fun_sum (u := Finset.univ) (fun (i : Fin d) _ =>
    (hasFDerivAt_apply (𝕜 := ℝ) i x).mul
      (HasFDerivAt.fun_sum (u := Finset.univ) (fun (j : Fin d) _ =>
        (hasFDerivAt_apply (𝕜 := ℝ) j x).const_mul (Q i j))))).const_mul k
  ext i
  unfold PDE.classicalGradient
  change fderiv ℝ (fun y => k * ∑ j, y j * ∑ l, Q j l * y l) x
    (PDE.basisVec i) = _
  change HasFDerivAt (fun y : PDE.Vec d => k * ∑ j, y j * ∑ l, Q j l * y l) _ x at h
  rw [h.fderiv]
  simp only [smul_apply, add_apply,
    sum_apply, ContinuousLinearMap.proj_apply,
    PDE.basisVec_apply, smul_eq_mul, Pi.smul_apply]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Finset.sum_add_distrib]
  have he : (∑ j, x j * Q j i) = ∑ j, Q i j * x j := by
    apply Finset.sum_congr rfl
    intro j _
    rw [← hQ.apply i j]
    ring
  rw [he]
  simp only [Matrix.mulVec, dotProduct]
  ring

/-- The native Hessian of the scaled symmetric quadratic. -/
theorem hessian_scaled_quadratic {d : ℕ} (Q : PDE.Mat d) (hQ : Q.IsSymm)
    (k : ℝ) (x : PDE.Vec d) :
    sliceHessian (fun y => k * PDE.vecDot y (Q *ᵥ y)) x = (2 * k) • Q := by
  have hg : PDE.classicalGradient (fun y => k * PDE.vecDot y (Q *ᵥ y)) =
      fun y => (2 * k) • (Q *ᵥ y) := funext (gradient_scaled_quadratic Q hQ k)
  have h := (hasFDerivAt_pi.mpr (fun j : Fin d =>
    (HasFDerivAt.fun_sum (u := Finset.univ) (fun (l : Fin d) _ =>
      (hasFDerivAt_apply (𝕜 := ℝ) l x).const_mul (Q j l))).const_mul (2 * k)))
  unfold sliceHessian
  rw [hg]
  ext i j
  change fderiv ℝ (fun y => fun j => (2 * k) * ∑ l, Q j l * y l) x
    (PDE.basisVec i) j = _
  rw [h.fderiv]
  simp only [ContinuousLinearMap.pi_apply, smul_apply,
    sum_apply, ContinuousLinearMap.proj_apply,
    PDE.basisVec_apply, smul_eq_mul, Matrix.smul_apply]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [hQ.apply i j]

/-- The exponential barrier's exact gradient, including its drift sign. -/
theorem gradient_exp_quadratic {d : ℕ} (Q : PDE.Mat d) (hQ : Q.IsSymm)
    (k C : ℝ) (x : PDE.Vec d) :
    PDE.classicalGradient
      (fun y => C * (Real.exp k - Real.exp (k * PDE.vecDot y (Q *ᵥ y)))) x =
      (-2 * C * k * Real.exp (k * PDE.vecDot x (Q *ᵥ x))) • (Q *ᵥ x) := by
  have hq := (contDiff_scaled_quadratic Q (-k)).differentiable (by norm_num) x
  have he : (fun y => C * (Real.exp k - Real.exp (k * PDE.vecDot y (Q *ᵥ y)))) =
      (fun y => C * Real.exp k + (-C) * Real.exp (-((-k) *
        PDE.vecDot y (Q *ᵥ y)))) := by
    funext y
    simp only [neg_mul, neg_neg]
    ring
  have heDiff : DifferentiableAt ℝ (fun y : PDE.Vec d =>
      (-C) * Real.exp (-((-k) * PDE.vecDot y (Q *ᵥ y)))) x := by
    exact hq.hasFDerivAt.neg.exp.differentiableAt.const_mul (-C)
  have hExDiff : DifferentiableAt ℝ (fun y : PDE.Vec d =>
      Real.exp (-((-k) * PDE.vecDot y (Q *ᵥ y)))) x :=
    hq.hasFDerivAt.neg.exp.differentiableAt
  have hExpGrad := Holder.classicalGradient_exp_neg hq
  rw [he, classicalGradient_add (differentiableAt_const _) heDiff,
    classicalGradient_const_mul (-C) hExDiff, hExpGrad,
    gradient_scaled_quadratic Q hQ]
  ext i
  simp only [PDE.classicalGradient, fderiv_const_apply, zero_apply,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, neg_mul, neg_neg, zero_add]
  ring

/-- The exponential barrier's exact Hessian. -/
theorem hessian_exp_quadratic {d : ℕ} (Q : PDE.Mat d) (hQ : Q.IsSymm)
    (k C : ℝ) (x : PDE.Vec d) (i j : Fin d) :
    sliceHessian
      (fun y => C * (Real.exp k - Real.exp (k * PDE.vecDot y (Q *ᵥ y)))) x i j =
      -C * Real.exp (k * PDE.vecDot x (Q *ᵥ x)) *
        (2 * k * Q i j + 4 * k ^ 2 * (Q *ᵥ x) i * (Q *ᵥ x) j) := by
  have hq : ContDiff ℝ 2 (fun y => (-k) * PDE.vecDot y (Q *ᵥ y)) :=
    (contDiff_scaled_quadratic Q (-k)).of_le (by norm_cast)
  have he : (fun y => C * (Real.exp k - Real.exp (k * PDE.vecDot y (Q *ᵥ y)))) =
      (fun y => C * Real.exp k + (-C) * Real.exp (-((-k) *
        PDE.vecDot y (Q *ᵥ y)))) := by
    funext y
    simp only [neg_mul, neg_neg]
    ring
  have hc : sliceHessian (fun _ : PDE.Vec d => C * Real.exp k) x = 0 := by
    have hg : PDE.classicalGradient (fun _ : PDE.Vec d => C * Real.exp k) =
        fun _ => (0 : PDE.Vec d) := by
      funext y; ext l
      simp only [PDE.classicalGradient, fderiv_const_apply, zero_apply,
        Pi.zero_apply]
    unfold sliceHessian
    rw [hg, fderiv_const_apply]
    rfl
  rw [he, sliceHessian_add contDiffAt_const (contDiffAt_const.mul hq.contDiffAt.neg.exp),
    hc, zero_add, sliceHessian_const_mul _ hq.contDiffAt.neg.exp,
    Matrix.smul_apply, Holder.sliceHessian_exp_neg hq,
    gradient_scaled_quadratic Q hQ, hessian_scaled_quadratic Q hQ]
  simp only [Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, neg_mul, neg_neg]
  ring

/-- Exact backward operator of the exponential ellipsoid barrier. -/
theorem scalarOperator_exp_quadratic {d : ℕ} (Q : PDE.Mat d) (hQ : Q.IsSymm)
    (k C : ℝ) (A : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (z : TimeVelocity d) :
    scalarParabolicZeroOrderOperator A b (fun _ _ => 0)
      (fun p => C * (Real.exp k - Real.exp (k * PDE.vecDot p.2 (Q *ᵥ p.2)))) z =
    -C * Real.exp (k * PDE.vecDot z.2 (Q *ᵥ z.2)) *
      (2 * k * matrixContraction (A z.1 z.2) Q +
       4 * k ^ 2 * PDE.vecDot (Q *ᵥ z.2) (A z.1 z.2 *ᵥ (Q *ᵥ z.2)) +
       2 * k * PDE.vecDot (b z.1 z.2) (Q *ᵥ z.2)) := by
  have ht : scalarTimeDerivative
      (fun p : TimeVelocity d => C *
        (Real.exp k - Real.exp (k * PDE.vecDot p.2 (Q *ᵥ p.2)))) z = 0 := by
    change deriv (fun _ : ℝ => C *
      (Real.exp k - Real.exp (k * PDE.vecDot z.2 (Q *ᵥ z.2)))) z.1 = 0
    exact deriv_const _ _
  rw [scalarParabolicZeroOrderOperator_apply, ht]
  simp only [zero_mul, add_zero, zero_add]
  change matrixContraction (A z.1 z.2)
    (sliceHessian (fun y => C * (Real.exp k - Real.exp (k * PDE.vecDot y (Q *ᵥ y))))
      z.2) + PDE.vecDot (b z.1 z.2)
        (PDE.classicalGradient
          (fun y => C * (Real.exp k - Real.exp (k * PDE.vecDot y (Q *ᵥ y)))) z.2) = _
  rw [gradient_exp_quadratic Q hQ]
  have hh : sliceHessian
      (fun y => C * (Real.exp k - Real.exp (k * PDE.vecDot y (Q *ᵥ y)))) z.2 =
      fun i j => -C * Real.exp (k * PDE.vecDot z.2 (Q *ᵥ z.2)) *
        (2 * k * Q i j + 4 * k ^ 2 * (Q *ᵥ z.2) i * (Q *ᵥ z.2) j) := by
    ext i j
    exact hessian_exp_quadratic Q hQ k C z.2 i j
  rw [hh]
  generalize Q *ᵥ z.2 = p
  generalize Real.exp (k * PDE.vecDot z.2 p) = e
  simp only [matrixContraction, PDE.vecDot, Pi.smul_apply, smul_eq_mul,
    Matrix.mulVec, dotProduct, Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  ring_nf
  simp only [mul_assoc, mul_left_comm, mul_comm]
  ring

end HypoellipticAleksandrov.KineticAleksandrov.Lieberman
