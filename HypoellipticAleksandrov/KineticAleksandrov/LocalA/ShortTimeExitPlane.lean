module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ShortTimeExitComparison
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Coordinate exponential planes for the ball exit barrier

Each plane uses only a diagonal coefficient bound. No coefficient derivative enters
its backward scalar operator.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open HypoellipticAleksandrov Parabolic Set
open scoped MatrixOrder

/-- A scalar exponential plane in one velocity coordinate and time. -/
def ballExitPlane {d : ℕ} (i : Fin d) (a b c : ℝ) (p : TimeVelocity d) : ℝ :=
  Real.exp (a * p.1 + b * p.2 i + c)

/-- Coordinate exponential planes are smooth at every order. -/
theorem ballExitPlane_contDiff {d : ℕ} (i : Fin d) (a b c : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (ballExitPlane i a b c) := by
  exact ((contDiff_const.mul contDiff_fst).add
    (contDiff_const.mul ((contDiff_apply ℝ ℝ i).comp contDiff_snd)) |>.add
      contDiff_const).exp

/-- The affine exponential has an explicit coordinate gradient. -/
theorem ballExitPlane_gradient {d : ℕ} (i : Fin d) (a b c t : ℝ) (v : PDE.Vec d) :
    PDE.classicalGradient (fun w => ballExitPlane i a b c (t, w)) v =
      (b * ballExitPlane i a b c (t, v)) • PDE.basisVec i := by
  have h := (((hasFDerivAt_apply (𝕜 := ℝ) i v).const_mul b).const_add (a * t)
    |>.add_const c).exp
  ext j
  unfold PDE.classicalGradient ballExitPlane
  rw [h.fderiv]
  by_cases hj : j = i
  · subst j
    simp [PDE.basisVec_apply, smul_eq_mul]
    ring
  · simp [hj, Ne.symm hj, PDE.basisVec_apply, smul_eq_mul]

/-- Its Hessian has a single nonzero diagonal entry. -/
theorem ballExitPlane_hessian {d : ℕ} (i : Fin d) (a b c : ℝ)
    (p : TimeVelocity d) (j k : Fin d) :
    scalarSpatialHessian (ballExitPlane i a b c) p j k =
      if j = i ∧ k = i then b ^ 2 * ballExitPlane i a b c p else 0 := by
  have hg : (fun w => PDE.classicalGradient
      (fun y => ballExitPlane i a b c (p.1, y)) w) =
      fun w => (b * ballExitPlane i a b c (p.1, w)) • PDE.basisVec i :=
    funext (ballExitPlane_gradient i a b c p.1)
  have h := ((((hasFDerivAt_apply (𝕜 := ℝ) i p.2).const_mul b).const_add (a * p.1)
    |>.add_const c).exp.const_mul b).smul_const (PDE.basisVec i)
  unfold scalarSpatialHessian
  rw [hg]
  unfold ballExitPlane
  rw [h.fderiv]
  by_cases hj : j = i
  · subst j
    by_cases hk : k = i
    · subst k
      simp only [PDE.basisVec_apply, ite_true, smul_eq_mul,
        ContinuousLinearMap.smulRight_apply, smul_apply,
        ContinuousLinearMap.proj_apply, Pi.smul_apply, and_self, mul_one]
      ring
    · simp [hk, PDE.basisVec_apply, smul_eq_mul]
  · simp [hj, Ne.symm hj, PDE.basisVec_apply, smul_eq_mul]

/-- The time derivative differentiates the affine time coefficient only. -/
theorem ballExitPlane_time {d : ℕ} (i : Fin d) (a b c : ℝ) (p : TimeVelocity d) :
    scalarTimeDerivative (ballExitPlane i a b c) p = a * ballExitPlane i a b c p := by
  have h := ((((hasDerivAt_id p.1).const_mul a).add_const (b * p.2 i)).add_const c).exp
  simpa only [scalarTimeDerivative, ballExitPlane, id_eq, mul_one, mul_comm] using h.deriv

/-- The backward operator of a plane has no derivatives of the coefficient. -/
theorem ballExitPlane_operator {d : ℕ} (B : CoefficientField d) (i : Fin d)
    (a b c : ℝ) (p : TimeVelocity d) :
    scalarParabolicOperator B 0 (ballExitPlane i a b c) p =
      (a + B p.1 p.2 i i * b ^ 2) * ballExitPlane i a b c p := by
  rw [scalarParabolicOperator_apply, ballExitPlane_time]
  unfold matrixContraction
  simp only [ballExitPlane_hessian, Pi.zero_apply, PDE.vecDot, zero_mul,
    Finset.sum_const_zero, add_zero]
  simp only [mul_ite, mul_zero, ite_and]
  simp only [Finset.sum_ite_irrel, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Finset.sum_const_zero]
  ring

/-- Upper ellipticity controls every diagonal coefficient. -/
theorem ballExit_coefficient_diagonal_upper {d : ℕ} {lam Lam : ℝ}
    (B : CoefficientField d) (hB : SectionTwo.IsSectionTwoCoefficient lam Lam B)
    (t : ℝ) (v : PDE.Vec d) (i : Fin d) : B t v i i ≤ Lam := by
  have h := (hB.2.2.2.2.2 t v).diag_nonneg (i := i)
  simpa only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq,
    smul_eq_mul, mul_one, sub_nonneg] using h

/-- An upper-ellipticity exponential plane is a backward supersolution. -/
theorem ballExitPlane_operator_nonpos {d : ℕ} {lam Lam : ℝ}
    (B : CoefficientField d) (hB : SectionTwo.IsSectionTwoCoefficient lam Lam B)
    (i : Fin d) (b c : ℝ) (p : TimeVelocity d) :
    scalarParabolicOperator B 0 (ballExitPlane i (-Lam * b ^ 2) b c) p ≤ 0 := by
  rw [ballExitPlane_operator]
  have hb := mul_le_mul_of_nonneg_right
    (ballExit_coefficient_diagonal_upper B hB p.1 p.2 i) (sq_nonneg b)
  exact mul_nonpos_of_nonpos_of_nonneg (by linarith only [hb]) (Real.exp_pos _).le

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
