module

public import HypoellipticAleksandrov.Parabolic.ScalarDirichletData
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonRadial
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonGrowth
import HypoellipticAleksandrov.Parabolic.C2ToScalarC12

/-! # Quadratic barriers on the actual Euclidean spatial ball

The trace of the lower ellipticity bound gives the normalized source-one barrier.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Set Matrix KineticAleksandrov
open scoped MatrixOrder Matrix.Norms.Elementwise

/-- The source-M quadratic barrier in the native Euclidean geometry. -/
def sourceBallBarrier {d : ℕ} (v₀ : PDE.Vec d) (r lam M : ℝ) (y : PDE.Vec d) : ℝ :=
  M * (r ^ 2 - PDE.vecNormSq (y - v₀)) / (2 * (d : ℝ) * lam)

/-- The polynomial source barrier is smooth. -/
theorem contDiff_sourceBallBarrier {d : ℕ} (v₀ : PDE.Vec d) (r lam M : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (sourceBallBarrier v₀ r lam M) :=
  (contDiff_const.mul (contDiff_const.sub
    (PDE.contDiff_vecNormSq.comp (contDiff_id.sub contDiff_const)))).div_const _

/-- The source barrier is nonnegative on the closed Euclidean ball. -/
theorem sourceBallBarrier_nonneg {d : ℕ} (v₀ : PDE.Vec d) (r lam M : ℝ)
    (hlam : 0 < lam) (hM : 0 ≤ M) {y : PDE.Vec d}
    (hy : y ∈ closure (PDE.euclideanBall v₀ r)) :
    0 ≤ sourceBallBarrier v₀ r lam M y := by
  have hs : closure (PDE.euclideanBall v₀ r) ⊆
      {y | PDE.vecNormSq (y - v₀) ≤ r ^ 2} := by
    apply closure_minimal
    · intro y hy
      exact (show PDE.vecNormSq (y - v₀) < r ^ 2 from hy).le
    · exact isClosed_le (contDiff_vecNormSq_sub v₀).continuous continuous_const
  exact div_nonneg (mul_nonneg hM (sub_nonneg.mpr (hs hy)))
    (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d)) hlam.le)

/-- The source barrier has zero trace on the Euclidean ball frontier. -/
theorem sourceBallBarrier_zero_frontier {d : ℕ} (v₀ : PDE.Vec d) (r lam M : ℝ)
    {y : PDE.Vec d} (hy : y ∈ frontier (PDE.euclideanBall v₀ r)) :
    sourceBallBarrier v₀ r lam M y = 0 := by
  rw [(PDE.isOpen_euclideanBall v₀ r).frontier_eq] at hy
  have hs : closure (PDE.euclideanBall v₀ r) ⊆
      {y | PDE.vecNormSq (y - v₀) ≤ r ^ 2} := by
    apply closure_minimal
    · intro y hy
      exact (show PDE.vecNormSq (y - v₀) < r ^ 2 from hy).le
    · exact isClosed_le (contDiff_vecNormSq_sub v₀).continuous continuous_const
  have heq : PDE.vecNormSq (y - v₀) = r ^ 2 :=
    le_antisymm (hs hy.1) (le_of_not_gt hy.2)
  simp only [sourceBallBarrier, heq, sub_self, mul_zero, zero_div]

/-- The stationary quadratic has the literal negative trace forcing. -/
theorem scalarOperator_sourceBallBarrier {d : ℕ} (v₀ : PDE.Vec d) (r lam M : ℝ)
    (A : CoefficientField d) (z : TimeVelocity d) :
    scalarParabolicZeroOrderOperator A (fun _ _ => 0) (fun _ _ => 0)
      (fun z => sourceBallBarrier v₀ r lam M z.2) z =
      -(2 * M * (A z.1 z.2).trace) / (2 * (d : ℝ) * lam) := by
  let Ψ : ℝ → ℝ := fun s => M * (r ^ 2 - s) / (2 * (d : ℝ) * lam)
  have hΨ : ContDiff ℝ 2 Ψ :=
    (contDiff_const.mul (contDiff_const.sub contDiff_id)).div_const _
  have hd (s : ℝ) : deriv Ψ s = -M / (2 * (d : ℝ) * lam) := by
    simpa only [zero_sub, mul_neg, neg_div, mul_one, Pi.sub_def, id_eq] using
      (((hasDerivAt_const s (r ^ 2)).sub (hasDerivAt_id s)).const_mul M
        |>.div_const (2 * (d : ℝ) * lam)).deriv
  have hdd (s : ℝ) : deriv (deriv Ψ) s = 0 := by
    rw [show deriv Ψ = fun _ => -M / (2 * (d : ℝ) * lam) from funext hd]
    exact deriv_const _ _
  have ht : scalarTimeDerivative (fun z => sourceBallBarrier v₀ r lam M z.2) z = 0 := by
    change deriv (fun _ : ℝ => sourceBallBarrier v₀ r lam M z.2) z.1 = 0
    exact deriv_const _ _
  rw [scalarParabolicZeroOrderOperator_apply, ht]
  simp only [Pi.zero_apply, PDE.vecDot, zero_mul, Finset.sum_const_zero, add_zero, zero_add]
  change matrixContraction _ (sliceHessian (fun y => Ψ (PDE.vecNormSq (y - v₀))) _) = _
  rw [matrixContraction_sliceHessian_comp_vecNormSq_sub hΨ.contDiffAt, hd, hdd]
  ring

/-- Lower ellipticity gives the source-M supersolution inequality. -/
theorem scalarOperator_sourceBallBarrier_le {d : ℕ} (hd : 0 < d)
    (v₀ : PDE.Vec d) (r lam M : ℝ) (hlam : 0 < lam) (hM : 0 ≤ M)
    (A : CoefficientField d) (hlo : HasLowerEllipticity lam A) (z : TimeVelocity d) :
    scalarParabolicZeroOrderOperator A (fun _ _ => 0) (fun _ _ => 0)
      (fun z => sourceBallBarrier v₀ r lam M z.2) z ≤ -M := by
  rw [scalarOperator_sourceBallBarrier]
  have htr := (Matrix.le_iff.mp (hlo z.1 z.2)).trace_nonneg
  rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one] at htr
  simp only [Fintype.card_fin, smul_eq_mul] at htr
  apply (div_le_iff₀ (mul_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr hd)) hlam)).2
  nlinarith [mul_nonneg hM (show 0 ≤ (A z.1 z.2).trace - (d : ℝ) * lam by linarith)]

end HypoellipticAleksandrov.Parabolic.LocalHolder
