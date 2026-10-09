module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.QuadraticCalculus
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Tactic

/-! # The fixed smooth cutoff for kinetic Gaussian barriers -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

/-- A source-compatible cutoff, zero through `-1/128` and one from zero onward. -/
def barrierCutoff (theta : ℝ) : ℝ := Real.smoothTransition (128 * theta + 1)

/-- The internally chosen barrier cutoff is infinitely differentiable. -/
theorem contDiff_barrierCutoff : ContDiff ℝ (⊤ : ℕ∞) barrierCutoff :=
  Real.smoothTransition.contDiff.comp (contDiff_const.mul contDiff_id |>.add contDiff_const)

/-- The barrier cutoff has values in the closed unit interval. -/
theorem barrierCutoff_bounds (theta : ℝ) : 0 ≤ barrierCutoff theta ∧ barrierCutoff theta ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

/-- The barrier cutoff vanishes throughout the left cutoff region. -/
theorem barrierCutoff_zero {theta : ℝ} (htheta : theta ≤ -(1 / 128 : ℝ)) :
    barrierCutoff theta = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith only [htheta])

/-- The barrier cutoff is exactly one on all nonnegative times. -/
theorem barrierCutoff_one {theta : ℝ} (htheta : 0 ≤ theta) : barrierCutoff theta = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith only [htheta])

/-- The source damping coefficient, fixed before the block and amplitude. -/
def Xi (d : ℕ) (lam Lam H h : ℝ) : ℝ :=
  2 * Lam * (128 * (d : ℝ) / lam) / h + 2 * H ^ 2 / (3 * lam)

/-- The raw quadratic form is smooth at every point of the positive-definite strip. -/
theorem contDiffAt_qform_raw {d : ℕ} {lam h s : ℝ}
    (hlam : 0 < lam) (hh : 0 < h) (hs : -(h / 128) ≤ s) (y V : PDE.Vec d) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun Q : ℝ × (PDE.Vec d × PDE.Vec d) => qform lam h Q.1 Q.2.1 Q.2.2)
      (s, (y, V)) := by
  have heq : (fun Q : ℝ × (PDE.Vec d × PDE.Vec d) =>
      qform lam h Q.1 Q.2.1 Q.2.2) =
      (fun Q => (covarianceVV lam h Q.1 * PDE.vecDot Q.2.1 Q.2.1 -
        2 * covarianceXV lam h Q.1 * PDE.vecDot Q.2.1 Q.2.2 +
        covarianceXX lam h Q.1 * PDE.vecDot Q.2.2 Q.2.2) / covarianceDet lam h Q.1) := by
    funext Q
    exact qform_eq_scalar lam hh _ _ _
  rw [heq]
  apply ContDiffAt.div
  · unfold covarianceVV covarianceXV covarianceXX PDE.vecDot
    fun_prop
  · unfold covarianceDet covarianceVV covarianceXV covarianceXX
    fun_prop
  · exact (covarianceDet_pos hlam hh hs).ne'

end HypoellipticAleksandrov.KineticAleksandrov.Holder
