module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.TimeCutoff
import Mathlib.Tactic.Linarith

/-! # A global bound on the second derivative of the fixed cutoff -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/-- The exact rescaling factor in the second derivative of the cutoff. -/
theorem deriv2_timeCutoffTheta (s : ℝ) :
    deriv (deriv timeCutoffTheta) s = 16 * deriv flatteningSlope (16 * s + 1) := by
  have h := ((contDiff_flatteningSlope.differentiable (by simp)) (16 * s + 1)).hasDerivAt
  have he := h.comp s (((hasDerivAt_id s).const_mul 16).add_const 1)
  rw [funext deriv_timeCutoffTheta]
  simpa only [Function.comp_def, id_eq, mul_one, one_mul, mul_comm] using! he.deriv

/-- A fixed bound, independent of the profile and flattening scale, controls the second
derivative used by the weak second chain rule. -/
theorem timeCutoffTheta_deriv2_abs_bound :
    ∃ M : ℝ, 0 < M ∧ ∀ s, |deriv (deriv timeCutoffTheta) s| ≤ M := by
  obtain ⟨K, hK, hb⟩ := flatteningPsi_deriv2_bound
  refine ⟨16 * K, by positivity, ?_⟩
  intro s
  rw [abs_of_nonneg (timeCutoffTheta_deriv2_nonneg s), deriv2_timeCutoffTheta]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  simpa only [funext deriv_flatteningPsi] using hb (16 * s + 1)

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
