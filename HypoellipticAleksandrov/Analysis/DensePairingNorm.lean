module

public import Mathlib.Analysis.InnerProductSpace.Continuous

/-!
# Norm control from pairings on a dense subset

This module records a real inner-product space closure lemma: a uniform bound for
inner-product pairings on a dense subset extends to the whole space and hence
controls the norm.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Analysis

open scoped InnerProductSpace

/-- A uniform pairing bound on a dense subset controls the norm in a real
inner-product space. -/
theorem norm_le_of_abs_real_inner_le_on_dense
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {D : Set H} (hD : Dense D) (x : H) (C : ℝ) (hC : 0 ≤ C)
    (hpair : ∀ y ∈ D, |⟪x, y⟫_ℝ| ≤ C * ‖y‖) :
    ‖x‖ ≤ C := by
  have hpair_all : ∀ y : H, |⟪x, y⟫_ℝ| ≤ C * ‖y‖ := by
    have hclosed : IsClosed {y : H | |⟪x, y⟫_ℝ| ≤ C * ‖y‖} :=
      isClosed_le
        ((continuous_const.inner continuous_id).abs)
        (continuous_const.mul continuous_norm)
    intro y
    exact hD.induction hpair hclosed y
  by_cases hx : x = 0
  · simp [hx, hC]
  · have hnorm_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hself := hpair_all x
    rw [real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg ‖x‖)] at hself
    nlinarith

end HypoellipticAleksandrov.Analysis
