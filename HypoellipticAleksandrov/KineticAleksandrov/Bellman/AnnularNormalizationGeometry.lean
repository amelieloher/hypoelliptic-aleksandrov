module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.BarrierFunctionSpaceGeometry
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic

/-! # Compact anisotropic sublevel sets away from the puncture -/

@[expose] public section
noncomputable section
open Set
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- A positive gauge is equivalent to being off the origin. -/
theorem bellmanGauge_pos (q : ℝ × ℝ) (hq : q ≠ (0, 0)) : 0 < bellmanGauge q := by
  exact Real.rpow_pos_of_pos
    (lt_of_le_of_ne (bellmanGaugePower_nonneg q)
      (Ne.symm ((bellmanGaugePower_eq_zero_iff q).not.mpr hq))) _

/-- The gauge is nonnegative everywhere. -/
theorem bellmanGauge_nonneg (q : ℝ × ℝ) : 0 ≤ bellmanGauge q :=
  Real.rpow_nonneg (bellmanGaugePower_nonneg q) _

private theorem abs_le_of_even_pow_bound (x C : ℝ) (hC : 0 ≤ C) (n : ℕ)
    (hn : n ≠ 0) (he : Even n) (hx : x ^ n ≤ C) : |x| ≤ C + 1 := by
  rcases le_or_gt |x| 1 with h | h
  · exact h.trans (by linarith only [hC])
  · have hp := le_self_pow₀ h.le hn
    rw [he.pow_abs] at hp
    exact hp.trans (hx.trans (by linarith))

/-- Polynomial sublevel sets are compact in the literal ambient product plane. -/
theorem bellmanGaugePower_sublevel_isCompact (C : ℝ) (hC : 0 ≤ C) :
    IsCompact {q : ℝ × ℝ | bellmanGaugePower q ≤ C} := by
  have hc : IsClosed {q : ℝ × ℝ | bellmanGaugePower q ≤ C} :=
    isClosed_le bellmanGaugePower_continuous continuous_const
  apply ((isCompact_Icc : IsCompact (Icc (-C - 1) (C + 1))).prod
    (isCompact_Icc : IsCompact (Icc (-C - 1) (C + 1)))).of_isClosed_subset hc
  intro q hq
  have hx : q.1 ^ 2 ≤ C := by
    have hv := Even.pow_nonneg (by decide : Even 6) q.2
    change q.1 ^ 2 + q.2 ^ 6 ≤ C at hq
    linarith only [hq, hv]
  have hv : q.2 ^ 6 ≤ C := by
    change q.1 ^ 2 + q.2 ^ 6 ≤ C at hq
    linarith only [hq, sq_nonneg q.1]
  have hx' := abs_le_of_even_pow_bound q.1 C hC 2 (by decide) (by decide) hx
  have hv' := abs_le_of_even_pow_bound q.2 C hC 6 (by decide) (by decide) hv
  rcases abs_le.mp hx' with ⟨hxl, hxu⟩
  rcases abs_le.mp hv' with ⟨hvl, hvu⟩
  exact ⟨⟨by linarith only [hxl], hxu⟩, ⟨by linarith only [hvl], hvu⟩⟩

/-- The closed anisotropic shell is compact in the ambient plane. -/
theorem bellmanGauge_shell_isCompact (a b : ℝ) :
    IsCompact {q : ℝ × ℝ | a ≤ bellmanGauge q ∧ bellmanGauge q ≤ b} := by
  have hc : IsClosed {q : ℝ × ℝ | a ≤ bellmanGauge q ∧ bellmanGauge q ≤ b} :=
    (isClosed_le continuous_const bellmanGauge_continuous).inter
      (isClosed_le bellmanGauge_continuous continuous_const)
  apply IsCompact.of_isClosed_subset
    (bellmanGaugePower_sublevel_isCompact (max 0 (b ^ 6)) (le_max_left _ _)) hc
  intro q hq
  change bellmanGaugePower q ≤ max 0 (b ^ 6)
  rw [← bellmanGauge_pow_six]
  exact (pow_le_pow_left₀ (bellmanGauge_nonneg q) hq.2 6).trans (le_max_right _ _)

/-- The polynomial gauge is smooth on the whole ambient plane. -/
theorem bellmanGaugePower_contDiff : ContDiff ℝ (⊤ : ℕ∞) bellmanGaugePower := by
  exact (contDiff_fst.pow 2).add (contDiff_snd.pow 6)

end HypoellipticAleksandrov.KineticAleksandrov
