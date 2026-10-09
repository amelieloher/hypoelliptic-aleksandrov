module

public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Topology.Order.OrderClosed

/-!
# Weak-limit norm bounds

This module records the dual-functional proof that a uniformly norm-bounded
sequence has a norm-bounded weak limit.
-/

@[expose] public section

open Filter
open scoped Topology

namespace HypoellipticAleksandrov

/-- A uniform norm bound is inherited by a limit that converges under every
continuous real linear functional. -/
theorem norm_le_of_tendsto_clm_of_norm_le
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (u : ℕ → H) (v : H) (R : ℝ)
    (hu : ∀ n, ‖u n‖ ≤ R)
    (hweak : ∀ ell : H →L[ℝ] ℝ,
      Tendsto (fun n => ell (u n)) atTop (𝓝 (ell v))) :
    ‖v‖ ≤ R := by
  have hR : 0 ≤ R := (norm_nonneg (u 0)).trans (hu 0)
  refine NormedSpace.norm_le_dual_bound ℝ v hR ?_
  intro ell
  refine le_of_tendsto' ((hweak ell).norm) ?_
  intro n
  calc
    ‖ell (u n)‖ ≤ ‖ell‖ * ‖u n‖ := ContinuousLinearMap.le_opNorm ell (u n)
    _ ≤ ‖ell‖ * R := mul_le_mul_of_nonneg_left (hu n) (norm_nonneg ell)
    _ = R * ‖ell‖ := mul_comm _ _

end HypoellipticAleksandrov
