module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Setting
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic

/-! # Contractive integer height from the ink-spots gain

The scalar c is the dimension-only gain supplied by the ink-spots theorem.
This is a purely arithmetic module.
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth

/-- Positive gain and threshold make the density factor strictly between zero and one. -/
theorem density_factor_pos_lt_one {c eta : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (heta : 0 < eta) (heta1 : eta < 1) : 0 < 1-c*eta ∧ 1-c*eta < 1 := by
  constructor <;> nlinarith

/-- An integer height makes the ink-spots multiplier contractive. -/
theorem exists_contractive_stack_height {c eta : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (heta : 0 < eta) (heta1 : eta < 1) :
    ∃ m : ℕ, 0 < m ∧ 0 < (((m : ℝ)+1)/(m : ℝ))*(1-c*eta) ∧
      (((m : ℝ)+1)/(m : ℝ))*(1-c*eta) < 1 := by
  obtain ⟨m, hm⟩ := exists_nat_gt ((1-c*eta)/(c*eta))
  have hce : 0 < c*eta := mul_pos hc heta
  have hf := density_factor_pos_lt_one hc hc1 heta heta1
  have hmpos : 0 < (m : ℝ) := (div_pos hf.1 hce).trans hm
  have hmn : 0 < m := by exact_mod_cast hmpos
  refine ⟨m, hmn, mul_pos (div_pos (by linarith) hmpos) hf.1, ?_⟩
  have hmul := (div_lt_iff₀ hce).mp hm
  have heq : (((m : ℝ)+1)/(m : ℝ))*(1-c*eta) =
      (((m : ℝ)+1)*(1-c*eta))/(m : ℝ) := by ring
  rw [heq]
  apply (div_lt_iff₀ hmpos).mpr
  nlinarith

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth
