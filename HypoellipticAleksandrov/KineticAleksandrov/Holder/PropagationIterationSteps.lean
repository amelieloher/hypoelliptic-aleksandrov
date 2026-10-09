module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.PropagationParametersBounds
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-! # Uniform step bounds for the source ceiling partition -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

/-- The source ceiling partition has steps between half the allowed size and the allowed size. -/
theorem propagation_ceiling_steps {hs TP T1 : ℝ} (hhs : 0 < hs) (hTP : hs ≤ TP)
    (hT1 : TP ≤ T1) :
    0 < Nat.ceil (TP / hs) ∧
      0 < TP / (Nat.ceil (TP / hs) : ℝ) ∧
      TP / (Nat.ceil (TP / hs) : ℝ) ≤ hs ∧
      hs / 2 ≤ TP / (Nat.ceil (TP / hs) : ℝ) ∧
      Nat.ceil (TP / hs) ≤ Nat.ceil (T1 / hs) ∧
      (Nat.ceil (TP / hs) : ℝ) * (TP / (Nat.ceil (TP / hs) : ℝ)) = TP := by
  have hTP0 := hhs.trans_le hTP
  have hn : 0 < Nat.ceil (TP / hs) := Nat.ceil_pos.mpr (div_pos hTP0 hhs)
  have hnr : 0 < (Nat.ceil (TP / hs) : ℝ) := Nat.cast_pos.mpr hn
  have hratio : 1 ≤ TP / hs := (le_div_iff₀ hhs).mpr (by simpa using hTP)
  have hlo := Nat.le_ceil (TP / hs)
  have hup := Nat.ceil_lt_add_one (div_pos hTP0 hhs).le
  have htwice : (Nat.ceil (TP / hs) : ℝ) ≤ 2 * (TP / hs) := by
    linarith only [hup, hratio]
  refine ⟨hn, div_pos hTP0 hnr, ?_, ?_, ?_, ?_⟩
  · apply (div_le_iff₀ hnr).mpr
    have he := (div_le_iff₀ hhs).mp hlo
    simpa only [mul_comm] using he
  · apply (le_div_iff₀ hnr).mpr
    have he := (le_div_iff₀ hhs).mp (by
      simpa only [mul_div_assoc] using htwice :
      (Nat.ceil (TP / hs) : ℝ) ≤ (2 * TP) / hs)
    nlinarith only [he]
  · exact Nat.ceil_mono (div_le_div_of_nonneg_right hT1 hhs.le)
  · field_simp

end HypoellipticAleksandrov.KineticAleksandrov.Holder
