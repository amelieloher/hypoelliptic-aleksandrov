module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreStartBand
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripGreen
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationWaiting
import Mathlib.Tactic

/-! # The literal first-arrival waiting component outside the closed entrance band -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set

/-- Every pole outside the entrance band has a waiting interval with entrance internal exits. -/
theorem belowFour_waiting_interval (c : Clock) (H : Interval) (v : ℝ)
    (hv : v ∈ H.carrier) (hnot : v ∉ closure c.entrance) :
    ∃ W : Interval, v ∈ W.carrier ∧ W.carrier ⊆ H.carrier ∧
      Disjoint W.carrier c.core ∧
      ∀ w : ℝ, (w = W.lo ∨ w = W.hi) → w ∈ H.carrier → w ∈ closure c.entrance := by
  have hlo : c.vbar - c.r / 2 < c.vbar + c.r / 2 := by linarith [c.positive]
  rw [Clock.entrance, closure_Ioo hlo.ne] at hnot ⊢
  change H.lo < v ∧ v < H.hi at hv
  by_cases hl : v < c.vbar - c.r / 2
  · have hp : H.lo < min H.hi (c.vbar - c.r / 2) := lt_min H.ordered (hv.1.trans hl)
    let W : Interval := ⟨H.lo, min H.hi (c.vbar - c.r / 2), hp⟩
    refine ⟨W, ⟨hv.1, lt_min hv.2 hl⟩, ?_, ?_, ?_⟩
    · intro w hw
      exact ⟨hw.1, hw.2.trans_le (min_le_left _ _)⟩
    · apply disjoint_left.mpr
      intro w hw hc
      change c.vbar - c.r / 4 ≤ w ∧ w ≤ c.vbar + c.r / 4 at hc
      have hh := hw.2.trans_le (min_le_right H.hi (c.vbar - c.r / 2))
      linarith [hc.1, c.positive]
    · intro w hw hwH
      rcases hw with hw | hw
      · change w = H.lo at hw
        exact (lt_irrefl w (hw ▸ hwH.1)).elim
      · change w = min H.hi (c.vbar - c.r / 2) at hw
        have he : min H.hi (c.vbar - c.r / 2) = c.vbar - c.r / 2 := by
          by_cases hh : H.hi ≤ c.vbar - c.r / 2
          · rw [min_eq_left hh] at hw
            exact (lt_irrefl w (hw ▸ hwH.2)).elim
          · exact min_eq_right (le_of_not_ge hh)
        rw [hw, he]
        exact ⟨le_rfl, hlo.le⟩
  · have hr : c.vbar + c.r / 2 < v := by
      by_contra hh
      exact hnot ⟨le_of_not_gt hl, le_of_not_gt hh⟩
    have hp : max H.lo (c.vbar + c.r / 2) < H.hi := max_lt H.ordered (hr.trans hv.2)
    let W : Interval := ⟨max H.lo (c.vbar + c.r / 2), H.hi, hp⟩
    refine ⟨W, ⟨max_lt hv.1 hr, hv.2⟩, ?_, ?_, ?_⟩
    · intro w hw
      exact ⟨(le_max_left _ _).trans_lt hw.1, hw.2⟩
    · apply disjoint_left.mpr
      intro w hw hc
      change c.vbar - c.r / 4 ≤ w ∧ w ≤ c.vbar + c.r / 4 at hc
      have hh := (le_max_right H.lo (c.vbar + c.r / 2)).trans_lt hw.1
      linarith [hc.2, c.positive]
    · intro w hw hwH
      rcases hw with hw | hw
      · change w = max H.lo (c.vbar + c.r / 2) at hw
        have he : max H.lo (c.vbar + c.r / 2) = c.vbar + c.r / 2 := by
          by_cases hh : c.vbar + c.r / 2 ≤ H.lo
          · rw [max_eq_left hh] at hw
            exact (lt_irrefl w (hw ▸ hwH.1)).elim
          · exact max_eq_right (le_of_not_ge hh)
        rw [hw, he]
        exact ⟨hlo.le, le_rfl⟩
      · change w = H.hi at hw
        exact (lt_irrefl w (hw ▸ hwH.2)).elim

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
