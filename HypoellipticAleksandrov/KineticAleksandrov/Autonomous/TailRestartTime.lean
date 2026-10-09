module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Elapsed
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Tactic

/-! # Exact translation of the positive elapsed-time measure -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory SectionTwo
open scoped ENNReal

/-- Shift a positive elapsed time by a nonnegative restart delay. -/
def tailElapsedShift (t : ℝ) (ht : 0 ≤ t) (tau : ElapsedTime ⊤) : ElapsedTime ⊤ :=
  ⟨t + tau.1, add_pos_of_nonneg_of_pos ht tau.2.1, ENNReal.ofReal_lt_top⟩

/-- The restart translation is Borel. -/
theorem measurable_tailElapsedShift (t : ℝ) (ht : 0 ≤ t) :
    Measurable (tailElapsedShift t ht) :=
  (measurable_const.add measurable_subtype_coe).subtype_mk

/-- Translation gives precisely the strict later-time restriction of elapsed Lebesgue measure. -/
theorem tailElapsedShift_map (t : ℝ) (ht : 0 ≤ t) :
    (elapsedVolume ⊤).map (tailElapsedShift t ht) =
      (elapsedVolume ⊤).restrict {tau | t < tau.1} := by
  ext B hB
  have hm : MeasurableSet {tau : ElapsedTime ⊤ | t < tau.1} :=
    measurable_subtype_coe measurableSet_Ioi
  rw [Measure.map_apply (measurable_tailElapsedShift t ht) hB,
    elapsedVolume_apply _ _ ((measurable_tailElapsedShift t ht) hB),
    Measure.restrict_apply hB, elapsedVolume_apply _ _ (hB.inter hm)]
  have he : (Subtype.val : ElapsedTime ⊤ → ℝ) '' (B ∩ {tau | t < tau.1}) =
      (fun x : ℝ => t + x) ''
        ((Subtype.val : ElapsedTime ⊤ → ℝ) '' ((tailElapsedShift t ht) ⁻¹' B)) := by
    ext x
    constructor
    · rintro ⟨tau, ⟨hBtau, httau⟩, rfl⟩
      let a : ElapsedTime ⊤ := ⟨tau.1 - t, sub_pos.mpr httau, ENNReal.ofReal_lt_top⟩
      have ha : tailElapsedShift t ht a = tau := Subtype.ext (by
        dsimp [a, tailElapsedShift]
        ring)
      have hb : a ∈ (tailElapsedShift t ht) ⁻¹' B := by
        change tailElapsedShift t ht a ∈ B
        rw [ha]
        exact hBtau
      exact ⟨a.1, ⟨a, hb, rfl⟩, by dsimp [a]; ring⟩
    · rintro ⟨x, ⟨tau, hBtau, rfl⟩, rfl⟩
      exact ⟨tailElapsedShift t ht tau, ⟨hBtau, by
        change t < t + tau.1; linarith [tau.2.1]⟩, rfl⟩
  rw [he]
  have hi : (fun x : ℝ => t + x) ''
      ((Subtype.val : ElapsedTime ⊤ → ℝ) '' ((tailElapsedShift t ht) ⁻¹' B)) =
      (fun x : ℝ => -t + x) ⁻¹'
        ((Subtype.val : ElapsedTime ⊤ → ℝ) '' ((tailElapsedShift t ht) ⁻¹' B)) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change -t + (t + y) ∈
        ((Subtype.val : ElapsedTime ⊤ → ℝ) '' ((tailElapsedShift t ht) ⁻¹' B))
      simpa only [neg_add_cancel_left] using hy
    · intro hx
      exact ⟨-t + x, hx, by ring⟩
  rw [hi, measure_preimage_add volume (-t)]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
