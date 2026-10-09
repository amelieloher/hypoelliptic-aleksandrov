module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-! # Continuous logarithmic covering of nonzero velocities

The literal identity `e:log-cover` uses closed core intervals and Lebesgue measure.
-/

@[expose] public section
noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory

/-- The continuous core cover has constant logarithmic multiplicity. -/
theorem log_core_cover (sgn : ℝ) (_hsgn : sgn = 1 ∨ sgn = -1)
    (v : ℝ) (hv : 0 < sgn * v) :
    (∫ r in Ioi (0 : ℝ),
      (if 7 * r / 8 ≤ sgn * v ∧ sgn * v ≤ 9 * r / 8 then 1 else 0) / r) =
        Real.log (9 / 7 : ℝ) := by
  let a := 8 * (sgn * v) / 9
  let b := 8 * (sgn * v) / 7
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have hfun : (fun r : ℝ =>
      (if 7 * r / 8 ≤ sgn * v ∧ sgn * v ≤ 9 * r / 8 then 1 else 0) / r) =
      (Icc a b).indicator (fun r => 1 / r) := by
    funext r
    have hiff : (7 * r / 8 ≤ sgn * v ∧ sgn * v ≤ 9 * r / 8) ↔ r ∈ Icc a b := by
      dsimp [a, b]
      constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
    by_cases hr : r ∈ Icc a b
    · rw [ite_eq_left (hiff.mpr hr), indicator_of_mem hr]
    · rw [ite_eq_right (fun h => hr (hiff.mp h)), indicator_of_notMem hr, zero_div]
  rw [hfun, setIntegral_indicator measurableSet_Icc]
  have hsub : Icc a b ⊆ Ioi (0 : ℝ) := fun r hr => lt_of_lt_of_le ha hr.1
  rw [inter_eq_right.mpr hsub, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab,
    integral_one_div_of_pos ha hb]
  congr 1
  dsimp [a, b]
  have hs : sgn ≠ 0 := left_ne_zero_of_mul (ne_of_gt hv)
  have hv' : v ≠ 0 := right_ne_zero_of_mul (ne_of_gt hv)
  field_simp

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
