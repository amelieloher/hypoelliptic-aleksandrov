module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BelowFourBandStatement
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! # The literal signed geometric core cover used below exponent four -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set

/-- The source geometric centre magnitudes, 8R(7/8)^j. -/
def geometricCoreScale (R : ℝ) (j : ℕ) : ℝ := 8 * R * (7 / 8 : ℝ) ^ j

/-- Every source centre magnitude is positive. -/
theorem geometricCoreScale_pos (R : ℝ) (hR : 0 < R) (j : ℕ) :
    0 < geometricCoreScale R j := by unfold geometricCoreScale; positivity

/-- The source positive and negative clock data have radius half the centre magnitude. -/
def geometricCoreClock (R : ℝ) (hR : 0 < R) (j : ℕ) (positive : Bool) : Clock where
  vbar := if positive then geometricCoreScale R j else -geometricCoreScale R j
  r := geometricCoreScale R j / 2
  nonzero := by split <;> have h := geometricCoreScale_pos R hR j <;> linarith
  positive := by have h := geometricCoreScale_pos R hR j; positivity
  radius := by
    have h := geometricCoreScale_pos R hR j
    split <;> simp only [abs_of_pos h, abs_neg] <;> linarith

/-- The source signed geometric clocks satisfy the band-centre relation. -/
theorem geometricCoreClock_center (R : ℝ) (hR : 0 < R) (j : ℕ) (s : Bool) :
    |(geometricCoreClock R hR j s).vbar| = 2 * (geometricCoreClock R hR j s).r := by
  have h := geometricCoreScale_pos R hR j
  cases s <;> simp only [geometricCoreClock, Bool.false_eq_true, ↓reduceIte,
    abs_neg, abs_of_pos h] <;> ring

/-- Every geometric band radius is at most 4R, hence within the allowed 6R. -/
theorem geometricCoreClock_radius (R : ℝ) (hR : 0 < R) (j : ℕ) (s : Bool) :
    (geometricCoreClock R hR j s).r ≤ 6 * R := by
  have hj : (7 / 8 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  change 8 * R * (7 / 8 : ℝ) ^ j / 2 ≤ 6 * R
  nlinarith

/-- Geometric annuli cover every positive magnitude up to 9R, including endpoints. -/
theorem geometricCoreScale_covers (R v : ℝ) (hR : 0 < R) (hv : 0 < v)
    (hupper : v ≤ 9 * R) :
    ∃ j : ℕ, geometricCoreScale R j * (7 / 8) ≤ v ∧
      v ≤ geometricCoreScale R j * (9 / 8) := by
  have hex : ∃ j : ℕ, geometricCoreScale R j * (7 / 8) ≤ v := by
    obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (show 0 < v / (8 * R) by positivity)
      (show (7 / 8 : ℝ) < 1 by norm_num)
    refine ⟨j, ?_⟩
    have hj' : 8 * R * (7 / 8 : ℝ) ^ j < v :=
      by
      simpa only [mul_comm] using
        (lt_div_iff₀ (by positivity : 0 < 8 * R)).mp hj
    have hp := pow_nonneg (show (0 : ℝ) ≤ 7 / 8 by norm_num) j
    unfold geometricCoreScale
    nlinarith
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  cases hn : Nat.find hex with
  | zero => simp only [geometricCoreScale, pow_zero, mul_one]; linarith
  | succ j =>
    have hj : ¬geometricCoreScale R j * (7 / 8) ≤ v :=
      Nat.find_min hex (by omega)
    have hp := geometricCoreScale_pos R hR (j + 1)
    have he : geometricCoreScale R (j + 1) = geometricCoreScale R j * (7 / 8) := by
      simp only [geometricCoreScale, pow_succ]; ring
    rw [he]
    linarith

/-- The actual closed cores cover both signs of every nonzero velocity up to 9R. -/
theorem geometricCoreClock_covers (R v : ℝ) (hR : 0 < R) (hv : v ≠ 0)
    (hupper : |v| ≤ 9 * R) :
    ∃ j : ℕ, ∃ s : Bool, v ∈ (geometricCoreClock R hR j s).core := by
  obtain ⟨j, hl, hu⟩ := geometricCoreScale_covers R |v| hR (abs_pos.mpr hv) hupper
  refine ⟨j, ?_⟩
  rcases lt_or_gt_of_ne hv with hneg | hpos
  · refine ⟨false, ?_⟩
    rw [abs_of_neg hneg] at hl hu
    change -geometricCoreScale R j - (geometricCoreScale R j / 2) / 4 ≤ v ∧
      v ≤ -geometricCoreScale R j + (geometricCoreScale R j / 2) / 4
    constructor <;> linarith
  · refine ⟨true, ?_⟩
    rw [abs_of_pos hpos] at hl hu
    change geometricCoreScale R j - (geometricCoreScale R j / 2) / 4 ≤ v ∧
      v ≤ geometricCoreScale R j + (geometricCoreScale R j / 2) / 4
    constructor <;> linarith

/-- The characterized Bellman degree forces exactly the positive geometric exponent. -/
theorem belowFour_exponent_range (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (alpha q : ℝ)
    (ha : bellmanAdjointExponent (Lam / lam) ((le_div_iff₀ hlam).2
      (by simpa only [one_mul] using hLam)) - 2 < alpha ∧ alpha < 1)
    (hq : 1 < q ∧ q < (4 - (1 - alpha)) / (3 - (1 - alpha))) :
    0 < alpha ∧ q < 3 / 2 ∧ 0 < 4 - 3 * q + (1 - alpha) * (q - 1) := by
  have hb := bellmanAdjointExponent_range (Lam / lam) ((le_div_iff₀ hlam).2
    (by simpa only [one_mul] using hLam))
  have ha0 : 0 < alpha := by linarith [hb.1, ha.1]
  have hd : 0 < 3 - (1 - alpha) := by linarith
  have hq' := (lt_div_iff₀ hd).mp hq.2
  refine ⟨ha0, ?_, ?_⟩ <;> nlinarith [ha.2]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
