module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SurvivalKernel
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-! # Iterating a uniform half-mass time

These internal kernel lemmas retain their literal uniform hypothesis. The active
survival theorem discharges it using the quadratic occupation calculation.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo

/-- A uniform half-mass estimate iterates through actual killed-kernel composition. -/
theorem stripSurvivingMass_geometric_of_half_mass {lam Lam : ℝ}
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (D : ℝ) (hD : 0 < D)
    (hhalf : ∀ s z, stripSurvivingMass H E s (s + D)
      (le_add_of_nonneg_right hD.le) z ≤ 1 / 2)
    (s : ℝ) (z : EvolutionState (intervalDomain H) (fun _ => 0) s) (n : ℕ) :
    stripSurvivingMass H E s (s + n * D)
      (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) hD.le)) z ≤
        (1 / 2 : ℝ) ^ n := by
  induction n with
  | zero =>
    simpa only [Nat.cast_zero, zero_mul, add_zero, pow_zero] using
      (stripSurvivingMass_bounds A H E hE s s le_rfl z).2
  | succ n ih =>
    have hst : s ≤ s + n * D :=
      le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) hD.le)
    have htu : s + n * D ≤ s + (n + 1 : ℕ) * D := by
      rw [Nat.cast_add, Nat.cast_one, add_mul]
      linarith
    have ht : s + (n + 1 : ℕ) * D = (s + n * D) + D := by
      push_cast
      ring
    have hh : ∀ w, E.1 (s + n * D) (s + (n + 1 : ℕ) * D) htu 1 w ≤ 1 / 2 := by
      intro w
      have hs := hhalf (s + n * D) w
      change E.1 (s + n * D) ((s + n * D) + D) _ 1 w ≤ 1 / 2 at hs
      have heq : E.1 (s + n * D) (s + (n + 1 : ℕ) * D) htu 1 w =
          E.1 (s + n * D) ((s + n * D) + D) (le_add_of_nonneg_right hD.le) 1 w := by
        exact congrArg (fun u : {u : ℝ // s + n * D ≤ u} =>
          E.1 (s + n * D) u.1 u.2 1 w)
          (show (⟨s + (n + 1 : ℕ) * D, htu⟩ : {u : ℝ // s + n * D ≤ u}) =
            ⟨(s + n * D) + D, le_add_of_nonneg_right hD.le⟩ from Subtype.ext ht)
      rw [heq]
      exact hs
    have hm := stripSurvivingMass_le_mul_of_later_bound A H E hE s
      (s + n * D) (s + (n + 1 : ℕ) * D) (1 / 2) hst htu hh z
    exact hm.trans (by simpa only [pow_succ, mul_comm] using
      mul_le_mul_of_nonneg_left ih (by norm_num : (0 : ℝ) ≤ 1 / 2))

/-- A geometric bound at half-mass times gives the source exponential estimate at every time. -/
theorem stripSurvivingMass_exp_of_half_mass {lam Lam : ℝ}
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (D : ℝ) (hD : 0 < D)
    (hhalf : ∀ s z, stripSurvivingMass H E s (s + D)
      (le_add_of_nonneg_right hD.le) z ≤ 1 / 2)
    (s t : ℝ) (ht : 0 ≤ t)
    (z : EvolutionState (intervalDomain H) (fun _ => 0) s) :
    stripSurvivingMass H E s (s + t) (le_add_of_nonneg_right ht) z ≤
      2 * Real.exp (-Real.log 2 * t / D) := by
  let n := Nat.floor (t / D)
  have hn : (n : ℝ) ≤ t / D := Nat.floor_le (div_nonneg ht hD.le)
  have hn' : t / D < (n : ℝ) + 1 := Nat.lt_floor_add_one (t / D)
  have htime : s + n * D ≤ s + t := by
    exact add_le_add_right ((le_div_iff₀ hD).mp hn) s
  have hm := stripSurvivingMass_antitone A H E hE s (s + n * D) (s + t)
    (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) hD.le)) htime z
  have hg := stripSurvivingMass_geometric_of_half_mass A H E hE D hD hhalf s z n
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have he : (1 / 2 : ℝ) ^ n = Real.exp (-Real.log 2 * n) := by
    rw [mul_comm (-Real.log 2) (n : ℝ), Real.exp_nat_mul,
      Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    simp only [one_div]
  have hx : -Real.log 2 * (n : ℝ) ≤ Real.log 2 + (-Real.log 2 * t / D) := by
    have hh := mul_le_mul_of_nonneg_left hn'.le hlog.le
    have heq : Real.log 2 * (t / D) = Real.log 2 * t / D := by ring
    rw [heq] at hh
    rw [mul_add, mul_one] at hh
    rw [neg_mul, neg_mul, neg_div]
    linarith only [hh]
  calc
    _ ≤ (1 / 2 : ℝ) ^ n := hm.trans hg
    _ = Real.exp (-Real.log 2 * n) := he
    _ ≤ Real.exp (Real.log 2 + (-Real.log 2 * t / D)) := Real.exp_le_exp.mpr hx
    _ = 2 * Real.exp (-Real.log 2 * t / D) := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
