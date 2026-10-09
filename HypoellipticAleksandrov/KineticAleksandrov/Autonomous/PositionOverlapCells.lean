module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitsCells
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-! # Coverage and separation of the literal time-position grid -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory
open scoped Classical

/-- Each time bin lies between its two literal grid endpoints. -/
theorem enlargedTimeBin_bounds (r s t : ℝ) (j : ℕ)
    (ht : t ∈ enlargedTimeBin r s j) :
    s + (j : ℝ) * r ^ 2 ≤ t ∧ t ≤ s + ((j : ℝ) + 1) * r ^ 2 := by
  by_cases hj : j = 0
  · subst j
    simpa [enlargedTimeBin] using ht
  · have ht' : s + (j : ℝ) * r ^ 2 < t ∧
        t ≤ s + ((j : ℝ) + 1) * r ^ 2 := by
      simpa [enlargedTimeBin, hj] using ht
    exact ⟨ht'.1.le, ht'.2⟩

/-- A later noninitial bin excludes its lower time endpoint. -/
theorem enlargedTimeBin_lower_strict (r s t : ℝ) (j : ℕ) (hj : j ≠ 0)
    (ht : t ∈ enlargedTimeBin r s j) : s + (j : ℝ) * r ^ 2 < t := by
  have ht' : s + (j : ℝ) * r ^ 2 < t ∧
      t ≤ s + ((j : ℝ) + 1) * r ^ 2 := by
    simpa [enlargedTimeBin, hj] using ht
  exact ht'.1

/-- The source time bins cover precisely the half line from their time origin. -/
theorem enlargedTimeBin_covers (r s t : ℝ) (hr : 0 < r) (ht : s ≤ t) :
    ∃ j : ℕ, t ∈ enlargedTimeBin r s j := by
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hex : ∃ n : ℕ, t ≤ s + ((n : ℝ) + 1) * r ^ 2 := by
    obtain ⟨n, hn⟩ := exists_nat_gt ((t - s) / r ^ 2)
    refine ⟨n, ?_⟩
    have h := (div_lt_iff₀ hr2).mp hn
    linarith
  let j := Nat.find hex
  have hu : t ≤ s + ((j : ℝ) + 1) * r ^ 2 := Nat.find_spec hex
  refine ⟨j, ?_⟩
  by_cases hj : j = 0
  · have hu' : t ≤ s + r ^ 2 := by simpa only [hj, Nat.cast_zero, zero_add, one_mul] using hu
    simpa [enlargedTimeBin, hj] using ⟨ht, hu'⟩
  · have hjp : j.pred < j := Nat.pred_lt hj
    have hn := Nat.find_min hex hjp
    have he : j = j.pred + 1 := (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hj)).symm
    have hc : (j.pred : ℝ) + 1 = (j : ℝ) := by exact_mod_cast he.symm
    have hl : s + (j : ℝ) * r ^ 2 < t := by
      rw [hc] at hn
      exact not_le.mp hn
    simpa [enlargedTimeBin, hj] using ⟨hl, hu⟩

/-- Distinct time bins are disjoint, including the initial atom convention. -/
theorem enlargedTimeBin_disjoint (r s : ℝ) (_hr : 0 < r) :
    Pairwise (fun i j => Disjoint (enlargedTimeBin r s i) (enlargedTimeBin r s j)) := by
  intro i j hij
  wlog hlt : i < j generalizing i j
  · exact (this (i := j) (j := i) hij.symm (lt_of_le_of_ne (Nat.le_of_not_gt hlt) hij.symm)).symm
  apply disjoint_left.mpr
  intro t hi hj
  have hui := (enlargedTimeBin_bounds r s t i hi).2
  have hlj := enlargedTimeBin_lower_strict r s t j (by omega) hj
  have hc : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hlt
  nlinarith only [hui, hlj, hc, sq_nonneg r]

/-- The half-open position grid covers every real position. -/
theorem enlargedPositionCell_covers (r x y : ℝ) (hr : 0 < r) :
    ∃ k : ℤ, y ∈ enlargedPositionCell r x k := by
  let u := (y - x) / r ^ 3
  refine ⟨⌊u⌋, ?_⟩
  have hr3 : 0 < r ^ 3 := pow_pos hr _
  have hl := (le_div_iff₀ hr3).mp (Int.floor_le u)
  have hu := (div_lt_iff₀ hr3).mp (Int.lt_floor_add_one u)
  change x + (⌊u⌋ : ℝ) * r ^ 3 ≤ y ∧ y < x + ((⌊u⌋ : ℝ) + 1) * r ^ 3
  constructor <;> linarith

/-- Distinct half-open position cells are disjoint. -/
theorem enlargedPositionCell_disjoint (r x : ℝ) (hr : 0 < r) :
    Pairwise (fun k l => Disjoint (enlargedPositionCell r x k) (enlargedPositionCell r x l)) := by
  intro k l hkl
  wlog hlt : k < l generalizing k l
  · exact (this (k := l) (l := k) hkl.symm (lt_of_le_of_ne (le_of_not_gt hlt) hkl.symm)).symm
  apply disjoint_left.mpr
  intro y hk hl
  change x + (k : ℝ) * r ^ 3 ≤ y ∧ y < x + ((k : ℝ) + 1) * r ^ 3 at hk
  change x + (l : ℝ) * r ^ 3 ≤ y ∧ y < x + ((l : ℝ) + 1) * r ^ 3 at hl
  have hc : (k : ℝ) + 1 ≤ (l : ℝ) := by exact_mod_cast hlt
  nlinarith only [hk.2, hl.1, hc, (pow_pos hr 3).le]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
