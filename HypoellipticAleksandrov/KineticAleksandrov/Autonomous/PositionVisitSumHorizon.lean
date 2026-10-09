module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionVisitSum
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-! # Finite-horizon q-power summation for the literal visit measure -/

public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory

/-- A visit cell beyond the supported time horizon has zero mass. -/
theorem enlargedPositionVisitMass_eq_zero_of_horizon
    (nu : Measure Point) (c : Clock) (s x T : ℝ) (j : ℕ) (k : ℤ)
    (hs : ∀ᵐ p ∂nu, p.time < s + T) (hj : T ≤ (j : ℝ) * c.r ^ 2) :
    enlargedPositionVisitMass nu c s x j k = 0 := by
  have hz : nu (enlargedStartCell c s x j k ∩
      {p | p.velocity 0 ∈ closure c.entrance}) = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    apply hs.mono
    intro p hp hcell
    have hl := (enlargedTimeBin_bounds c.r s p.time j hcell.1.1).1
    linarith
  unfold enlargedPositionVisitMass
  rw [hz, ENNReal.toReal_zero]

/-- The source double q-power sum follows from the literal time and cell counts.
This helper is applied only after its two decay premises are proved for the same measure. -/
theorem enlargedPositionVisitMass_power_sum_horizon_le
    (nu : Measure Point) [IsFiniteMeasure nu] (c : Clock) (s x R T : ℝ)
    (hR : 0 < R) (hT : 0 < T) (hTR : T ≤ R ^ 2)
    (hs : ∀ᵐ p ∂nu, p.time < s + T)
    (Ct Cp g q : ℝ) (hCt : 0 ≤ Ct) (hCp : 0 ≤ Cp)
    (hg : 1 < g ∧ g < 2) (hq : 1 < q ∧ q < 3 / 2)
    (htime : ∀ j : ℕ,
      enlargedTimeVisitMass nu c s j ≤ Ct * (1 + (j : ℝ)) ^ (-1 / 2 : ℝ))
    (hcell : ∀ (j : ℕ) (k : ℤ),
      enlargedPositionVisitMass nu c s x j k ≤ Cp * (1 + (j : ℝ)) ^ (-g / 2)) :
    (∑' j : ℕ, ∑' k : ℤ, ENNReal.ofReal (enlargedPositionVisitMass nu c s x j k ^ q)) ≤
      ENNReal.ofReal ((Cp ^ (q - 1) * Ct *
        ((1 + 1 / (1 - (1 + g * (q - 1)) / 2)) *
          (3 : ℝ) ^ (1 - (1 + g * (q - 1)) / 2))) *
            (1 + R / c.r) ^ (1 - g * (q - 1))) := by
  let N : ℕ := ⌊T / c.r ^ 2⌋₊ + 1
  have hr := c.positive
  have hr2 : 0 < c.r ^ 2 := sq_pos_of_pos hr
  have hNlo : T / c.r ^ 2 < (N : ℝ) := by
    simpa only [N, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (T / c.r ^ 2)
  have hNhi : (N : ℝ) ≤ T / c.r ^ 2 + 1 := by
    have h := Nat.floor_le (by positivity : 0 ≤ T / c.r ^ 2)
    simp only [N, Nat.cast_add, Nat.cast_one]
    linarith
  have hNhorizon : (N : ℝ) ≤ 2 + (R / c.r) ^ 2 := by
    have ht := div_le_div_of_nonneg_right hTR hr2.le
    rw [div_pow] at ⊢
    linarith
  have hz : ∀ j : ℕ, j ∉ Finset.range (N + 1) →
      (∑' k : ℤ, ENNReal.ofReal (enlargedPositionVisitMass nu c s x j k ^ q)) = 0 := by
    intro j hj
    have hjN : N ≤ j := by
      simp only [Finset.mem_range, not_lt] at hj
      omega
    have hcast : (N : ℝ) ≤ (j : ℝ) := by exact_mod_cast hjN
    have htj : T ≤ (j : ℝ) * c.r ^ 2 := by
      have h := (div_lt_iff₀ hr2).mp hNlo
      exact h.le.trans (mul_le_mul_of_nonneg_right hcast hr2.le)
    have he : ∀ k : ℤ, enlargedPositionVisitMass nu c s x j k = 0 :=
      fun k => enlargedPositionVisitMass_eq_zero_of_horizon nu c s x T j k hs htj
    simp only [he, Real.zero_rpow (by linarith [hq.1] : q ≠ 0), ENNReal.ofReal_zero,
      tsum_zero]
  rw [tsum_eq_sum hz]
  apply (Finset.sum_le_sum (fun j _ =>
    enlargedPositionVisitMass_power_sum_decay_le nu c s x j Ct Cp g q hCt hCp
      hq.1 (htime j) (hcell j))).trans
  have hcoef : 0 ≤ Cp ^ (q - 1) * Ct := mul_nonneg (Real.rpow_nonneg hCp _) hCt
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ =>
    mul_nonneg hcoef (Real.rpow_nonneg (by positivity) _)), ← Finset.mul_sum]
  apply ENNReal.ofReal_le_ofReal
  have h := mul_le_mul_of_nonneg_left
    (position_decay_power_sum_horizon_le g q hg hq R c.r hR.le hr N hNhorizon) hcoef
  exact h.trans_eq (mul_assoc _ _ _).symm

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
