module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Tactic

/-! # Bounded supremum iteration with a geometrically growing error

This is the elementary iteration step in the return-time proof.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Filter Finset
open scoped Topology

/-- Iterated substitution in a nonnegative-coefficient recurrence. -/
theorem return_recurrence_substitution (f : ℕ → ℝ) (q r B : ℝ)
    (hq : 0 ≤ q) (hstep : ∀ n, f n ≤ q * f (n + 1) + B * r ^ n)
    (n N : ℕ) :
    f n ≤ q ^ N * f (n + N) + B * r ^ n * ∑ j ∈ range N, (q * r) ^ j := by
  induction N generalizing n with
  | zero => simp
  | succ N ih =>
    have htail := mul_le_mul_of_nonneg_left (ih (n + 1)) hq
    apply (hstep n).trans
    apply (add_le_add htail (le_refl (B * r ^ n))).trans_eq
    rw [geom_sum_succ, pow_succ]
    simp only [pow_succ]
    have hindex : n + 1 + N = n + (N + 1) := by omega
    rw [hindex]
    ring

/-- A bounded sequence loses the terminal supremum when the absorption ratio is small. -/
theorem return_recurrence_bound (f : ℕ → ℝ) (q r B M : ℝ)
    (hq : 0 ≤ q) (hq1 : q < 1) (hr : 0 ≤ r) (hqr : q * r < 1)
    (hB : 0 ≤ B) (hbounded : ∀ n, f n ≤ M)
    (hstep : ∀ n, f n ≤ q * f (n + 1) + B * r ^ n) :
    f 0 ≤ B / (1 - q * r) := by
  have hsum (N : ℕ) : (∑ j ∈ range N, (q * r) ^ j) ≤ 1 / (1 - q * r) := by
    simpa only [Nat.Ico_zero_eq_range, pow_zero] using
      (geom_sum_Ico_le_of_lt_one (m := 0) (n := N) (mul_nonneg hq hr) hqr)
  have hN (N : ℕ) : f 0 ≤ q ^ N * M + B / (1 - q * r) := by
    have h := return_recurrence_substitution f q r B hq hstep 0 N
    simp only [zero_add, pow_zero, mul_one] at h
    apply h.trans
    exact (add_le_add
      (mul_le_mul_of_nonneg_left (hbounded N) (pow_nonneg hq N))
      (mul_le_mul_of_nonneg_left (hsum N) hB)).trans_eq (by ring)
  have ht : Tendsto (fun N : ℕ => q ^ N * M + B / (1 - q * r)) atTop
      (𝓝 (B / (1 - q * r))) := by
    simpa only [zero_mul, zero_add] using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1).mul_const M).add_const
        (B / (1 - q * r))
  exact ge_of_tendsto ht (Eventually.of_forall hN)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
