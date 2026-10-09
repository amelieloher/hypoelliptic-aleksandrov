module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PatchPowerIteration
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Turning a finite number of uniform doubling losses into a power -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous

/-- A fixed contraction dominates a sufficiently large integer power of one half. -/
theorem return_loss_exponent {c : ℝ} (hc : 0 < c) :
    ∃ m : ℕ, 0 < m ∧ (1 / 2 : ℝ) ^ m ≤ c := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hc (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨n + 1, by omega, ?_⟩
  rw [pow_succ]
  nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n]

/-- Stop doubling at a radius between the fixed cutoff and twice that cutoff. -/
theorem return_doubling_cutoff (r ell : ℝ) (_hr : 0 < r) (hell : 0 < ell)
    (hsmall : ell ≤ r) :
    ∃ N : ℕ, r ≤ returnExpandedRadius ell N ∧ returnExpandedRadius ell N ≤ 2 * r := by
  obtain ⟨n, hn, hn1⟩ := exists_nat_pow_near
    ((one_le_div hell).mpr hsmall) (by norm_num : (1 : ℝ) < 2)
  refine ⟨n + 1, ?_, ?_⟩
  · dsimp [returnExpandedRadius]
    exact ((div_lt_iff₀ hell).mp hn1).le
  · have hh := (le_div_iff₀ hell).mp hn
    dsimp [returnExpandedRadius]
    rw [pow_succ]
    nlinarith

/-- The power loss is bounded by the accumulated uniform contractions. -/
theorem return_loss_power {c ell : ℝ} {m N : ℕ}
    (_hc : 0 ≤ c) (hell : 0 ≤ ell) (hbase : (1 / 2 : ℝ) ^ m ≤ c)
    (hrad : returnExpandedRadius ell N ≤ 1) : ell ^ m ≤ c ^ N := by
  have hR : 0 ≤ returnExpandedRadius ell N := by
    dsimp [returnExpandedRadius]
    positivity
  have hpow : (returnExpandedRadius ell N) ^ m ≤ 1 :=
    pow_le_one₀ hR hrad
  have hcoeff : ((1 / 2 : ℝ) ^ m) ^ N ≤ c ^ N :=
    pow_le_pow_left₀ (pow_nonneg (by norm_num) m) hbase N
  have he : ((1 / 2 : ℝ) ^ m) ^ N * (returnExpandedRadius ell N) ^ m = ell ^ m := by
    dsimp [returnExpandedRadius]
    rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm m N]
    rw [← mul_assoc, ← mul_pow]
    norm_num
  rw [← he]
  exact (mul_le_mul_of_nonneg_left hpow (pow_nonneg (pow_nonneg (by norm_num) m) N)).trans
    (by simpa only [mul_one] using hcoeff)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
