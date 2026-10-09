module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.Integral
public import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Tactic

/-!
# Polynomially bounded Taylor remainder for a translated power

Analyticity controls the remainder at zero. A polynomial growth bound then extends it
to the entire nonnegative half-line, as required for domination of Laplace remainders.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

/-- Literal Taylor polynomial of the translated power, truncated before order N. -/
def powerTaylor (q : ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, Ring.choose q n * t ^ n

/-- The analytic partial sum is precisely the scalar binomial polynomial. -/
theorem powerTaylor_eq_partialSum (q : ℝ) (N : ℕ) (t : ℝ) :
    powerTaylor q N t = (binomialSeries ℝ q).partialSum N t := by
  simp only [powerTaylor, binomialSeries, FormalMultilinearSeries.partialSum,
    FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm]

/-- The local analytic remainder has the exact truncation order. -/
theorem powerTaylor_remainder_local (q : ℝ) (N : ℕ) :
    Asymptotics.IsBigO (𝓝 (0 : ℝ))
      (fun t => (1 + t) ^ q - powerTaylor q N t) (fun t => ‖t‖ ^ N) := by
  have h := (Real.one_add_rpow_hasFPowerSeriesAt_zero (a := q))
    |>.isBigO_sub_partialSum_pow N
  simpa only [zero_add, ← powerTaylor_eq_partialSum] using h

/-- A global polynomial bound for the Taylor polynomial and the translated power. -/
theorem powerTaylor_remainder_growth (q : ℝ) (N L : ℕ) (hq : q ≤ (L : ℝ))
    (hN : N ≤ L) (t : ℝ) (ht : 0 ≤ t) :
    ‖(1 + t) ^ q - powerTaylor q N t‖ ≤
      (1 + ∑ n ∈ Finset.range N, ‖Ring.choose q n‖) * (1 + t) ^ L := by
  have hbase : 1 ≤ 1 + t := by linarith only [ht]
  have hf : ‖(1 + t) ^ q‖ ≤ (1 + t) ^ L := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by linarith only [ht]) _)]
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hbase hq
  have hp : ‖powerTaylor q N t‖ ≤
      (∑ n ∈ Finset.range N, ‖Ring.choose q n‖) * (1 + t) ^ L := by
    apply (norm_sum_le _ _).trans
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro n hn
    simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ht n)]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    calc
      t ^ n ≤ (1 + t) ^ n := pow_le_pow_left₀ ht (by linarith) n
      _ ≤ (1 + t) ^ L := pow_le_pow_right₀ hbase ((Finset.mem_range.mp hn).le.trans hN)
  calc
    ‖(1 + t) ^ q - powerTaylor q N t‖ ≤ ‖(1 + t) ^ q‖ + ‖powerTaylor q N t‖ :=
      norm_sub_le _ _
    _ ≤ (1 + t) ^ L + (∑ n ∈ Finset.range N, ‖Ring.choose q n‖) * (1 + t) ^ L :=
      add_le_add hf hp
    _ = _ := by ring

/-- Every finite truncation has a global, polynomially dominated remainder. -/
theorem exists_powerTaylor_remainder_bound (q : ℝ) (N : ℕ) :
    ∃ C : ℝ, ∃ L : ℕ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
      ‖(1 + t) ^ q - powerTaylor q N t‖ ≤ C * t ^ N * (1 + t) ^ L := by
  obtain ⟨n, hn⟩ := exists_nat_gt q
  let L := max n N
  have hq : q ≤ (L : ℝ) := hn.le.trans (by exact_mod_cast le_max_left n N)
  have hN : N ≤ L := le_max_right n N
  obtain ⟨C₀, hC₀, hlocal⟩ := Asymptotics.isBigO_iff'.mp (powerTaylor_remainder_local q N)
  obtain ⟨δ, hδ, hδlocal⟩ := Metric.eventually_nhds_iff.mp hlocal
  let D : ℝ := 1 + ∑ n ∈ Finset.range N, ‖Ring.choose q n‖
  let C : ℝ := max C₀ (D / δ ^ N)
  have hC : 0 < C := hC₀.trans_le (le_max_left _ _)
  refine ⟨C, L, hC, ?_⟩
  intro t ht
  have hbase : 1 ≤ (1 + t) ^ L := one_le_pow₀ (by linarith only [ht])
  by_cases htδ : t < δ
  · have hdist : dist t 0 < δ := by
      rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg ht]
      exact htδ
    have h := hδlocal hdist
    simp only [Real.norm_eq_abs, abs_of_nonneg ht,
      abs_of_nonneg (pow_nonneg ht N)] at h
    exact h.trans ((mul_le_mul_of_nonneg_right (le_max_left C₀ _) (pow_nonneg ht N)).trans
      (le_mul_of_one_le_right (by positivity) hbase))
  · have hδt : δ ≤ t := le_of_not_gt htδ
    have hpow : δ ^ N ≤ t ^ N := pow_le_pow_left₀ hδ.le hδt N
    have hDC : D ≤ C * t ^ N := by
      have hDδ : D ≤ C * δ ^ N := (div_le_iff₀ (pow_pos hδ N)).mp (le_max_right _ _)
      exact hDδ.trans (mul_le_mul_of_nonneg_left hpow hC.le)
    exact (powerTaylor_remainder_growth q N L hq hN t ht).trans
      (mul_le_mul_of_nonneg_right hDC (pow_nonneg (by linarith only [ht]) L))

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
