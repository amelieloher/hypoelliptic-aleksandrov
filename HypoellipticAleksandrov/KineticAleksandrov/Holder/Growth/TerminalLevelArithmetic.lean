module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.ParameterChoice
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-! # Exact scalar induction and leakage choice for the source density ladder -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth

open scoped BigOperators

/-- The power sum has the shifted recurrence used in the density ladder. -/
theorem ladder_power_sum_succ (q : ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), q ^ k) =
      q * (∑ k ∈ Finset.range n, q ^ k) + 1 := by
  rw [Finset.sum_range_succ']
  simp only [pow_succ, pow_zero]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The exact source ladder gives its terminal-level lower bound by numeric induction. -/
theorem density_ladder_numeric {a beta L0 : ℝ} (ha : 0 < a) (e : ℕ → ℝ) (N : ℕ)
    (hzero : beta ≤ e 0) (hstep : ∀ j < N, e j ≤ a * (e (j + 1) + L0)) :
    a⁻¹ ^ N * beta - L0 * (∑ k ∈ Finset.range N, a⁻¹ ^ k) ≤ e N := by
  have hrec : ∀ j < N, a⁻¹ * e j - L0 ≤ e (j + 1) := by
    intro j hj
    have he := mul_le_mul_of_nonneg_left (hstep j hj) (inv_nonneg.mpr ha.le)
    rw [← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul] at he
    linarith only [he]
  have hbound : ∀ n, n ≤ N →
      a⁻¹ ^ n * beta - L0 * (∑ k ∈ Finset.range n, a⁻¹ ^ k) ≤ e n := by
    intro n
    induction n with
    | zero => intro _; simpa only [pow_zero, one_mul, Finset.range_zero,
        Finset.sum_empty, mul_zero, sub_zero] using hzero
    | succ n ih =>
      intro hn
      have he := mul_le_mul_of_nonneg_left (ih (Nat.le_of_succ_le hn))
        (inv_nonneg.mpr ha.le)
      have hr := hrec n (Nat.lt_of_succ_le hn)
      rw [ladder_power_sum_succ, pow_succ]
      nlinarith only [he, hr]
  exact hbound N le_rfl

/-- Fixing N first allows the source leakage radius to be chosen strictly positive and small. -/
theorem exists_density_leakage_choice {a eta beta C V : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (_heta1 : eta < 1) (hbeta : 0 < beta) (hC : 0 < C) (hV : 0 < V)
    (m : ℕ) (hm : 0 < m) :
    ∃ N : ℕ, 1 ≤ N ∧ a⁻¹ ^ N * beta > 1 - eta ∧
      ∃ r0 : ℝ, 0 < r0 ∧ r0 < 1 ∧
        (C * (m : ℝ) * r0 ^ 2 / V) * (∑ k ∈ Finset.range N, a⁻¹ ^ k) <
          a⁻¹ ^ N * beta - (1 - eta) := by
  have hq : 1 < a⁻¹ := (one_lt_inv₀ ha).mpr ha1
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((1 - eta) / beta) hq
  let N := n + 1
  have hN : 1 ≤ N := by dsimp only [N]; omega
  have hn' : a⁻¹ ^ n ≤ a⁻¹ ^ N := pow_le_pow_right₀ hq.le (Nat.le_succ n)
  have hbig : 1 - eta < a⁻¹ ^ N * beta := by
    exact (div_lt_iff₀ hbeta).mp (hn.trans_le hn')
  let S := ∑ k ∈ Finset.range N, a⁻¹ ^ k
  have hS : 0 < S := Finset.sum_pos (fun k _ => pow_pos (inv_pos.mpr ha) k)
    (Finset.nonempty_range_iff.mpr (by omega))
  let D := (C * (m : ℝ) / V) * S
  have hD : 0 < D := mul_pos (div_pos (mul_pos hC (Nat.cast_pos.mpr hm)) hV) hS
  let gap := a⁻¹ ^ N * beta - (1 - eta)
  have hgap : 0 < gap := sub_pos.mpr hbig
  let r0 := min (1 / 2 : ℝ) (Real.sqrt (gap / (2 * D)))
  have hr0 : 0 < r0 := lt_min (by norm_num) (Real.sqrt_pos.mpr (by positivity))
  have hr01 : r0 < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hrsq : r0 ^ 2 ≤ gap / (2 * D) := by
    have he := (sq_le_sq₀ hr0.le (Real.sqrt_nonneg _)).mpr (min_le_right _ _)
    rwa [Real.sq_sqrt (by positivity : 0 ≤ gap / (2 * D))] at he
  have hhalf : D * r0 ^ 2 ≤ gap / 2 := by
    have he := mul_le_mul_of_nonneg_left hrsq hD.le
    apply he.trans_eq
    field_simp
  refine ⟨N, hN, hbig, r0, hr0, hr01, ?_⟩
  have heq : (C * (m : ℝ) * r0 ^ 2 / V) * S = D * r0 ^ 2 := by
    dsimp only [D]
    ring
  rw [heq]
  exact hhalf.trans_lt (by dsimp only [gap] at hgap ⊢; linarith only [hgap])

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth
