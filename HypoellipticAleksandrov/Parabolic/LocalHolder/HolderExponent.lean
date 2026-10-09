module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Algebra.Order.Archimedean.Basic

/-! # Choosing a structural Hölder exponent

Continuity at exponent zero supplies an exponent below one. The real power identities
then convert the dyadic geometric envelope into a power of the physical distance.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Filter Set
open scoped Topology

/-- Every contraction factor admits a strictly positive Hölder exponent below one. -/
theorem exists_holder_exponent_of_contraction {q : ℝ} (hq : q < 1) :
    ∃ α : ℝ, 0 < α ∧ α < 1 ∧ q ≤ (1 / 2 : ℝ) ^ α := by
  have hcont : ContinuousAt (fun α : ℝ => (1 / 2 : ℝ) ^ α) 0 :=
    Real.continuousAt_const_rpow (by norm_num)
  have hnhds : {α : ℝ | q < (1 / 2 : ℝ) ^ α} ∈ 𝓝 0 :=
    hcont.preimage_mem_nhds (Ioi_mem_nhds (by simpa only [Real.rpow_zero] using hq))
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hnhds
  let α := min (ε / 2) (1 / 2)
  have hα : 0 < α := lt_min (half_pos hε) (by norm_num)
  have hαε : α < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have hα1 : α < 1 := (min_le_right _ _).trans_lt (by norm_num)
  refine ⟨α, hα, hα1, le_of_lt (hsub ?_)⟩
  change dist α 0 < ε
  simpa only [Real.dist_eq, sub_zero, abs_of_pos hα] using hαε

/-- A dyadic scale chosen above `x` bounds the corresponding geometric decay by `2x`. -/
theorem geometric_decay_le_holder_power {q α x : ℝ}
    (hq : 0 ≤ q) (hα : 0 < α) (hqx : q ≤ (1 / 2 : ℝ) ^ α)
    (n : ℕ) (hn : (1 / 2 : ℝ) ^ (n + 1) < x) :
    q ^ n ≤ (2 * x) ^ α := by
  have hpow : (1 / 2 : ℝ) ^ n < 2 * x := by
    rw [pow_succ] at hn
    linarith only [hn]
  calc q ^ n ≤ ((1 / 2 : ℝ) ^ α) ^ n := pow_le_pow_left₀ hq hqx n
    _ = ((1 / 2 : ℝ) ^ n) ^ α := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
        ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm α (n : ℝ)]
    _ ≤ (2 * x) ^ α := Real.rpow_le_rpow (pow_nonneg (by norm_num) n) hpow.le hα.le

end HypoellipticAleksandrov.Parabolic.LocalHolder
