module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Continuity of L2 pairings

This module derives convergence of scalar pairings from convergence of squared L2 errors.
-/

@[expose] public section

open Filter MeasureTheory Topology

noncomputable section

/-- Pairing with a fixed L2 function preserves convergence to zero of squared L2 errors. -/
theorem tendsto_integral_mul_of_memLp_two_of_tendsto_integral_sq
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {U : α → ℝ} {g : ℕ → α → ℝ}
    (hU : MemLp U 2 μ)
    (hg : ∀ n, MemLp (g n) 2 μ)
    (hg0 : Tendsto (fun n => ∫ x, (g n x) ^ 2 ∂μ) atTop (nhds 0)) :
    Tendsto (fun n => ∫ x, U x * g n x ∂μ) atTop (nhds 0) := by
  have hroot : Tendsto (fun n => Real.sqrt (∫ x, (g n x) ^ 2 ∂μ))
      atTop (nhds 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hg0
  have hmajor : Tendsto
      (fun n => Real.sqrt (∫ x, U x ^ 2 ∂μ) * Real.sqrt (∫ x, (g n x) ^ 2 ∂μ))
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hroot
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (Eventually.of_forall fun n => ?_) hmajor
  calc
    ‖∫ x, U x * g n x ∂μ‖ ≤ ∫ x, ‖U x * g n x‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ = ∫ x, ‖U x‖ * ‖g n x‖ ∂μ := by simp only [norm_mul]
    _ ≤ (∫ x, ‖U x‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
        (∫ x, ‖g n x‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) :=
      integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
        (by simpa using hU) (by simpa using hg n)
    _ = Real.sqrt (∫ x, U x ^ 2 ∂μ) * Real.sqrt (∫ x, (g n x) ^ 2 ∂μ) := by
      simp only [Real.sqrt_eq_rpow, Real.norm_eq_abs, Real.rpow_two, sq_abs]
