module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Squared integral convergence on a common compact support

This module turns a uniform pointwise bound tending to zero into convergence
of squared integrals when all functions share one compact support.
-/

@[expose] public section

open Filter MeasureTheory Set Topology

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- Uniform decay on one compact support implies decay of the squared integral. -/
theorem tendsto_integral_sq_of_common_compact_uniform_bound
    {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
    {μ : Measure α} [IsFiniteMeasureOnCompacts μ]
    (K : TopologicalSpace.Compacts α) (g : ℕ → α → ℝ)
    (hKmeas : MeasurableSet (K : Set α))
    (hgmeas : ∀ n, AEStronglyMeasurable (g n) μ)
    (hgsupport : ∀ n, Function.support (g n) ⊆ (K : Set α))
    (bound : ℕ → ℝ) (hbound0 : Tendsto bound atTop (𝓝 0))
    (hbound : ∀ n x, |g n x| ≤ bound n) :
    Tendsto (fun n => ∫ x, (g n x) ^ 2 ∂μ) atTop (𝓝 0) := by
  let μK : Measure α := μ.restrict (K : Set α)
  letI : IsFiniteMeasure μK := isFiniteMeasure_restrict.mpr K.isCompact.measure_ne_top
  have hsqMeas (n : ℕ) : AEStronglyMeasurable (fun x => (g n x) ^ 2) μ :=
    (hgmeas n).pow 2
  have hsqMemK (n : ℕ) : MemLp (fun x => (g n x) ^ 2) 1 μK := by
    refine MemLp.of_bound ((hsqMeas n).mono_measure Measure.restrict_le_self)
      (|bound n| ^ 2) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_sq]
    simpa only [sq_abs] using
      (pow_le_pow_left₀ (abs_nonneg _) ((hbound n x).trans (le_abs_self _)) 2)
  have hsqIntK (n : ℕ) : Integrable (fun x => (g n x) ^ 2) μK :=
    (hsqMemK n).integrable (by norm_num)
  have hsqInt (n : ℕ) : Integrable (fun x => (g n x) ^ 2) μ := by
    have hindicator : (K : Set α).indicator (fun x => (g n x) ^ 2) =
        fun x => (g n x) ^ 2 := by
      funext x
      by_cases hx : x ∈ (K : Set α)
      · rw [Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx]
        have hgzero : g n x = 0 := by
          by_contra hgne
          exact hx (hgsupport n hgne)
        rw [hgzero, zero_pow (by norm_num : 2 ≠ 0)]
    rw [← hindicator, integrable_indicator_iff hKmeas]
    simpa only [μK, IntegrableOn] using hsqIntK n
  have hlower (n : ℕ) : 0 ≤ ∫ x, (g n x) ^ 2 ∂μ :=
    integral_nonneg fun _ => sq_nonneg _
  have hupper (n : ℕ) :
      (∫ x, (g n x) ^ 2 ∂μ) ≤ μ.real (K : Set α) * bound n ^ 2 := by
    calc
      (∫ x, (g n x) ^ 2 ∂μ) = ∫ x in (K : Set α), (g n x) ^ 2 ∂μ := by
        rw [← integral_indicator hKmeas]
        apply integral_congr_ae
        filter_upwards with x
        by_cases hx : x ∈ (K : Set α)
        · rw [Set.indicator_of_mem hx]
        · rw [Set.indicator_of_notMem hx]
          have hgzero : g n x = 0 := by
            by_contra hgne
            exact hx (hgsupport n hgne)
          rw [hgzero, zero_pow (by norm_num : 2 ≠ 0)]
      _ ≤ ∫ _x in (K : Set α), bound n ^ 2 ∂μ := by
        apply integral_mono_ae (hsqIntK n) (integrable_const (bound n ^ 2))
        filter_upwards with x
        simpa only [sq_abs] using
          (pow_le_pow_left₀ (abs_nonneg _) (hbound n x) 2)
      _ = μ.real (K : Set α) * bound n ^ 2 := by
        rw [integral_const, MeasureTheory.measureReal_restrict_apply_univ, smul_eq_mul]
  have hmajorant : Tendsto (fun n => μ.real (K : Set α) * bound n ^ 2)
      atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : 2 ≠ 0), mul_zero] using
      tendsto_const_nhds.mul (hbound0.pow 2)
  exact squeeze_zero' (Eventually.of_forall hlower) (Eventually.of_forall hupper) hmajorant

end HypoellipticAleksandrov.Parabolic.Dirichlet
