module

public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementApproxSquareNorm
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Bounded almost-everywhere convergence in the literal L2 carrier -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Filter
open scoped Topology

/-- Uniformly bounded functions on a finite measure space converge strongly in L2 when
an actual almost-everywhere pointwise limit is supplied. -/
theorem tendsto_toLp_two_of_bounded_ae
    {E : Type*} [MeasurableSpace E] (μ : Measure E) [IsFiniteMeasure μ]
    (f : ℕ → E → ℝ) (F : E → ℝ)
    (hf : ∀ n, MemLp (f n) 2 μ) (hF : MemLp F 2 μ)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n, ∀ᵐ x ∂μ, |f n x| ≤ C)
    (hFb : ∀ᵐ x ∂μ, |F x| ≤ C)
    (hae : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (F x))) :
    Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hF.toLp F)) := by
  have hbound (n : ℕ) : ∀ᵐ x ∂μ, ‖(f n x - F x) ^ 2‖ ≤ (2 * C) ^ 2 := by
    filter_upwards [hb n, hFb] with x hx hy
    have h := (abs_sub _ _).trans (add_le_add hx hy)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hh := (sq_le_sq₀ (abs_nonneg (f n x - F x))
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hC)).2 (by simpa only [two_mul] using h)
    simpa only [sq_abs] using hh
  have hm (n : ℕ) : AEStronglyMeasurable (fun x => (f n x - F x) ^ 2) μ := by
    have hh := ((hf n).aestronglyMeasurable.sub hF.aestronglyMeasurable).pow 2
    exact hh
  have ha : ∀ᵐ x ∂μ, Tendsto (fun n => (f n x - F x) ^ 2) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hae] with x hx
    have hc : Tendsto (fun _ : ℕ => F x) atTop (𝓝 (F x)) := tendsto_const_nhds
    simpa only [sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using (hx.sub hc).pow 2
  have hlim : Tendsto (fun n => ∫ x, (f n x - F x) ^ 2 ∂μ) atTop (𝓝 0) := by
    have hd := tendsto_integral_of_dominated_convergence (fun _ => (2 * C) ^ 2)
      hm (integrable_const _) hbound ha
    simpa only [integral_zero] using hd
  have hnorm (n : ℕ) : ‖(hf n).toLp (f n) - hF.toLp F‖ ^ 2 =
      ∫ x, (f n x - F x) ^ 2 ∂μ := by
    rw [← (hf n).toLp_sub hF, Lp.norm_toLp]
    exact (Parabolic.LocalHolder.integral_square_eq_eLpNorm_two_sq (f n - F)
      ((hf n).sub hF)).symm
  have hsqrt := Real.continuous_sqrt.tendsto 0 |>.comp hlim
  change Tendsto (fun n => Real.sqrt (∫ x, (f n x - F x) ^ 2 ∂μ))
    atTop (𝓝 (Real.sqrt 0)) at hsqrt
  have hn : Tendsto (fun n => ‖(hf n).toLp (f n) - hF.toLp F‖) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ← hnorm, Real.sqrt_sq (norm_nonneg _),
      Real.sqrt_zero] using hsqrt
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
