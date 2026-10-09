module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Calculus
public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Mollification of bounded continuous functions

The admissible test functions: the mollification `moll ρ f = ρ ⋆ f` of a continuous function is
smooth, bounded by `sup |f|` for a probability density `ρ`, tends to `f` as the support of `ρ`
shrinks, and commutes with line derivatives: if `f` has a bounded continuous line derivative `g`
in the direction `w`, then so has `moll ρ f`, with line derivative `moll ρ g`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

open MeasureTheory Set Filter Metric
open scoped Convolution Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]

/-- The mollification `x ↦ ∫ ρ(t) f(x - t) dt`. -/
def moll (ρ f : E → ℝ) : E → ℝ := fun x => ∫ t, ρ t * f (x - t)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
theorem moll_eq_convolution (ρ f : E → ℝ) :
    moll ρ f = (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f : E → ℝ) := by
  funext x
  simp [moll, convolution_def]

/-- The mollification of a continuous function by a smooth compactly supported kernel is smooth. -/
theorem contDiff_moll {ρ f : E → ℝ} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρc : HasCompactSupport ρ)
    (hf : Continuous f) : ContDiff ℝ (⊤ : ℕ∞) (moll ρ f) := by
  rw [moll_eq_convolution]
  exact hρc.contDiff_convolution_left _ hρ hf.locallyIntegrable

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
/-- A probability density preserves bounds. -/
theorem abs_moll_le {ρ f : E → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x = 1)
    (hρi : Integrable ρ) {C : ℝ} (hf : ∀ x, |f x| ≤ C) (x : E) : |moll ρ f x| ≤ C := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hf x)
  have h := norm_integral_le_of_norm_le (hρi.mul_const C)
    (f := fun t => ρ t * f (x - t)) (Filter.Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ0 t)]
      exact mul_le_mul_of_nonneg_left (hf _) (hρ0 t))
  rw [integral_mul_const, hρ1, one_mul] at h
  simpa [moll, Real.norm_eq_abs] using h

omit [FiniteDimensional ℝ E] [(volume : Measure E).IsAddHaarMeasure] in
/-- Mollification commutes with line derivatives. -/
theorem hasDerivAt_moll_line {ρ f g : E → ℝ} (hρi : Integrable ρ) (hf : Continuous f)
    (hg : Continuous g) {Cf Cg : ℝ} (hfb : ∀ x, |f x| ≤ Cf) (hgb : ∀ x, |g x| ≤ Cg) (w : E)
    (hline : ∀ x, HasDerivAt (fun s : ℝ => f (x + s • w)) (g x) 0) (x : E) :
    HasDerivAt (fun s : ℝ => moll ρ f (x + s • w)) (moll ρ g x) 0 := by
  have hmeas : ∀ (h : E → ℝ) (s : ℝ), Continuous h →
      AEStronglyMeasurable (fun t => ρ t * h (x + s • w - t)) volume := fun h s hh =>
    hρi.1.mul (hh.comp (by fun_prop : Continuous fun t : E => x + s • w - t)).aestronglyMeasurable
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun (s : ℝ) (t : E) => ρ t * f (x + s • w - t))
    (F' := fun (s : ℝ) (t : E) => ρ t * g (x + s • w - t)) (x₀ := 0)
    (bound := fun t => ‖ρ t‖ * Cg) (s := univ) univ_mem
    (Filter.Eventually.of_forall fun s => hmeas f s hf) ?_ (hmeas g 0 hg) ?_
    (hρi.norm.mul_const Cg) ?_
  · simpa [moll] using key.2
  · refine Integrable.mono' (hρi.norm.mul_const Cf) (hmeas f 0 hf)
      (Filter.Eventually.of_forall fun t => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (by simpa using hfb _) (norm_nonneg _)
  · refine Filter.Eventually.of_forall fun t s _ => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (by simpa using hgb _) (norm_nonneg _)
  · refine Filter.Eventually.of_forall fun t s₀ _ => ?_
    have h := hline (x + s₀ • w - t)
    have h2 : HasDerivAt (fun s : ℝ => f (x + s₀ • w - t + (s - s₀) • w)) (g (x + s₀ • w - t)) s₀ :=
      HasDerivAt.comp_sub_const s₀ s₀ (by simpa using h)
    have h3 : (fun s : ℝ => f (x + s₀ • w - t + (s - s₀) • w)) =
        fun s : ℝ => f (x + s • w - t) := by
      funext s
      congr 1
      rw [sub_smul]
      abel
    rw [h3] at h2
    exact h2.const_mul (ρ t)

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
