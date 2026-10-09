module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothed.Mollifier
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.MeasureTheory.Group.Integral

/-!
# A sequence of time mollifiers and Lebesgue-point convergence

the mollifiers
`η_n` supported in `(-1/(n+2), 1/(n+2))`, and the almost-everywhere convergence
`∫ η_n(τ - s) g(s) ds → g(τ)` for locally integrable `g` (Lebesgue differentiation).
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory Filter Topology

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

/-- The radius `1/(n+2)`. -/
def mollRadius (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)

theorem mollRadius_pos (n : ℕ) : 0 < mollRadius n := by unfold mollRadius; positivity

/-- The `n`-th bump. -/
def mollBump (n : ℕ) : ContDiffBump (0 : ℝ) :=
  ⟨mollRadius n / 2, mollRadius n, by linarith [mollRadius_pos n], by linarith [mollRadius_pos n]⟩

/-- The `n`-th mollifier, of integral one and supported in `(-1/(n+2), 1/(n+2))`. -/
def mollN (n : ℕ) : ℝ → ℝ := (mollBump n).normed volume

theorem isMollifier_mollN (n : ℕ) : IsMollifier (mollRadius n) (mollN n) := by
  refine ⟨(mollBump n).contDiff_normed, (mollBump n).nonneg_normed, fun t ht => ?_,
    (mollBump n).integral_normed⟩
  by_contra hne
  have : t ∈ Function.support ((mollBump n).normed volume) := hne
  rw [(mollBump n).support_normed_eq] at this
  simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at this
  exact absurd ht (not_le.2 this)

theorem tendsto_mollRadius : Tendsto mollRadius atTop (𝓝 0) := by
  unfold mollRadius
  have : Tendsto (fun n : ℕ => ((n : ℝ) + 2)) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  simp only [one_div]
  exact tendsto_inv_atTop_zero.comp this

theorem ae_tendsto_mollify {g : ℝ → ℝ} (hg : LocallyIntegrable g volume) :
    ∀ᵐ τ : ℝ, Tendsto (fun n => ∫ s, mollN n (τ - s) * g s) atTop (𝓝 (g τ)) := by
  have hφ : Tendsto (fun n => (mollBump n).rOut) atTop (𝓝 0) := tendsto_mollRadius
  have h'φ : ∀ᶠ n in atTop, (mollBump n).rOut ≤ 2 * (mollBump n).rIn :=
    Eventually.of_forall fun n => by
      change mollRadius n ≤ 2 * (mollRadius n / 2); linarith
  filter_upwards [ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (μ := (volume : Measure ℝ)) (φ := mollBump) (l := atTop) (K := 2) hφ h'φ hg] with τ hτ
  refine hτ.congr fun n => ?_
  simp only [convolution, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have := integral_sub_left_eq_self (fun s => mollN n s * g (τ - s)) (volume : Measure ℝ) τ
  simp only [sub_sub_cancel] at this
  exact this.symm

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
