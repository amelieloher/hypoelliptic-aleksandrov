module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsBarrierErrorBounds
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Actual expanding cutoff limits and extended Fatou bounds -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory Filter
open scoped Topology ENNReal

/-- The literal scalar cutoff equals one throughout its inner unit interval. -/
theorem barrierCutoff_eq_one {x : ℝ} (hx : |x| ≤ 1) : barrierCutoff x = 1 := by
  apply barrierCutoffBump.one_of_mem_closedBall
  simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, barrierCutoffBump] using hx

/-- At every physical point, the expanding kinetic cutoff is eventually exactly one. -/
theorem barrierRectCutoff_eventually_one (Y : ℝ) (z : Z) :
    ∀ᶠ n : ℕ in atTop, barrierRectCutoff Y ((n : ℝ) + 1) z = 1 := by
  have hn : ∀ᶠ n : ℕ in atTop, max |z.1 - Y| |z.2| ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [hn] with n hn
  have hR : 1 ≤ (n : ℝ) + 1 := by
    have hn0 : (0 : ℝ) ≤ n := by positivity
    linarith only [hn0]
  have hR0 : 0 < (n : ℝ) + 1 := by positivity
  have hcube : (n : ℝ) + 1 ≤ ((n : ℝ) + 1) ^ 3 := by
    have hh := mul_nonneg hR0.le (show 0 ≤ ((n : ℝ) + 1) ^ 2 - 1 by nlinarith [hR])
    nlinarith only [hh]
  have hx : |z.1 - Y| ≤ ((n : ℝ) + 1) ^ 3 :=
    (le_max_left _ _).trans (hn.trans ((by linarith : (n : ℝ) ≤ n + 1).trans hcube))
  have hv : |z.2| ≤ (n : ℝ) + 1 :=
    (le_max_right _ _).trans (hn.trans (by linarith))
  have hx' : |(z.1 - Y) / ((n : ℝ) + 1) ^ 3| ≤ 1 := by
    rw [abs_div, abs_of_pos (pow_pos hR0 3), div_le_iff₀ (pow_pos hR0 3), one_mul]
    exact hx
  have hv' : |z.2 / ((n : ℝ) + 1)| ≤ 1 := by
    rw [abs_div, abs_of_pos hR0, div_le_iff₀ hR0, one_mul]
    exact hv
  simp only [barrierRectCutoff, barrierCutoff_eq_one hx', barrierCutoff_eq_one hv', one_mul]

/-- Actual integrable endpoint tests converge under the expanding kinetic cutoff. -/
theorem barrierRectCutoff_integral_tendsto (mu : Measure Z) (f : Z → ℝ)
    (hf : Measurable f) (hi : Integrable f mu) (Y : ℝ) :
    Tendsto (fun n : ℕ => ∫ z, barrierRectCutoff Y ((n : ℝ) + 1) z * f z ∂mu)
      atTop (𝓝 (∫ z, f z ∂mu)) := by
  apply tendsto_integral_of_dominated_convergence (fun z => |f z|)
  · intro n
    have hc : Continuous (barrierRectCutoff Y ((n : ℝ) + 1)) := by
      exact (barrierCutoff_contDiff.continuous.comp
        ((continuous_fst.sub continuous_const).div_const _)).mul
          (barrierCutoff_contDiff.continuous.comp (continuous_snd.div_const _))
    exact (hc.measurable.mul hf).aestronglyMeasurable
  · exact hi.abs
  · intro n
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (barrierRectCutoff_bounds _ _ _).1]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (barrierRectCutoff_bounds Y ((n : ℝ) + 1) z).2 (abs_nonneg (f z))
  · filter_upwards with z
    apply Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [barrierRectCutoff_eventually_one Y z] with n hn
    simp only [hn, one_mul]

/-- Extended Fatou passes quantitative finite bounds without removing singular atoms. -/
theorem singular_fatou_of_real_bounds {W : Type*} [MeasurableSpace W]
    (mu : Measure W) (f : ℕ → W → ENNReal) (F : W → ENNReal)
    (hm : ∀ n, Measurable (f n))
    (hp : ∀ w, Tendsto (fun n => f n w) atTop (𝓝 (F w)))
    (b : ℕ → ℝ) (B : ℝ) (hb : Tendsto b atTop (𝓝 B))
    (hi : ∀ n, (∫⁻ w, f n w ∂mu) ≤ ENNReal.ofReal (b n)) :
    (∫⁻ w, F w ∂mu) ≤ ENNReal.ofReal B := by
  have he : (fun w => liminf (fun n => f n w) atTop) = F :=
    funext (fun w => (hp w).liminf_eq)
  rw [← he]
  apply (lintegral_liminf_le hm).trans
  apply (liminf_le_liminf (Eventually.of_forall hi)).trans_eq
  exact ((ENNReal.continuous_ofReal.tendsto B).comp hb).liminf_eq

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
