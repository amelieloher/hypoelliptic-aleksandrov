module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsConvolutionModulus
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Actual shrinking normalized position mollifiers -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open MeasureTheory Filter Set
open scoped Topology Convolution

/-- The positive position smoothing radius tends to zero. -/
def barrierMollifierRadius (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

/-- Every smoothing radius is strictly positive. -/
theorem barrierMollifierRadius_pos (n : ℕ) : 0 < barrierMollifierRadius n := by
  dsimp only [barrierMollifierRadius]
  positivity

/-- The source position bump at the actual shrinking radius. -/
def barrierMollifierBump (n : ℕ) : ContDiffBump (0 : ℝ) :=
  ⟨barrierMollifierRadius n / 2, barrierMollifierRadius n,
    half_pos (barrierMollifierRadius_pos n), half_lt_self (barrierMollifierRadius_pos n)⟩

/-- The actual nonnegative normalized smooth position mollifier. -/
def barrierMollifier (n : ℕ) : ℝ → ℝ := (barrierMollifierBump n).normed volume

/-- Every sequence member satisfies the mollifier conditions. -/
theorem barrierMollifier_spec (n : ℕ) : IsNonnegativeUnitSmoothMollifier (barrierMollifier n) :=
  ⟨(barrierMollifierBump n).contDiff_normed,
    (barrierMollifierBump n).hasCompactSupport_normed,
    (barrierMollifierBump n).nonneg_normed, (barrierMollifierBump n).integral_normed⟩

/-- The outer support radii tend to zero. -/
theorem barrierMollifierRadius_tendsto :
    Tendsto barrierMollifierRadius atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- The actual position-smoothed continuous barrier converges at every physical point. -/
theorem barrier_position_mollifier_tendsto {alpha : ℝ} {phi : (ℝ × ℝ) → ℝ}
    (h : IsBellmanHomogeneous alpha phi) (ha : 0 < alpha) (q : ℝ × ℝ) :
    Tendsto (fun n => positionConvolution (barrierMollifier n)
      (bellmanOriginExtension phi) q) atTop (𝓝 (bellmanOriginExtension phi q)) := by
  have hc : Continuous (fun X : ℝ => bellmanOriginExtension phi (X, q.2)) :=
    (h.origin_extension_continuous ha).comp (continuous_id.prodMk continuous_const)
  have hh := ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume)
    (φ := barrierMollifierBump) barrierMollifierRadius_tendsto hc q.1
  simpa only [positionConvolution_displacement, barrierMollifier, convolution_def,
    ContinuousLinearMap.lsmul_apply, smul_eq_mul] using hh

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
