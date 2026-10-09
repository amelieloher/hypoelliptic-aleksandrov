module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureJets
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasurePlaneScaling
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Tactic

/-! # Spatial integration by parts for the explicit Kolmogorov Gaussian -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory

/-- A continuous factor times a continuous compactly supported test is integrable. -/
theorem bellman_integrable_mul_test {f g : ℝ × ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hc : HasCompactSupport g) :
    Integrable (fun q => f q * g q) :=
  (hf.mul hg).integrable_of_hasCompactSupport hc.mul_left

/-- Integration by parts for smooth functions with a compactly supported right factor. -/
theorem bellman_integral_mul_direction {f g : ℝ × ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hc : HasCompactSupport g) (v : ℝ × ℝ) :
    (∫ q, f q * fderiv ℝ g q v) = -(∫ q, fderiv ℝ f q v * g q) := by
  let : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    infer_instance
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact bellman_integrable_mul_test (bellman_contDiff_direction hf v).continuous
      hg.continuous hc
  · exact bellman_integrable_mul_test hf.continuous
      (bellman_contDiff_direction hg v).continuous (hc.fderiv_apply ℝ v)
  · exact bellman_integrable_mul_test hf.continuous hg.continuous hc
  · exact fun q _ => hf.differentiable (by simp) q
  · exact fun q _ => hg.differentiable (by simp) q

/-- Spatial transfer of the Kolmogorov generator from the test to the Gaussian. -/
theorem bellmanGaussianKernel_integral_generator (t : BellmanPositiveTime)
    (φ : ℝ × ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) :
    (∫ q, bellmanGaussianKernel t q *
      (q.2 * fderiv ℝ φ q (1, 0) +
        fderiv ℝ (fun z => fderiv ℝ φ z (0, 1)) q (0, 1))) =
    ∫ q, (-q.2 * fderiv ℝ (bellmanGaussianKernel t) q (1, 0) +
      fderiv ℝ (fun z => fderiv ℝ (bellmanGaussianKernel t) z (0, 1)) q (0, 1)) *
        φ q := by
  have hk := contDiff_bellmanGaussianKernel t
  have hvφ : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => q.2 * φ q) :=
    contDiff_snd.mul hφ
  have hd (q : ℝ × ℝ) : fderiv ℝ (fun z : ℝ × ℝ => z.2 * φ z) q (1, 0) =
      q.2 * fderiv ℝ φ q (1, 0) := by
    rw [fderiv_fun_mul differentiableAt_snd (hφ.differentiable (by simp) q)]
    simp [fderiv_snd]
  have hx := bellman_integral_mul_direction hk hvφ hc.mul_left (1, 0)
  simp only [hd] at hx
  have hv := bellman_integral_mul_direction hk (bellman_contDiff_direction hφ (0, 1))
    (hc.fderiv_apply ℝ (0, 1)) (0, 1)
  have hv2 := bellman_integral_mul_direction (bellman_contDiff_direction hk (0, 1)) hφ
    hc (0, 1)
  rw [hv2, neg_neg] at hv
  have hiX : Integrable (fun q => bellmanGaussianKernel t q *
      (q.2 * fderiv ℝ φ q (1, 0))) :=
    bellman_integrable_mul_test hk.continuous
      (continuous_snd.mul (bellman_contDiff_direction hφ (1, 0)).continuous)
      (hc.fderiv_apply ℝ (1, 0)).mul_left
  have hiV : Integrable (fun q => bellmanGaussianKernel t q *
      fderiv ℝ (fun z => fderiv ℝ φ z (0, 1)) q (0, 1)) :=
    bellman_integrable_mul_test hk.continuous
      (bellman_contDiff_direction (bellman_contDiff_direction hφ (0, 1)) (0, 1)).continuous
      ((hc.fderiv_apply ℝ (0, 1)).fderiv_apply ℝ (0, 1))
  have hjX : Integrable (fun q => -q.2 * fderiv ℝ (bellmanGaussianKernel t) q (1, 0) *
      φ q) := bellman_integrable_mul_test
        (continuous_snd.neg.mul (bellman_contDiff_direction hk (1, 0)).continuous)
        hφ.continuous hc
  have hjV : Integrable (fun q =>
      fderiv ℝ (fun z => fderiv ℝ (bellmanGaussianKernel t) z (0, 1)) q (0, 1) * φ q) :=
    bellman_integrable_mul_test
      (bellman_contDiff_direction (bellman_contDiff_direction hk (0, 1)) (0, 1)).continuous
      hφ.continuous hc
  simp only [mul_add, add_mul]
  rw [integral_add hiX hiV, integral_add hjX hjV, hx, hv]
  congr 1
  rw [← integral_neg]
  congr 1
  funext q
  ring

end HypoellipticAleksandrov.KineticAleksandrov
