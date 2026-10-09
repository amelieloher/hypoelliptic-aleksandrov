module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsWeightBasic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Quantitative divergence of the actual regularized weight at the singular origin -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Set MeasureTheory Filter
open scoped Topology ENNReal

/-- The regularized origin value has the explicit negative position-scale power lower bound. -/
theorem regularizedBarrierWeight_origin_lower (alpha : ℝ) (ha : 0 < alpha)
    (ha1 : alpha < 1) (n : ℕ) :
    barrierMollifierRadius n ^ ((alpha - 2) / 3) ≤ regularizedBarrierWeight alpha n (0, 0) := by
  let eta := barrierMollifier n
  have heta := barrierMollifier_spec n
  have hi := position_kernel_integrable eta (fun X => bellmanGauge (X, 0) ^ (alpha - 2))
    heta.1.continuous heta.2.1 (barrier_weight_fiber_locallyIntegrable alpha ha ha1 0) 0
  have hiη := (barrierMollifierBump n).integrable_normed (μ := volume)
  have hbound : ∀ᵐ X : ℝ ∂volume,
      eta (0 - X) * barrierMollifierRadius n ^ ((alpha - 2) / 3) ≤
      eta (0 - X) * bellmanGauge (X, 0) ^ (alpha - 2) := by
    filter_upwards [volume.ae_ne (0 : ℝ)] with X hX
    by_cases hη : eta (0 - X) = 0
    · simp only [hη, zero_mul, le_refl]
    have hsupport : 0 - X ∈ Function.support ((barrierMollifierBump n).normed volume) := hη
    rw [(barrierMollifierBump n).support_normed_eq] at hsupport
    have hx : |X| < barrierMollifierRadius n := by
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, zero_sub, abs_neg,
        barrierMollifierBump] using hsupport
    rw [barrier_weight_position_axis]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (abs_pos.mpr hX) hx.le (by linarith)) (heta.2.2.1 _)
  have hh := integral_mono_ae ((hiη.comp_sub_left 0).mul_const
    (barrierMollifierRadius n ^ ((alpha - 2) / 3))) hi hbound
  rw [integral_mul_const, integral_sub_left_eq_self, (barrierMollifierBump n).integral_normed,
    one_mul] at hh
  exact hh

/-- At the origin the regularized weight tends to positive infinity in real values. -/
theorem regularizedBarrierWeight_origin_atTop (alpha : ℝ) (ha : 0 < alpha)
    (ha1 : alpha < 1) :
    Tendsto (fun n => regularizedBarrierWeight alpha n (0, 0)) atTop atTop := by
  have hr : Tendsto barrierMollifierRadius atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨barrierMollifierRadius_tendsto,
      Eventually.of_forall barrierMollifierRadius_pos⟩
  have hh := (tendsto_rpow_neg_nhdsGT_zero (by linarith : (alpha - 2) / 3 < 0)).comp hr
  exact tendsto_atTop_mono (regularizedBarrierWeight_origin_lower alpha ha ha1) hh

/-- The extended regularized weight tends to infinity at the origin, retaining any origin atom. -/
theorem regularizedBarrierWeight_origin_tendsto (alpha : ℝ) (ha : 0 < alpha)
    (ha1 : alpha < 1) :
    Tendsto (fun n => ENNReal.ofReal (regularizedBarrierWeight alpha n (0, 0)))
      atTop (𝓝 ⊤) :=
  ENNReal.tendsto_ofReal_atTop.comp (regularizedBarrierWeight_origin_atTop alpha ha ha1)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
