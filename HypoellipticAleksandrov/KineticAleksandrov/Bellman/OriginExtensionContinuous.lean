module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.OriginJetsBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # The continuous zero extension of a positive-degree Bellman function -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open Set Filter
open scoped Topology

/-- Extend the punctured homogeneous function by its forced value zero at the origin. -/
def bellmanOriginExtension (phi : (ℝ × ℝ) → ℝ) (q : ℝ × ℝ) : ℝ :=
  if q = (0, 0) then 0 else phi q

/-- The extension has zero origin value. -/
theorem bellmanOriginExtension_zero (phi : (ℝ × ℝ) → ℝ) :
    bellmanOriginExtension phi (0, 0) = 0 := ite_eq_left rfl

/-- The extension retains the given punctured function. -/
theorem bellmanOriginExtension_eqOn (phi : (ℝ × ℝ) → ℝ) :
    EqOn (bellmanOriginExtension phi) phi bellmanPuncturedSet :=
  fun _ hq => ite_eq_right hq

/-- Positive homogeneous degree forces continuity of the extension at the origin. -/
theorem IsBellmanHomogeneous.origin_extension_continuous {alpha : ℝ}
    {phi : (ℝ × ℝ) → ℝ} (h : IsBellmanHomogeneous alpha phi) (ha : 0 < alpha) :
    Continuous (bellmanOriginExtension phi) := by
  obtain ⟨C, hC, hCb⟩ := h.origin_jet_bounds.1
  have hbound (q : ℝ × ℝ) :
      |bellmanOriginExtension phi q| ≤ C * bellmanGauge q ^ alpha := by
    by_cases hq : q = (0, 0)
    · rw [hq, bellmanOriginExtension_zero, abs_zero]
      exact mul_nonneg hC (Real.rpow_nonneg (bellmanGauge_nonneg _) _)
    · rw [bellmanOriginExtension, ite_eq_right hq]
      exact hCb q hq
  apply continuous_iff_continuousAt.mpr
  intro q
  by_cases hq : q = (0, 0)
  · subst q
    rw [ContinuousAt, bellmanOriginExtension_zero]
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hb : Tendsto (fun q => C * bellmanGauge q ^ alpha) (𝓝 (0, 0)) (𝓝 0) := by
      have hc : Continuous (fun q : ℝ × ℝ => C * bellmanGauge q ^ alpha) :=
        continuous_const.mul ((Real.continuous_rpow_const ha.le).comp bellmanGauge_continuous)
      have hh := hc.continuousAt.tendsto (x := (0, 0))
      simpa only [bellmanGauge, bellmanGaugePower, zero_pow (by decide : (2 : ℕ) ≠ 0),
        zero_pow (by decide : (6 : ℕ) ≠ 0), zero_add,
        Real.zero_rpow (by norm_num : (1 / 6 : ℝ) ≠ 0), Real.zero_rpow ha.ne',
        mul_zero] using hh
    apply squeeze_zero (fun _ => norm_nonneg _) (fun q => ?_) hb
    rw [Real.norm_eq_abs]
    exact hbound q
  · have he : bellmanOriginExtension phi =ᶠ[𝓝 q] phi := by
      filter_upwards [bellmanPuncturedSet_isOpen.mem_nhds hq] with z hz
      exact bellmanOriginExtension_eqOn phi hz
    exact (h.1.contDiffAt (bellmanPuncturedSet_isOpen.mem_nhds hq)).continuousAt.congr he.symm

end HypoellipticAleksandrov.KineticAleksandrov
