module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.HeatBarrier
import Mathlib.Topology.Algebra.Order.Field

/-! # Positive-time regularity and terminal limit of the half-line killing barrier -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open Set Filter Topology

/-- The heat barrier is jointly smooth wherever its time parameter is positive. -/
theorem contDiffAt_intervalHeat {lam : ℝ} (hlam : 0 < lam)
    (p : ℝ × ℝ) (hp : 0 < p.1) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => intervalHeat lam q.1 q.2) p := by
  have hs : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => Real.sqrt (lam * q.1)) p :=
    (contDiffAt_const.mul contDiffAt_fst).sqrt (mul_pos hlam hp).ne'
  exact contDiff_intervalErf.contDiffAt.comp p
    (contDiffAt_snd.div (contDiffAt_const.mul hs)
      (mul_ne_zero (by norm_num) (Real.sqrt_pos.2 (mul_pos hlam hp)).ne'))

/-- Positive distance has terminal heat-barrier limit one as time decreases to zero. -/
theorem tendsto_intervalHeat_time_zero {lam x : ℝ} (hlam : 0 < lam) (hx : 0 < x) :
    Tendsto (fun θ => intervalHeat lam θ x) (nhdsWithin 0 (Ioi 0)) (𝓝 1) := by
  have hs : Tendsto (fun θ : ℝ => 2 * Real.sqrt (lam * θ))
      (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
    have ht : Tendsto (fun θ : ℝ => θ) (nhdsWithin 0 (Ioi 0)) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hm : Tendsto (fun θ : ℝ => lam * θ) (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
      simpa only [mul_zero] using (tendsto_const_nhds.mul ht)
    have hq := Real.continuous_sqrt.continuousAt.tendsto.comp hm
    simpa only [Real.sqrt_zero, mul_zero] using
      (tendsto_const_nhds.mul hq : Tendsto (fun θ : ℝ => 2 * Real.sqrt (lam * θ))
        (nhdsWithin 0 (Ioi 0)) (𝓝 (2 * Real.sqrt 0)))
  have hsg : Tendsto (fun θ : ℝ => 2 * Real.sqrt (lam * θ))
      (nhdsWithin 0 (Ioi 0)) (nhdsWithin 0 (Ioi 0)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hs, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with θ hθ
    exact mul_pos (by norm_num) (Real.sqrt_pos.2 (mul_pos hlam hθ))
  have hr := hsg.inv_tendsto_nhdsGT_zero.const_mul_atTop hx
  have he := tendsto_intervalErf_atTop.comp hr
  simpa only [intervalHeat, div_eq_mul_inv, Pi.inv_apply, Function.comp_def] using he

/-- Fixed positive-time heat barriers are increasing with spatial distance. -/
theorem intervalHeat_mono_distance {lam θ : ℝ} (hlam : 0 < lam) (hθ : 0 < θ) :
    Monotone (intervalHeat lam θ) := by
  intro x y hxy
  exact strictMono_intervalErf.monotone
    ((div_le_div_iff_of_pos_right (mul_pos (by norm_num)
      (Real.sqrt_pos.2 (mul_pos hlam hθ)))).mpr hxy)

end HypoellipticAleksandrov.KineticAleksandrov.Interval
