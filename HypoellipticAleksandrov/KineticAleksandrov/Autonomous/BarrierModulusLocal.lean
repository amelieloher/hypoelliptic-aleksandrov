module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.OriginExtension
import Mathlib.Analysis.Calculus.MeanValue

/-! # Uniform reference-scale increments of the actual Bellman extension -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BarrierRegularization
open HypoellipticAleksandrov Set MeasureTheory

/-- Gauge below one implies product norm at most one, using both kinetic weights. -/
theorem barrier_small_gauge_norm {q : ℝ × ℝ} (hq : bellmanGauge q < 1) : ‖q‖ ≤ 1 := by
  obtain ⟨hX, hv⟩ := bellmanGauge_coordinate_bounds q
  rw [Prod.norm_def, max_le_iff, Real.norm_eq_abs, Real.norm_eq_abs]
  have hpow : bellmanGauge q ^ 3 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (bellmanGauge_nonneg q) hq.le 3
  exact ⟨hX.trans hpow, hv.trans hq.le⟩

/-- A reference-scale axis increment is controlled either by distant jets or a compact ball. -/
theorem barrier_reference_axis_increment (Phi : (ℝ × ℝ) → ℝ)
    (axis : ℝ → ℝ × ℝ)
    (haxisdist : ∀ t u, ‖axis t - axis u‖ ≤ |t - u|)
    (D B : ℝ) (hD : 0 ≤ D) (hB : 0 ≤ B)
    (hball : ∀ q, ‖q‖ ≤ 2 → |Phi q| ≤ B)
    (hderiv : ∀ t, 1 ≤ bellmanGauge (axis t) →
      ∃ g : ℝ, HasDerivAt (Phi ∘ axis) g t ∧ |g| ≤ D)
    (x y : ℝ) (hxy : |y - x| ≤ 1) : |Phi (axis y) - Phi (axis x)| ≤ D + 2 * B := by
  by_cases hfar : ∀ t ∈ uIcc x y, 1 ≤ bellmanGauge (axis t)
  · have hd (t : ℝ) (ht : t ∈ uIcc x y) := hderiv t (hfar t ht)
    have hh := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun t ht => (hd t ht).choose_spec.1.differentiableAt)
      (fun t ht => by
        rw [(hd t ht).choose_spec.1.deriv, Real.norm_eq_abs]
        exact (hd t ht).choose_spec.2)
      (convex_uIcc x y) (left_mem_uIcc) (right_mem_uIcc)
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hh
    exact (hh.trans (mul_le_mul_of_nonneg_left hxy hD)).trans
      (by simpa only [mul_one] using le_add_of_nonneg_right (mul_nonneg (by norm_num) hB))
  · push Not at hfar
    obtain ⟨t, ht, htg⟩ := hfar
    have htq := barrier_small_gauge_norm htg
    have hx : ‖axis x‖ ≤ 2 := by
      have hdist := (haxisdist x t).trans
        (by simpa only [abs_sub_comm] using (abs_sub_left_of_mem_uIcc ht).trans hxy)
      have hh := norm_le_norm_add_norm_sub' (axis x) (axis t)
      linarith only [hdist, hh, htq]
    have hy : ‖axis y‖ ≤ 2 := by
      have hdist := (haxisdist y t).trans ((abs_sub_right_of_mem_uIcc ht).trans hxy)
      have hh := norm_le_norm_add_norm_sub' (axis y) (axis t)
      linarith only [hdist, hh, htq]
    exact (abs_sub _ _).trans (by linarith only [hball _ hx, hball _ hy, hD])

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BarrierRegularization
