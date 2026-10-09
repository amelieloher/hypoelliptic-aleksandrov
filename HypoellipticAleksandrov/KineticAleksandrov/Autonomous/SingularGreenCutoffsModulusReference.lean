module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsModulusLocal

/-! # Reference position and velocity increments from the actual homogeneous jets -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Set MeasureTheory Filter
open scoped Topology

/-- Off the origin the extension has the original local germ. -/
theorem barrierExtension_eventuallyEq (phi : (ℝ × ℝ) → ℝ) {q : ℝ × ℝ}
    (hq : q ≠ (0, 0)) : bellmanOriginExtension phi =ᶠ[𝓝 q] phi := by
  filter_upwards [bellmanPuncturedSet_isOpen.mem_nhds hq] with z hz
  exact bellmanOriginExtension_eqOn phi hz

/-- A gauge at least one excludes the origin. -/
theorem barrier_gauge_one_ne_zero {q : ℝ × ℝ} (hq : 1 ≤ bellmanGauge q) : q ≠ (0, 0) := by
  intro he
  subst q
  norm_num [bellmanGauge, bellmanGaugePower] at hq

/-- The continuous extension satisfies the same homogeneity including at the origin. -/
theorem barrierExtension_scaling {alpha : ℝ} {phi : (ℝ × ℝ) → ℝ}
    (h : IsBellmanHomogeneous alpha phi) (r : ℝ) (hr : 0 < r) (q : ℝ × ℝ) :
    bellmanOriginExtension phi (bellmanPlaneDilation r q) =
      r ^ alpha * bellmanOriginExtension phi q := by
  by_cases hq : q = (0, 0)
  · subst q
    simp only [bellmanPlaneDilation, mul_zero, bellmanOriginExtension_zero]
  · rw [bellmanOriginExtension_eqOn phi (bellmanPlaneDilation_ne_zero r hr q hq),
      bellmanOriginExtension_eqOn phi hq]
    exact h.2 r hr q hq

/-- One constant controls every reference-scale increment in either coordinate. -/
theorem barrier_reference_increments {alpha : ℝ} {phi : (ℝ × ℝ) → ℝ}
    (h : IsBellmanHomogeneous alpha phi) (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x y v : ℝ, |y - x| ≤ 1 →
      |bellmanOriginExtension phi (y, v) - bellmanOriginExtension phi (x, v)| ≤ D ∧
      |bellmanOriginExtension phi (v, y) - bellmanOriginExtension phi (v, x)| ≤ D := by
  obtain ⟨_, hX, hv, _⟩ := h.origin_jet_bounds
  obtain ⟨CX, hCX, hbX⟩ := hX
  obtain ⟨Cv, hCv, hbv⟩ := hv
  have hψ := h.origin_extension_continuous ha
  obtain ⟨B, hBb⟩ := (isCompact_closedBall (0 : ℝ × ℝ) 2).exists_bound_of_continuousOn
    hψ.continuousOn
  let B' := max B 0
  have hB : 0 ≤ B' := le_max_right _ _
  have hball q (hq : ‖q‖ ≤ 2) : |bellmanOriginExtension phi q| ≤ B' :=
    (by
      have hh := hBb q (by simpa only [Metric.mem_closedBall, dist_zero_right] using hq)
      rw [Real.norm_eq_abs] at hh
      exact hh.trans (le_max_left _ _))
  refine ⟨CX + Cv + 2 * B', by positivity, fun x y v hxy => ?_⟩
  constructor
  · have hh := barrier_reference_axis_increment (bellmanOriginExtension phi)
      (fun t => (t, v)) (fun t u => by
        simp only [Prod.mk_sub_mk, sub_self,
        Prod.norm_def, Real.norm_eq_abs, norm_zero]
        exact max_le le_rfl (abs_nonneg (t - u)))
      CX B' hCX hB hball (fun t ht => ?_) x y hxy
    · exact hh.trans (by linarith only [hCv])
    · have hq := barrier_gauge_one_ne_zero ht
      have hd := (h.1.contDiffAt (bellmanPuncturedSet_isOpen.mem_nhds hq)).differentiableAt
        (by norm_num)
      have he := (barrierExtension_eventuallyEq phi hq).comp_tendsto
        ((continuous_id.prodMk continuous_const).tendsto t)
      refine ⟨bellmanDx phi (t, v), (bellman_hasDerivAt_first hd).congr_of_eventuallyEq he, ?_⟩
      exact (hbX _ hq).trans (by
        have hh := Real.rpow_le_rpow_of_nonpos zero_lt_one ht (by linarith : alpha - 3 ≤ 0)
        simpa only [Real.one_rpow, mul_one] using mul_le_mul_of_nonneg_left hh hCX)
  · have hh := barrier_reference_axis_increment (bellmanOriginExtension phi)
      (fun t => (v, t)) (fun t u => by
        simp only [Prod.mk_sub_mk, sub_self,
        Prod.norm_def, Real.norm_eq_abs, norm_zero]
        exact max_le (abs_nonneg (t - u)) le_rfl)
      Cv B' hCv hB hball (fun t ht => ?_) x y hxy
    · exact hh.trans (by linarith only [hCX])
    · have hq := barrier_gauge_one_ne_zero ht
      have hd := (h.1.contDiffAt (bellmanPuncturedSet_isOpen.mem_nhds hq)).differentiableAt
        (by norm_num)
      have he := (barrierExtension_eventuallyEq phi hq).comp_tendsto
        ((continuous_const.prodMk continuous_id).tendsto t)
      refine ⟨bellmanDv phi (v, t), (bellman_hasDerivAt_second hd).congr_of_eventuallyEq he, ?_⟩
      exact (hbv _ hq).trans (by
        have hh := Real.rpow_le_rpow_of_nonpos zero_lt_one ht (by linarith : alpha - 1 ≤ 0)
        simpa only [Real.one_rpow, mul_one] using mul_le_mul_of_nonneg_left hh hCv)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
