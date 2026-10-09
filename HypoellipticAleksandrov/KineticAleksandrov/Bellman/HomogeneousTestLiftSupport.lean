module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.HomogeneousTestLift
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AnnularNormalizationGeometry
import Mathlib.Tactic

/-! # Uniform positive radial windows for compact tests away from the origin -/

@[expose] public section
noncomputable section
open Set Filter Topology MeasureTheory
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- A compact test away from zero has a positive lower and finite upper gauge bound. -/
theorem bellman_compact_test_gauge_bounds (zeta : (ℝ × ℝ) → ℝ)
    (hc : HasCompactSupport zeta) (hs : tsupport zeta ⊆ bellmanPuncturedSet) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ ∀ q ∈ tsupport zeta,
      a ≤ bellmanGauge q ∧ bellmanGauge q ≤ b := by
  by_cases hn : (tsupport zeta).Nonempty
  · obtain ⟨q0, hq0, hlo⟩ := hc.exists_isMinOn hn bellmanGauge_continuous.continuousOn
    obtain ⟨q1, hq1, hhi⟩ := hc.exists_isMaxOn hn bellmanGauge_continuous.continuousOn
    exact ⟨bellmanGauge q0, bellmanGauge q1, bellmanGauge_pos q0 (hs hq0),
      hhi hq0, fun q hq => ⟨hlo hq, hhi hq⟩⟩
  · exact ⟨1, 1, by norm_num, le_rfl, fun q hq => (hn ⟨q, hq⟩).elim⟩

/-- Each punctured spatial point has a neighborhood sharing one compact positive radial window. -/
theorem bellman_compact_test_local_radius_window (zeta : (ℝ × ℝ) → ℝ)
    (hc : HasCompactSupport zeta) (hs : tsupport zeta ⊆ bellmanPuncturedSet)
    (q : ℝ × ℝ) (hq : q ∈ bellmanPuncturedSet) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ q ∈ U ∧ U ⊆ bellmanPuncturedSet ∧
      ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧
        ∀ x ∈ U, ∀ r : BellmanPositiveTime,
          bellmanPlaneDilation r.val x ∈ tsupport zeta → r.val ∈ Icc a b := by
  obtain ⟨a0, b0, ha0, hab0, hbounds⟩ := bellman_compact_test_gauge_bounds zeta hc hs
  have hg : 0 < bellmanGauge q := bellmanGauge_pos q hq
  let U := {x : ℝ × ℝ | bellmanGauge q / 2 < bellmanGauge x ∧
    bellmanGauge x < 2 * bellmanGauge q}
  have hU : IsOpen U :=
    (isOpen_lt continuous_const bellmanGauge_continuous).inter
      (isOpen_lt bellmanGauge_continuous continuous_const)
  have hqU : q ∈ U := ⟨half_lt_self hg, by linarith⟩
  have hsub : U ⊆ bellmanPuncturedSet := by
    intro x hx hz
    have hh := hx.1
    have hzero : bellmanGauge (0, 0) = 0 := by
      norm_num [bellmanGauge, bellmanGaugePower]
    rw [hz, hzero] at hh
    linarith
  refine ⟨U, hU, hqU, hsub, a0 / (2 * bellmanGauge q),
    2 * b0 / bellmanGauge q, div_pos ha0 (by positivity), ?_, ?_⟩
  · apply (div_le_div_iff₀ (by positivity) hg).mpr
    nlinarith [mul_pos ha0 hg]
  · intro x hx r hr
    obtain ⟨hlo, hhi⟩ := hbounds _ hr
    rw [bellmanGauge_dilation _ r.property] at hlo hhi
    constructor
    · apply (div_le_iff₀ (by positivity)).mpr
      nlinarith [mul_pos r.property (sub_pos.mpr hx.2)]
    · apply (le_div_iff₀ hg).mpr
      nlinarith [mul_pos r.property (sub_pos.mpr hx.1)]

end HypoellipticAleksandrov.KineticAleksandrov
