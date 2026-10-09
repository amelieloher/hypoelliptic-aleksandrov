module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.HomogeneousTestLiftWindow
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic

/-! # Absolute integrability of the compact radial test integrands -/

@[expose] public section
noncomputable section
open Set MeasureTheory
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- The radial integrand has compact support for every fixed punctured spatial point. -/
theorem bellman_lift_integrand_compactSupport (alpha : ℝ) (zeta : (ℝ × ℝ) → ℝ)
    (hc : HasCompactSupport zeta) (hs : tsupport zeta ⊆ bellmanPuncturedSet)
    (q : ℝ × ℝ) (hq : q ∈ bellmanPuncturedSet) :
    HasCompactSupport (fun r : BellmanPositiveTime => r.val ^ (-1 - alpha) *
      zeta (bellmanPlaneDilation r.val q)) := by
  obtain ⟨U, _, hqU, _, a, b, ha, _, hwindow⟩ :=
    bellman_compact_test_local_radius_window zeta hc hs q hq
  have hK := bellmanRadiusWindow_isCompact a b ha
  apply hK.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal
  · intro r hr
    have hz : zeta (bellmanPlaneDilation r.val q) ≠ 0 := by
      intro he
      exact hr (by simp only [he, mul_zero])
    exact hwindow q hqU r (subset_tsupport zeta hz)
  · exact hK.isClosed

/-- Compact radial support and continuity prove absolute integrability of the lift integrand. -/
theorem bellman_lift_integrand_integrable (alpha : ℝ) (zeta : (ℝ × ℝ) → ℝ)
    (hz : Continuous zeta) (hc : HasCompactSupport zeta)
    (hs : tsupport zeta ⊆ bellmanPuncturedSet)
    (q : ℝ × ℝ) (hq : q ∈ bellmanPuncturedSet) :
    Integrable (fun r : BellmanPositiveTime => r.val ^ (-1 - alpha) *
      zeta (bellmanPlaneDilation r.val q)) bellmanPositiveTimeVolume := by
  have hd : Continuous (fun r : BellmanPositiveTime => bellmanPlaneDilation r.val q) := by
    unfold bellmanPlaneDilation
    fun_prop
  have hcont : Continuous (fun r : BellmanPositiveTime =>
      r.val ^ (-1 - alpha) * zeta (bellmanPlaneDilation r.val q)) :=
    (continuous_subtype_val.rpow_const
    (fun r : BellmanPositiveTime => Or.inl r.property.ne')).mul (hz.comp hd)
  exact hcont.integrable_of_hasCompactSupport
    (bellman_lift_integrand_compactSupport alpha zeta hc hs q hq)

end HypoellipticAleksandrov.KineticAleksandrov
