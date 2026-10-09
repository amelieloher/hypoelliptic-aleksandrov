module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.RadialMeasures
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.HomogeneousTestLiftWindow
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic

/-! # Absolute integrability for the sphere-probability radial Fubini calculation -/

@[expose] public section
noncomputable section
open Set MeasureTheory
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- A compact punctured test pulls back to compact radial support uniformly over the sphere. -/
theorem bellman_radial_test_compactSupport {lam Lam : ℝ} (alpha : ℝ)
    (g : (ℝ × ℝ) → ℝ) (hc : HasCompactSupport g) (hs : tsupport g ⊆ bellmanPuncturedSet)
    (weight : BellmanSphere × BellmanCoefficient lam Lam → ℝ) :
    HasCompactSupport (fun w : BellmanPositiveTime ×
      (BellmanSphere × BellmanCoefficient lam Lam) =>
      w.1.val ^ (1 - alpha) * (weight w.2 * g (sphereRadialPoint w).val)) := by
  obtain ⟨a, b, ha, _, hbounds⟩ := bellman_compact_test_gauge_bounds g hc hs
  have hK := (bellmanRadiusWindow_isCompact a b ha).prod
    (isCompact_univ : IsCompact (univ : Set (BellmanSphere × BellmanCoefficient lam Lam)))
  apply hK.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal
  · intro w hw
    have hg : g (sphereRadialPoint w).val ≠ 0 := by
      intro hz
      exact hw (by simp only [hz, mul_zero])
    have hb := hbounds _ (subset_tsupport g hg)
    rw [sphereRadialPoint_gauge] at hb
    exact ⟨hb, trivial⟩
  · exact hK.isClosed

/-- Compact radial support proves integrability, including any continuous coefficient weight. -/
theorem bellman_radial_test_integrable {lam Lam : ℝ} (alpha : ℝ)
    (pi : Measure (BellmanSphere × BellmanCoefficient lam Lam)) [IsFiniteMeasure pi]
    (g : (ℝ × ℝ) → ℝ) (hg : Continuous g) (hc : HasCompactSupport g)
    (hs : tsupport g ⊆ bellmanPuncturedSet)
    (weight : BellmanSphere × BellmanCoefficient lam Lam → ℝ) (hw : Continuous weight) :
    Integrable (fun w : BellmanPositiveTime ×
      (BellmanSphere × BellmanCoefficient lam Lam) =>
      w.1.val ^ (1 - alpha) * (weight w.2 * g (sphereRadialPoint w).val))
      (bellmanPositiveTimeVolume.prod pi) := by
  have hr : Continuous (fun w : BellmanPositiveTime ×
      (BellmanSphere × BellmanCoefficient lam Lam) => w.1.val ^ (1 - alpha)) :=
    (continuous_subtype_val.comp continuous_fst).rpow_const
      (fun w => Or.inl w.1.property.ne')
  have hp : Continuous (fun w : BellmanPositiveTime ×
      (BellmanSphere × BellmanCoefficient lam Lam) => (sphereRadialPoint w).val) :=
    continuous_subtype_val.comp (continuous_sphereRadialPoint lam Lam)
  have hcont := hr.mul ((hw.comp continuous_snd).mul (hg.comp hp))
  exact hcont.integrable_of_hasCompactSupport
    (bellman_radial_test_compactSupport alpha g hc hs weight)

end HypoellipticAleksandrov.KineticAleksandrov
