module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.RadialMeasuresProper
import Mathlib.Tactic

/-! # Elliptic comparison of the literal radial measure pair -/

@[expose] public section
noncomputable section
open MeasureTheory Set
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- The coefficient interval bounds the two radial measures with the same ellipticity constants. -/
theorem radial_bellman_measures_comparison {lam Lam : ℝ} (alpha : ℝ)
    (pi : Measure (BellmanSphere × BellmanCoefficient lam Lam)) :
    ENNReal.ofReal lam • radialMu alpha pi ≤ radialEta alpha pi ∧
      radialEta alpha pi ≤ ENNReal.ofReal Lam • radialMu alpha pi := by
  let mu := (bellmanRadiusMeasure alpha).prod pi
  have hlo : ENNReal.ofReal lam • mu ≤
      mu.withDensity (fun w => ENNReal.ofReal w.2.2.val) := by
    rw [← withDensity_const]
    exact withDensity_mono (Filter.Eventually.of_forall
      (fun w => ENNReal.ofReal_le_ofReal w.2.2.property.1))
  have hhi : mu.withDensity (fun w => ENNReal.ofReal w.2.2.val) ≤
      ENNReal.ofReal Lam • mu := by
    rw [← withDensity_const]
    exact withDensity_mono (Filter.Eventually.of_forall
      (fun w => ENNReal.ofReal_le_ofReal w.2.2.property.2))
  have hf := (continuous_sphereRadialPoint lam Lam).measurable
  have hl := Measure.map_mono hlo hf
  have hh := Measure.map_mono hhi hf
  rw [Measure.map_smul _ hf.aemeasurable] at hl hh
  exact ⟨hl, hh⟩

end HypoellipticAleksandrov.KineticAleksandrov
