module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.RadialMeasures
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

/-! # Literal integral formulas for the two radial adjoint measures -/

@[expose] public section
noncomputable section
open Set MeasureTheory
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- Integrating the first radial measure integrates the actual radial density before projection. -/
theorem integral_radialMu {lam Lam : ℝ} (alpha : ℝ)
    (pi : Measure (BellmanSphere × BellmanCoefficient lam Lam)) [IsFiniteMeasure pi]
    (f : BellmanPuncturedPlane → ℝ) (hf : Continuous f) :
    (∫ q, f q ∂radialMu alpha pi) =
      ∫ w : BellmanPositiveTime × (BellmanSphere × BellmanCoefficient lam Lam),
        w.1.val ^ (1 - alpha) * f (sphereRadialPoint w)
        ∂bellmanPositiveTimeVolume.prod pi := by
  unfold radialMu
  rw [integral_map (continuous_sphereRadialPoint lam Lam).measurable.aemeasurable
    hf.aestronglyMeasurable]
  have hweight : Measurable (fun w : BellmanPositiveTime ×
      (BellmanSphere × BellmanCoefficient lam Lam) => bellmanRadiusWeight alpha w.1) :=
    (measurable_bellmanRadiusWeight alpha).comp measurable_fst
  unfold bellmanRadiusMeasure
  rw [prod_withDensity_left (measurable_bellmanRadiusWeight alpha),
    integral_withDensity_eq_integral_toReal_smul
      hweight
      (ae_of_all _ (fun w => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  apply ae_of_all
  intro w
  simp only [bellmanRadiusWeight,
    ENNReal.toReal_ofReal (Real.rpow_nonneg w.1.property.le _), smul_eq_mul]

/-- Integrating the second radial measure also retains the literal coefficient weight. -/
theorem integral_radialEta {lam Lam : ℝ} (alpha : ℝ)
    (pi : Measure (BellmanSphere × BellmanCoefficient lam Lam)) [IsFiniteMeasure pi]
    (f : BellmanPuncturedPlane → ℝ) (hf : Continuous f) (hlam : 0 ≤ lam) :
    (∫ q, f q ∂radialEta alpha pi) =
      ∫ w : BellmanPositiveTime × (BellmanSphere × BellmanCoefficient lam Lam),
        w.1.val ^ (1 - alpha) * (w.2.2.val * f (sphereRadialPoint w))
        ∂bellmanPositiveTimeVolume.prod pi := by
  unfold radialEta
  rw [integral_map (continuous_sphereRadialPoint lam Lam).measurable.aemeasurable
    hf.aestronglyMeasurable]
  have hcoeff : Measurable (fun w : BellmanPositiveTime ×
      (BellmanSphere × BellmanCoefficient lam Lam) => ENNReal.ofReal w.2.2.val) := by
    fun_prop
  rw [integral_withDensity_eq_integral_toReal_smul hcoeff
    (ae_of_all _ (fun w => ENNReal.ofReal_lt_top))]
  have hweight : Measurable (fun w : BellmanPositiveTime ×
      (BellmanSphere × BellmanCoefficient lam Lam) => bellmanRadiusWeight alpha w.1) :=
    (measurable_bellmanRadiusWeight alpha).comp measurable_fst
  unfold bellmanRadiusMeasure
  rw [prod_withDensity_left (measurable_bellmanRadiusWeight alpha),
    integral_withDensity_eq_integral_toReal_smul
      hweight
      (ae_of_all _ (fun w => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  apply ae_of_all
  intro w
  simp only [bellmanRadiusWeight, ENNReal.toReal_ofReal (Real.rpow_nonneg w.1.property.le _),
    ENNReal.toReal_ofReal (hlam.trans w.2.2.property.1), smul_eq_mul]

end HypoellipticAleksandrov.KineticAleksandrov
