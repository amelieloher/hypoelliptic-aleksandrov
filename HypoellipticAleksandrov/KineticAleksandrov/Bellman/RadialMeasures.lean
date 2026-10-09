module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.BarrierFunctionSpaceGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDisintegrationDensity
public import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic

/-! # Literal radial measures of a probability on the Bellman sphere and coefficient interval -/

@[expose] public section
noncomputable section
open MeasureTheory Set
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- Positive radial dilation of a unit-gauge point stays away from the origin. -/
theorem sphereRadialPoint_ne_zero {lam Lam : ℝ}
    (w : BellmanPositiveTime × (BellmanSphere × BellmanCoefficient lam Lam)) :
    bellmanPlaneDilation w.1.val w.2.1.val ≠ (0, 0) :=
  bellmanPlaneDilation_ne_zero w.1.val w.1.property w.2.1.val w.2.1.ne_zero

/-- The radial projection uses the source's anisotropic dilation. -/
def sphereRadialPoint {lam Lam : ℝ}
    (w : BellmanPositiveTime × (BellmanSphere × BellmanCoefficient lam Lam)) :
    BellmanPuncturedPlane :=
  ⟨bellmanPlaneDilation w.1.val w.2.1.val, sphereRadialPoint_ne_zero w⟩

/-- The radial weight has exponent one minus the homogeneous function degree. -/
def bellmanRadiusWeight (alpha : ℝ) : BellmanPositiveTime → ENNReal :=
  fun r => ENNReal.ofReal (r.val ^ (1 - alpha))

/-- The source's weighted positive radial volume. -/
def bellmanRadiusMeasure (alpha : ℝ) : Measure BellmanPositiveTime :=
  bellmanPositiveTimeVolume.withDensity (bellmanRadiusWeight alpha)

/-- The first radial adjoint measure is the actual radial pushforward. -/
def radialMu {lam Lam : ℝ} (alpha : ℝ)
    (pi : Measure (BellmanSphere × BellmanCoefficient lam Lam)) :
    Measure BellmanPuncturedPlane :=
  Measure.map sphereRadialPoint ((bellmanRadiusMeasure alpha).prod pi)

/-- The second radial adjoint measure includes the actual diffusion coefficient density. -/
def radialEta {lam Lam : ℝ} (alpha : ℝ)
    (pi : Measure (BellmanSphere × BellmanCoefficient lam Lam)) :
    Measure BellmanPuncturedPlane :=
  Measure.map sphereRadialPoint (((bellmanRadiusMeasure alpha).prod pi).withDensity
    (fun w => ENNReal.ofReal w.2.2.val))

/-- The radial projection is continuous on its actual product carrier. -/
theorem continuous_sphereRadialPoint (lam Lam : ℝ) :
    Continuous (sphereRadialPoint (lam := lam) (Lam := Lam)) := by
  apply Continuous.subtype_mk
  unfold bellmanPlaneDilation
  fun_prop

/-- The radius coordinate is exactly the gauge of the projected point. -/
theorem sphereRadialPoint_gauge {lam Lam : ℝ}
    (w : BellmanPositiveTime × (BellmanSphere × BellmanCoefficient lam Lam)) :
    bellmanGauge (sphereRadialPoint w).val = w.1.val := by
  rw [sphereRadialPoint, bellmanGauge_dilation _ w.1.property, w.2.1.property, mul_one]

/-- The radial weight is a measurable function on strictly positive radii. -/
theorem measurable_bellmanRadiusWeight (alpha : ℝ) :
    Measurable (bellmanRadiusWeight alpha) := by
  unfold bellmanRadiusWeight
  exact (ENNReal.continuous_ofReal.comp
    (continuous_subtype_val.rpow_const (fun r => Or.inl r.property.ne'))).measurable

/-- Continuous radial weights are finite on every compact subset of positive radii. -/
instance bellmanRadiusMeasure_finiteOnCompacts (alpha : ℝ) :
    IsFiniteMeasureOnCompacts (bellmanRadiusMeasure alpha) := by
  have hf : Continuous (fun r : BellmanPositiveTime => r.val ^ (1 - alpha)) :=
    continuous_subtype_val.rpow_const (fun r => Or.inl r.property.ne')
  exact bellman_withDensity_finiteOnCompacts bellmanPositiveTimeVolume _ hf

/-- Positive radial weighted volume is sigma finite on the open radius carrier. -/
instance bellmanRadiusMeasure_sigmaFinite (alpha : ℝ) :
    SigmaFinite (bellmanRadiusMeasure alpha) := by
  let : LocallyCompactSpace BellmanPositiveTime := isOpen_Ioi.locallyCompactSpace
  infer_instance

end HypoellipticAleksandrov.KineticAleksandrov
