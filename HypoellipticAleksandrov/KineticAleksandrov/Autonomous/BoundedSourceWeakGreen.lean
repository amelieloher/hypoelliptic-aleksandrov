module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoundedSourceLimits
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripGreenSupport
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.GreenPotentialsGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.DuhamelTheorem

/-! # Green identification for ambient sources that may meet the velocity faces -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo TheoremA

/-- A native interior point determines a valid physical pole by exchanging coordinates. -/
def nativeStripPole (H : Interval) (T : ℝ) (p : Point)
    (hp : p ∈ evolutionPastOpenCylinder (intervalDomain H) (fun _ => 0) T) :
    StripPole H (T : WithTop ℝ) :=
  ⟨sectionTwoPoint p, WithTop.coe_lt_coe.mpr hp.1, by
    have hv : p.position ∈ intervalDomain H := by
      simpa only [movingDomain, PDE.mem_translateSet_iff_sub_mem, sub_zero] using hp.2
    simpa only [sectionTwoPoint, Interval.carrier, PDE.vecOneCoordinate] using
      PDE.mem_oneDimensionalAxisBox_iff.mp hv⟩

/-- The existing Duhamel potential equals the actual physical Green integral even when the
ambient nonnegative compact source reaches the velocity faces. No interior support is needed. -/
theorem duhamelPotential_eq_stripGreen (H : Interval)
    (K : MovingFiberKernel (intervalDomain H) (fun _ => 0)) (T : ℝ)
    (g : Point → ℝ) (hgn : ∀ p, 0 ≤ g p) (hg : Continuous g) (hgc : HasCompactSupport g)
    (p : Point) (hp : p ∈ evolutionPastOpenCylinder (intervalDomain H) (fun _ => 0) T) :
    duhamelPotential K T g p =
      ∫ q, g (sectionTwoPoint q) ∂stripGreenOfKernel H K T (nativeStripPole H T p hp) := by
  rw [stripGreenOfKernel,
    integral_map (measurable_elapsedPhysicalPoint _ _).aemeasurable
      (show AEStronglyMeasurable (fun q : Point => g (sectionTwoPoint q)) _ from
        (hg.comp (continuous_sectionTwoPoint 1)).measurable.aestronglyMeasurable)]
  exact duhamelPotential_eq_greenMeasure K (intervalDomain_measurable H)
    continuous_const T g hgn hg hgc p.time hp.1
    (stripPoleState H T (nativeStripPole H T p hp))

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
