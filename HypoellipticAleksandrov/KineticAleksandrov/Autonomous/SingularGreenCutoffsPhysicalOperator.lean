module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsPhysicalCoordinates
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsSpatialOperator

/-! # Actual physical compact generators and their occupation integrability -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Parabolic SectionTwo Evolution MeasureTheory Set

/-- A compact physical C² test has a continuous compactly supported physical generator. -/
theorem physicalSpatialOperator_continuous_compact {lam Lam : ℝ}
    (A : SmoothAutonomous lam Lam) (f : Z → ℝ) (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) :
    Continuous (physicalSpatialOperator A.a f) ∧
      HasCompactSupport (physicalSpatialOperator A.a f) := by
  let F := physicalCompactDatum f hf.continuous hc
  have hh := compact_spatial_generator A F
    (physicalCompactDatum_contDiff f hf hc) (physicalCompactDatum_hasCompactSupport f _ hc)
  let H := fun x : EvolutionAmbientState 1 => transportedForwardOperator (evolutionCoefficient
    A.a) (identityDrift 1)
    (fun q => F (q.position, q.velocity)) ⟨0, x.1, x.2⟩
  have he : physicalSpatialOperator A.a f = H ∘ physicalStateCLE.symm := by
    funext q
    exact (physicalSpatialOperator_eq_native A.a f
      ⟨0, fun _ => q.2, fun _ => q.1⟩).symm
  rw [he]
  exact ⟨hh.1.comp physicalStateCLE.symm.continuous,
    hh.2.comp_homeomorph physicalStateCLE.symm.toHomeomorph⟩

/-- Every compact physical generator is integrable for the finite actual occupation measure. -/
theorem physicalSpatialOperator_occupation_integrable {lam Lam : ℝ}
    (A : SmoothAutonomous lam Lam) (f : Z → ℝ) (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) (E : FullSpaceEvolution) (z : Z) (T : ℝ) :
    Integrable (physicalSpatialOperator A.a f) (physicalOccupationMeasure E z T) := by
  obtain ⟨hL, hcL⟩ := physicalSpatialOperator_continuous_compact A f hf hc
  obtain ⟨C, hb⟩ := hL.bounded_above_of_compact_support hcL
  apply (integrable_const C).mono' hL.measurable.aestronglyMeasurable
  exact Filter.Eventually.of_forall hb

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
