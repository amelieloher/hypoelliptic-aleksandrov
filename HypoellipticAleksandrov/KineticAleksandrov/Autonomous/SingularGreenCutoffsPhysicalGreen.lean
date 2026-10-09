module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsDuhamelPhysical

/-! # Derived compact Green identity for the finite actual physical occupation measure -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Parabolic SectionTwo Evolution MeasureTheory Set

/-- Compact physical C² tests satisfy the actual occupation Green identity.
The source term and terminal kernel use the same explicit native-to-physical exchange. -/
theorem fullspace_physical_green_compact_c2
    (hH : HormanderHypoellipticityStatement) {lam Lam : ℝ}
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)
    (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E)
    (f : Z → ℝ) (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (z : Z) (T : NNReal) (hT : 0 < (T : ℝ)) :
    (∫ w, physicalSpatialOperator A.a f w ∂physicalOccupationMeasure E z T) =
      (∫ w, f w ∂kernelXV E T z) - f z := by
  let F := physicalCompactDatum f hf.continuous hc
  have hh := fullspace_green_spatial_compact_c2 hH hlam hLam A E hE T F
    (physicalCompactDatum_contDiff f hf hc) (physicalCompactDatum_hasCompactSupport f _ hc)
    ⟨0, fun _ => z.2, fun _ => z.1⟩ hT
  have hL := physicalSpatialOperator_continuous_compact A f hf hc
  have hLi := physicalSpatialOperator_occupation_integrable A f hf hc E z T
  have heSource :
      ((evolutionPastOpenCylinder autonomousWholeDomain (fun _ => 0) T).indicator
        (fun q => -transportedForwardOperator (evolutionCoefficient A.a)
          (identityDrift 1) (fun q => F (q.position, q.velocity)) q)) =
      ((evolutionPastOpenCylinder autonomousWholeDomain (fun _ => 0) T).indicator
        (fun q => -physicalSpatialOperator A.a f (nativeToXV (q.position, q.velocity)))) := by
    congr 1
    funext q
    exact congrArg Neg.neg (physicalSpatialOperator_eq_native A.a f q)
  rw [heSource, duhamelPotential_physical_occupation E z T
    (fun w => -physicalSpatialOperator A.a f w) hL.1.measurable.neg hLi.neg,
    integral_neg] at hh
  have heTerminal := integral_map nativeToXV_measurable.aemeasurable
    (hf.continuous.measurable.aestronglyMeasurable (μ := kernelXV E T z))
  change (∫ w, f w ∂kernelXV E T z) =
    ∫ x, f (nativeToXV x) ∂E.2.master (wholeQuery T z) at heTerminal
  change -(∫ w, physicalSpatialOperator A.a f w ∂physicalOccupationMeasure E z T) =
    f z - ∫ x, f (nativeToXV x) ∂E.2.master (wholeQuery T z) at hh
  rw [← heTerminal] at hh
  linarith only [hh]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
