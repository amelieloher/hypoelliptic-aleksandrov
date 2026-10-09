module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GreenTestExtensionBounded

/-! # The unique finite-horizon exit measure has total mass one -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo TheoremA Evolution Parabolic
open scoped ENNReal

/-- The literal physical kinetic operator annihilates constant tests. -/
theorem reconstruction_forwardScalarOperator_const (a : ℝ → ℝ → ℝ) (c : ℝ) (p : Point) :
    forwardScalarOperator a (fun _ => c) p = 0 := by
  simp [forwardScalarOperator, kineticTimeDerivative, kineticPositionGradient_scalar,
    kineticVelocityHessian_scalar]

/-- The actual finite-horizon exit measure is a probability measure. -/
theorem stripExitOfRealization_mass_one
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ)) :
    stripExitOfRealization hH hlam hLam A H E hE T e univ = 1 := by
  have hi := strip_identity_bounded_smooth_of_realization hH hlam hLam A H E hE T e
    (fun _ => 1) contDiff_const (by
      refine ⟨1, fun p _ => ?_⟩
      simp only [abs_one, le_refl, reconstruction_forwardScalarOperator_const, abs_zero,
        zero_le_one, and_self])
  simp only [reconstruction_forwardScalarOperator_const, integral_zero, sub_zero,
    integral_const, smul_eq_mul, mul_one, Measure.real] at hi
  exact (ENNReal.toReal_eq_one_iff _).mp hi.symm

/-- The actual exit measure carries the probability instance with no extra hypothesis. -/
instance stripExitOfRealization_isProbabilityMeasure
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ)) :
    IsProbabilityMeasure (stripExitOfRealization hH hlam hLam A H E hE T e) :=
  ⟨stripExitOfRealization_mass_one hH hlam hLam A H E hE T e⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
