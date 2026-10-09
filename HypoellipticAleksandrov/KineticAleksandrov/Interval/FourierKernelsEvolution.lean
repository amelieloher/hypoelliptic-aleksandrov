module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.Setting

/-! # Structural clauses for a supplied interval evolution

The existence theorem produces a second evolution. Uniqueness identifies its kernel with the
supplied realizing kernel, transferring all structural clauses without new premises.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open Set MeasureTheory HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Decay

/-- The clauses hold for every kernel realizing the same interval problem. -/
theorem interval_evolution_clauses
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam m Lb a c : ℝ} (hac : a < c)
    (B : CoefficientField 1) (b : PDE.Vec 1 → PDE.Vec 1)
    (hs : SourceSetting lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b)
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (S : TerminalOperatorFamily (PDE.oneDimensionalAxisBox a c) stationary)
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (hr : RealizesTerminalEvolution (PDE.oneDimensionalAxisBox a c) stationary hJ
      (zIndependentCoefficient B) b S K) :
    IsDomainMonotoneEvolution (PDE.oneDimensionalAxisBox a c) stationary
      (zIndependentCoefficient B) b K ∧
    HasParabolicMarginalBundle (PDE.oneDimensionalAxisBox a c) stationary hJ
      (zIndependentCoefficient B) K ∧
    IsTranslationCovariantEvolution (PDE.oneDimensionalAxisBox a c) stationary hJ K := by
  obtain ⟨S₀, K₀, hr₀, hm, hp, hc⟩ :=
    exists_interval_evolution hH hLE lam Lam m Lb a c hac B b hs
  have hK := (terminalEvolution_unique (PDE.oneDimensionalAxisBox a c) stationary
    (interval_admissible hac) (zIndependentCoefficient B) b S S₀ K K₀ hr hr₀).2
  subst K₀
  exact ⟨hm, hp, hc⟩

end HypoellipticAleksandrov.KineticAleksandrov.Interval
