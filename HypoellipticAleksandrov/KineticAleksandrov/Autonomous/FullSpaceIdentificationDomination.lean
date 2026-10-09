module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FullSpaceIdentification

/-! # Zero-extension domination of every supplied velocity-strip kernel -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Set MeasureTheory
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

/-- Every stationary velocity interval is contained in the full velocity domain. -/
theorem strip_subset_fullspace (H : Interval) (t : ℝ) :
    movingDomain (intervalDomain H) (fun _ => 0) t ⊆
      movingDomain autonomousWholeDomain (fun _ => 0) t := by
  change _ ⊆ movingDomain (wholeSpace 1) (fun _ => 0) t
  rw [movingDomain_wholeSpace]
  exact subset_univ _

/-- Every realizing full-space kernel inherits domain domination from the evolution theorem. -/
theorem fullspace_domainMonotone
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E) :
    IsDomainMonotoneEvolution autonomousWholeDomain (fun _ => 0)
      (evolutionCoefficient A.a) (identityDrift 1) E.2 := by
  obtain ⟨S, K, hc, -, -, -, -, hi, -, -, -, -, he, hcomp, -, hmono, -⟩ :=
    exists_terminalEvolution_of_classical hLE hH 1 (by omega) lam Lam 1 1
      hlam hLam one_pos le_rfl autonomousWholeDomain (fun _ => 0)
      (evolutionCoefficient A.a) (identityDrift 1) autonomousWholeDomain_admissible
      (zeroCurve_piecewiseC1 1) (evolutionCoefficient_smooth A)
      (evolutionCoefficient_symmetric A.a) (evolutionCoefficient_bounds A)
      (identityDrift_smooth 1) (identityDrift_bounds 1).1 (identityDrift_bounds 1).2
  have hpair : E = (S, K) := fullSpaceEvolution_unique A E (S, K) hE ⟨hc, hi, he, hcomp⟩
  simpa only [hpair] using hmono

/-- Every supplied strip realization is measure dominated by the supplied full-space one. -/
theorem strip_kernel_le_fullspace
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)
    (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E)
    (H : Interval) (G : StripEvolution H) (hG : IsStripEvolution A H G) :
    MovingFiberKernel.IsZeroExtensionDominatedBy G.2 E.2 (strip_subset_fullspace H) :=
  domainMonotone_of_realizes (evolutionCoefficient A.a) (identityDrift 1) E.2
    (fullspace_domainMonotone hH hLE hlam hLam A E hE)
    (intervalDomain H) (fun _ => 0) (intervalDomain_admissible H)
    (zeroCurve_piecewiseC1 1) (strip_subset_fullspace H) G.1 G.2 hG

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
