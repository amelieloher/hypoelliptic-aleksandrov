module

public import HypoellipticAleksandrov.KineticAleksandrov.SourceProblem.WholeSpaceLocalization

public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.WholeSpaceComparison
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.WholeSpaceGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.LocalizedKrylovGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.PotentialWhole
public import HypoellipticAleksandrov.Parabolic.ContDiffOnTwoToScalarC12

/-! # Localization of the whole-space occupation potential -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic SectionTwo Set

/-- The whole-space potential admits the source quadratic comparison on every ball. -/
theorem wholeSpace_localization {d : ℕ} (hH : HormanderHypoellipticityStatement)
    (hd : 0 < d)
    {lam Lam : ℝ} {B : CoefficientField d} (hB : IsSectionTwoCoefficient lam Lam B)
    (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
    (hP : HasParabolicMarginalBundle (wholeSpace d) (fun _ => (0 : PDE.Vec d))
      MeasurableSet.univ (zIndependentCoefficient B) K)
    (F : TimeVelocity d → ℝ) (hF0 : ∀ q, 0 ≤ F q)
    (hFs : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F)
    (hFsupp : tsupport F ⊆ Ioo (0 : ℝ) 1 ×ˢ univ)
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1) (vStar : PDE.Vec d)
    (R : ℝ) (hR : 0 < R) (hRsq : R ^ 2 = max 1 (4 * d * Lam)) :
    let W := parabolicDuhamelPotential K MeasurableSet.univ 1 F
    let H := sSup (W '' (Icc (0 : ℝ) 1 ×ˢ univ))
    ∃ V : TimeVelocity d → ℝ,
      IsClassicalBackwardDirichletSolution α 1 (PDE.euclideanBall vStar R) B
        (fun _ _ => 0) (fun _ _ => 0) (fun r v => -F (r, v))
        (fun _ => 0) (fun _ => 0) V ∧
      (∀ q ∈ scalarParabolicClosedCylinder α 1 (PDE.euclideanBall vStar R),
        W q ≤ V q + H * occupationQuadratic Lam vStar q / R ^ 2) ∧
      (2 * d * Lam * (1 - α)) / R ^ 2 ≤ 1 / 2 := by
  exact wholeSpace_localization_direct hH hd hB K hP F hF0 hFs hFc hFsupp
    α hα0 hα1 vStar R hR hRsq

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
