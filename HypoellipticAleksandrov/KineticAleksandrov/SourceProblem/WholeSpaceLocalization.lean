module

public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.WholeSpaceComparison
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.WholeSpaceGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.LocalizedKrylovGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.PotentialWhole
public import HypoellipticAleksandrov.Parabolic.ContDiffOnTwoToScalarC12
public import HypoellipticAleksandrov.KineticAleksandrov.SourceProblem.SourceCorrection

/-! # Localization of the whole-space occupation potential -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic SectionTwo Set

/-- The whole-space potential admits the source quadratic comparison on every ball. -/
theorem wholeSpace_localization_direct {d : ℕ} (hH : HormanderHypoellipticityStatement)
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
  dsimp only
  let W := parabolicDuhamelPotential K MeasurableSet.univ 1 F
  let H := sSup (W '' (Icc (0 : ℝ) 1 ×ˢ univ))
  obtain ⟨hW0, hbdd, -, hWt, hWs, hWe⟩ :=
    occupation_potential hH hB K hP F hF0 hFs hFc hFsupp
  have hH0 : 0 ≤ H := (hW0 (0, 0)).trans
    (le_csSup hbdd ⟨(0, 0), ⟨⟨le_rfl, zero_le_one⟩, mem_univ _⟩, rfl⟩)
  have hU : tsupport F ⊆ {p : TimeVelocity d | p.1 < 1 ∧
      p.2 ∈ movingDomain (wholeSpace d) (fun _ => (0 : PDE.Vec d)) p.1} := by
    intro p hp
    exact ⟨(hFsupp hp).1.2, by simp [movingDomain_wholeSpace]⟩
  have hWcont := (parabolic_duhamel hH (wholeSpace_admissible d)
    (zeroCurve_piecewiseC1 d) hB K hP 1 F hF0 hFs hFc hU).2.2.2.1
  obtain ⟨V, hV⟩ := LocalHolder.exists_signed_source_ball_correction hd vStar R hR α 1
    hα1 lam Lam hB.1 hB.2.1 B (sectionTwoCoefficient_smooth hB)
    hB.2.2.2.2.1 hB.2.2.2.2.2 (fun z => -F z) hFs.neg
  refine ⟨V, hV, ?_, occupationQuadratic_center_half (hB.1.le.trans hB.2.1)
    hα0 hR hRsq⟩
  apply wholeSpace_quadratic_comparison hB hα1 vStar (isBounded_euclideanBall vStar hR)
    hH0 W V F
  · exact hWcont.mono fun p hp => ⟨hp.1.2, by simp [movingDomain_wholeSpace]⟩
  · apply isScalarC12On_of_isOpen_contDiffOn_two
      (isOpen_Ioo.prod (PDE.isOpen_euclideanBall vStar R))
    exact (hWs.of_le (by simp)).mono fun p hp => hp.1.2
  · intro p hp
    exact hWe p hp.1.2
  · exact hV
  · intro p hp
    have ht := (mem_scalarParabolicTerminalFace_iff.mp hp).1
    have hpEq : p = (1, p.2) := Prod.ext ht rfl
    rw [hpEq]
    exact hWt p.2
  · intro p hp
    have hz := mem_scalarParabolicLateralFace_iff.mp hp
    have hw : W p ≤ H := le_csSup hbdd
      ⟨p, ⟨⟨hα0.trans hz.1, hz.2.1⟩, mem_univ _⟩, rfl⟩
    have hs := radius_sq_le_frontier_sum vStar R hz.2.2
    have ht : 0 ≤ 2 * (d : ℝ) * Lam * (1 - p.1) :=
      mul_nonneg (by positivity [hB.1.le.trans hB.2.1]) (sub_nonneg.mpr hz.2.1)
    apply hw.trans
    apply (le_div_iff₀ (sq_pos_of_pos hR)).mpr
    unfold occupationQuadratic
    exact mul_le_mul_of_nonneg_left (by linarith) hH0

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
