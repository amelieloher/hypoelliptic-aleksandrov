module

public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.WholeSpaceLocalization
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.WholeSpaceAbsorption
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.OccupationDensity
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.LocalizedKrylovBound

/-! # The whole-space occupation source bound -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic SectionTwo Set
open scoped Matrix.Norms.Elementwise
variable {d : ℕ}

/-- The uniform whole-space source estimate and its ball comparison. -/
theorem occupation_whole_space_bound
    (hH : HormanderHypoellipticityStatement)
    (hd : 0 < d) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (B : CoefficientField d) (_hB : IsSectionTwoCoefficient lam Lam B)
        (S : WholeFamily d) (K : WholeKernel d)
        (_hreal : RealizesTerminalEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d))
          MeasurableSet.univ (zIndependentCoefficient B) (identityDrift d) S K)
        (_hP : HasParabolicMarginalBundle (wholeSpace d) (fun _ => (0 : PDE.Vec d))
          MeasurableSet.univ (zIndependentCoefficient B) K)
        (F : TimeVelocity d → ℝ) (_hF0 : ∀ q, 0 ≤ F q)
        (_hFs : ContDiff ℝ (⊤ : ℕ∞) F) (_hFc : HasCompactSupport F)
        (_hFsupp : tsupport F ⊆ Ioo (0 : ℝ) 1 ×ˢ univ),
        let W := parabolicDuhamelPotential K MeasurableSet.univ 1 F
        let H := sSup (W '' (Icc (0 : ℝ) 1 ×ˢ univ))
        (∀ (α : ℝ), 0 ≤ α → α < 1 → ∀ (vStar : PDE.Vec d) (R : ℝ),
          0 < R → R ^ 2 = max 1 (4 * d * Lam) →
          ∃ V : TimeVelocity d → ℝ,
            IsClassicalBackwardDirichletSolution α 1 (PDE.euclideanBall vStar R) B
              (fun _ _ => 0) (fun _ _ => 0) (fun r v => -F (r, v))
              (fun _ => 0) (fun _ => 0) V ∧
            (∀ q ∈ scalarParabolicClosedCylinder α 1 (PDE.euclideanBall vStar R),
              W q ≤ V q + H *
                ((∑ i, (q.2 i - vStar i) ^ 2) + 2 * d * Lam * (1 - q.1)) / R ^ 2) ∧
            (2 * d * Lam * (1 - α)) / R ^ 2 ≤ 1 / 2) ∧
        H ≤ C * parabolicLpNorm d F := by
  obtain ⟨C, hC0, hbound⟩ := localizedBound_direct hd hlam hLam
  let R := Real.sqrt (max 1 (4 * (d : ℝ) * Lam))
  have hm : 0 < max 1 (4 * (d : ℝ) * Lam) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hR : 0 < R := Real.sqrt_pos.mpr hm
  have hRsq : R ^ 2 = max 1 (4 * (d : ℝ) * Lam) := Real.sq_sqrt hm.le
  let M := C * R ^ ((d : ℝ) / ((d : ℝ) + 1))
  have hM : 0 ≤ M := mul_nonneg hC0 (Real.rpow_nonneg hR.le _)
  refine ⟨2 * M, by positivity, ?_⟩
  intro B hB S K _hreal hP F hF0 hFs hFc hFsupp
  dsimp only
  let W := parabolicDuhamelPotential K MeasurableSet.univ 1 F
  let H := sSup (W '' (Icc (0 : ℝ) 1 ×ˢ univ))
  have hloc := wholeSpace_localization_direct hH hd hB K hP F hF0 hFs hFc hFsupp
  refine ⟨?_, ?_⟩
  · intro α hα0 hα1 vStar R' hR' hRsq'
    simpa only [occupationQuadratic] using hloc α hα0 hα1 vStar R' hR' hRsq'
  · have hnorm : 0 ≤ parabolicLpNorm d F := ENNReal.toReal_nonneg
    have hpoint : ∀ q ∈ Icc (0 : ℝ) 1 ×ˢ univ,
        W q ≤ M * parabolicLpNorm d F + H / 2 := by
      intro q hq
      by_cases ht : q.1 = 1
      · have hzero : W q = 0 := by
          exact parabolicDuhamelPotential_eq_zero_of_terminal_le K MeasurableSet.univ
            1 F q ht.ge
        have hpot := occupation_potential hH hB K hP F hF0 hFs hFc hFsupp
        have hH0 : 0 ≤ H := (hpot.1 (0, 0)).trans
          (le_csSup hpot.2.1 ⟨(0, 0), ⟨⟨le_rfl, zero_le_one⟩, mem_univ _⟩, rfl⟩)
        rw [hzero]
        positivity
      · have htlt : q.1 < 1 := lt_of_le_of_ne hq.1.2 ht
        obtain ⟨V, hV, hcmp, hhalf⟩ := hloc q.1 hq.1.1 htlt q.2 R hR hRsq
        have hqball : q.2 ∈ closure (PDE.euclideanBall q.2 R) := by
          apply subset_closure
          change PDE.euclideanSqDist q.2 q.2 < R ^ 2
          simpa [PDE.euclideanSqDist, PDE.vecNormSq_eq_sum_sq] using sq_pos_of_pos hR
        have hqc : q ∈ scalarParabolicClosedCylinder q.1 1
            (PDE.euclideanBall q.2 R) := ⟨⟨le_rfl, hq.1.2⟩, hqball⟩
        have hc := hcmp q hqc
        have hv := (hbound B hB.2.2.2.1 (sectionTwoCoefficient_smooth hB)
          hB.2.2.2.2.1 hB.2.2.2.2.2 F hF0 hFs hFc hFsupp q.1 hq.1.1 htlt
          q.2 R hR hRsq V hV q hqc).2
        have hpot := occupation_potential hH hB K hP F hF0 hFs hFc hFsupp
        have hH0 : 0 ≤ H := (hpot.1 (0, 0)).trans
          (le_csSup hpot.2.1 ⟨(0, 0), ⟨⟨le_rfl, zero_le_one⟩, mem_univ _⟩, rfl⟩)
        have hh := mul_le_mul_of_nonneg_left hhalf hH0
        simp only [occupationQuadratic, sub_self, zero_pow (by norm_num : 2 ≠ 0),
          Finset.sum_const_zero, zero_add] at hc
        rw [mul_div_assoc] at hc
        dsimp [M] at hv ⊢
        linarith
    have hsup := wholeSpace_absorb
      (show (Icc (0 : ℝ) 1 ×ˢ (univ : Set (PDE.Vec d))).Nonempty from
        ⟨(0, 0), ⟨⟨le_rfl, zero_le_one⟩, mem_univ _⟩⟩) hpoint
    change H ≤ (2 * M) * parabolicLpNorm d F
    nlinarith [hsup]

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
