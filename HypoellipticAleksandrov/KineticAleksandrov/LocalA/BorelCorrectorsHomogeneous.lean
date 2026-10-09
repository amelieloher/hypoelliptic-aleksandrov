module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BorelCorrectorsGreen
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundarySolution

/-! # Smoothness and homogeneity of the literal compactly corrected solution -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory Parabolic SectionTwo TheoremA Evolution Occupation
open scoped Topology Matrix.Norms.Elementwise

/-- Correct the actual classical residual by the signed whole-space source integral. -/
def borelCorrectedFunction {d : ℕ}
    (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
    (T : ℝ) (χ : KineticPoint d → ℝ) (B : CoefficientField d)
    (U : KineticPoint d → ℝ) (P : KineticPoint d) : ℝ :=
  U P + borelCorrectorPotential K T (borelCorrectorSource χ B U) P

/-- The literal correction is smooth and homogeneous where the cutoff equals one. -/
theorem borelCorrectedFunction_smooth_homogeneous
    (hH : HormanderHypoellipticityStatement) {d : ℕ} {lam Lam : ℝ}
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (hBs : IsSmoothCoefficient B)
    (S : TerminalOperatorFamily (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
    (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
    (hreal : RealizesTerminalEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d))
      MeasurableSet.univ (zIndependentCoefficient B) (identityDrift d) S K)
    (T : ℝ) (D O : Set (KineticPoint d)) (hD : IsOpen D) (hO : IsOpen O)
    (hOD : O ⊆ D) (hDt : ∀ P ∈ D, P.time < T)
    (U : KineticPoint d → ℝ) (hu : IsKineticC112On U D)
    (χ : KineticPoint d → ℝ) (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hχD : tsupport χ ⊆ D) (hχone : ∀ P ∈ O, χ P = 1) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (borelCorrectedFunction K T χ B U ∘ (KineticPoint.equivProd d).symm)
      ((KineticPoint.equivProd d) '' O) ∧
      ∀ P ∈ O, forwardKineticOperator (ofTimeVelocityCoefficient B)
        (borelCorrectedFunction K T χ B U) P = 0 := by
  let F := borelCorrectorSource χ B U
  let W := borelCorrectorPotential K T F
  let J := borelCorrectedFunction K T χ B U
  let O' := sectionTwoPoint '' O
  let V := massPhysicalPoint ⁻¹' O
  obtain ⟨hFc, hFcompact⟩ := borelCorrectorSource_continuous_compact
    hD χ hχ hχc hχD B hBs U hu
  obtain ⟨M, hM⟩ := hFcompact.exists_bound_of_continuous hFc
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  have hFb : ∀ P, |F P| ≤ max M 0 := fun P => (hM P).trans (le_max_left _ _)
  obtain ⟨hfull, hsym, hell⟩ := sectionTwoCoefficient_fullBounds lam Lam B hB
  have hFd : tsupport F ⊆ D := by
    exact (tsupport_mul_subset_left).trans hχD
  have hFpast : ∀ Q, KineticPoint.equivProd d Q ∉
      boundedSourcePast (wholeSpace d) (fun _ => (0 : PDE.Vec d)) T →
      (F ∘ sectionTwoPoint) Q = 0 := by
    intro Q hQ
    change F (sectionTwoPoint Q) = 0
    apply image_eq_zero_of_notMem_tsupport
    intro hs
    apply hQ
    have ht : Q.time < T := hDt (sectionTwoPoint Q) (hFd hs)
    refine ⟨ht, ?_⟩
    simp only [movingDomain_wholeSpace, mem_univ]
  have hWcont := continuousOn_duhamelPotential_bounded_signed hH (wholeSpace_admissible d)
    MeasurableSet.univ continuous_const (zIndependentCoefficient B) (identityDrift d)
    S K hreal hfull hsym (identityDrift_smooth d) lam Lam 1 hB.1 zero_lt_one hell
    (identityDrift_bounds d).2 T (F ∘ sectionTwoPoint)
    (hFc.measurable.comp (continuous_sectionTwoPoint d).measurable) (max M 0) hM0
    (fun Q => hFb _) hFpast
  have hsub : O' ⊆ evolutionPastOpenCylinder (wholeSpace d) (fun _ => (0 : PDE.Vec d)) T := by
    rintro Q ⟨P, hP, rfl⟩
    refine ⟨hDt P (hOD hP), ?_⟩
    simp only [movingDomain_wholeSpace, mem_univ]
  have hWweak := borelCorrectorPotential_weak B hB S K hreal T F hFc.measurable
    (max M 0) hM0 hFb
  have hw := boundedSource_weak_restrict hsub (zIndependentCoefficient B) (identityDrift d)
    (W ∘ sectionTwoPoint) (fun Q => -F (sectionTwoPoint Q)) hWweak
  have heqV : V = evolutionHomeomorph d ⁻¹' O' := by
    ext x
    constructor
    · intro hx
      exact ⟨massPhysicalPoint x, hx, rfl⟩
    · rintro ⟨P, hP, hEq⟩
      have hp : massPhysicalPoint x = P := congrArg sectionTwoPoint hEq.symm
      change massPhysicalPoint x ∈ O
      rw [hp]
      exact hP
  have hwNative := (isWeakTransportedSolution_comp_iff _ _ _ _ _).2 hw
  rw [← heqV] at hwNative
  have hwResidual : IsWeakTransportedSolution (zIndependentCoefficient B) (identityDrift d)
      V (W ∘ massPhysicalPoint)
      (fun x => -(forwardKineticOperator (ofTimeVelocityCoefficient B) U
        (massPhysicalPoint x))) := by
    refine ⟨hwNative.1, fun ψ hψ hc hs => ?_⟩
    have h := hwNative.2 ψ hψ hc hs
    refine h.trans (setIntegral_congr_fun (hO.preimage continuous_massPhysicalPoint).measurableSet
      fun x hx => ?_)
    change -F (massPhysicalPoint x) * ψ x = _
    simp only [F, borelCorrectorSource, hχone _ hx, one_mul]
  have huO : IsKineticC112On U O :=
    ⟨hu.continuousOn.mono hOD, fun P hP => hu.timeSlice_differentiableAt (hOD hP),
      fun P hP => hu.positionSlice_contDiffAt (hOD hP),
      fun P hP => hu.velocitySlice_contDiffAt (hOD hP),
      hu.continuousOn_kineticTimeDerivative.mono hOD,
      hu.continuousOn_kineticPositionGradient.mono hOD,
      hu.continuousOn_kineticVelocityGradient.mono hOD,
      hu.continuousOn_kineticVelocityHessian.mono hOD⟩
  have huNative := borelCorrector_classical_weak B hB hO U huO
  have hjWeak : IsWeakTransportedSolution (zIndependentCoefficient B) (identityDrift d)
      V (J ∘ massPhysicalPoint) (fun _ => 0) :=
    borelCorrector_weak_cancel _ _ hfull (identityDrift_smooth d) V
      (U ∘ massPhysicalPoint) (W ∘ massPhysicalPoint)
      (forwardKineticOperator (ofTimeVelocityCoefficient B) U ∘ massPhysicalPoint)
      huNative hwResidual
  have hWc : ContinuousOn W O :=
    hWcont.comp (continuous_sectionTwoPoint d).continuousOn
      (fun P hP => hsub ⟨P, hP, rfl⟩)
  have hJc : ContinuousOn (J ∘ massPhysicalPoint) V :=
    ((hu.continuousOn.mono hOD).add hWc).comp
      continuous_massPhysicalPoint.continuousOn (fun _ hx => hx)
  have hV : IsOpen V := hO.preimage continuous_massPhysicalPoint
  obtain ⟨f, hf, hae⟩ := exists_smooth_representative_transported_source hH hB.1
    hfull hell (identityDrift_smooth d) zero_lt_one (identityDrift_bounds d).2 hV
    hjWeak contDiffOn_const
  have hEq := Measure.eqOn_open_of_ae_eq hae hV hJc hf.continuousOn
  have hjSmooth := hf.congr (fun x hx => hEq hx)
  have hjOp := duhamel_operator_eq_of_smooth_weak hV hfull hsym
    (identityDrift_smooth d) hjSmooth continuousOn_const hjWeak
  have hjPhysical : ContDiffOn ℝ (⊤ : ℕ∞) (J ∘ (KineticPoint.equivProd d).symm)
      ((KineticPoint.equivProd d) '' O) := by
    apply boundary_native_smooth_to_physical O J
    rw [← heqV]
    exact hjSmooth
  refine ⟨hjPhysical, ?_⟩
  intro P hP
  let x := (evolutionHomeomorph d).symm (sectionTwoPoint P)
  have hx : x ∈ V := by
    rw [heqV]
    change evolutionHomeomorph d x ∈ O'
    rw [Homeomorph.apply_symm_apply]
    exact ⟨P, hP, rfl⟩
  have he := hjOp x hx
  have hsm : ContDiffAt ℝ 2 ((J ∘ sectionTwoPoint) ∘ evolutionHomeomorph d) x :=
    (hjSmooth.contDiffAt (hV.mem_nhds hx)).of_le (by simp)
  have hNativeEq : J ∘ massPhysicalPoint =
      (J ∘ sectionTwoPoint) ∘ evolutionHomeomorph d := rfl
  change transportedOperator (zIndependentCoefficient B) (identityDrift d)
    (J ∘ massPhysicalPoint) x = 0 at he
  rw [hNativeEq, transportedOperator_comp hsm] at he
  dsimp only [x] at he
  rw [Homeomorph.apply_symm_apply] at he
  rw [forwardKineticOperator_eq_lop_identity B J]
  exact he

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
