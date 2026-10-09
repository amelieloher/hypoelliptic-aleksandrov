module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ExitDecompositionComparison
import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.CaseW

/-! # Restriction of genuine terminal solutions to physical local strips -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory SectionTwo Parabolic TheoremA

/-- Swapping physical coordinates maps the local closed strip into the past closed cylinder. -/
theorem exit_closed_into_past {d : ℕ} {a T R : ℝ} {v₀ : PDE.Vec d}
    {Q : KineticPoint d} (hQ : Q ∈ localClosedStrip a T v₀ R) :
    sectionTwoPoint Q ∈ evolutionPastClosedCylinder (PDE.euclideanBall v₀ R)
      (fun _ => 0) T := by
  exact ⟨hQ.2.1, by simpa only [sectionTwoPoint, movingDomain_ball_zero] using hQ.2.2⟩

/-- Swapping physical coordinates maps the open strip into the genuine past interior. -/
theorem exit_open_into_past {d : ℕ} {a T R : ℝ} {v₀ : PDE.Vec d}
    {Q : KineticPoint d} (hQ : Q ∈ localStrip a T v₀ R) :
    sectionTwoPoint Q ∈ evolutionPastOpenCylinder (PDE.euclideanBall v₀ R)
      (fun _ => 0) T := by
  exact ⟨hQ.2.1, by simpa only [sectionTwoPoint, movingDomain_ball_zero] using hQ.2.2⟩

/-- A genuine classical terminal solution retains all local physical regularity and bounds. -/
theorem exit_terminal_physical_regular {d : ℕ} (B : CoefficientField d)
    {a T R : ℝ} {v₀ : PDE.Vec d}
    (F : BoundedBorel (EvolutionAmbientState d)) (u : KineticPoint d → ℝ)
    (hu : IsClassicalTerminalSolution (PDE.euclideanBall v₀ R) (fun _ => 0)
      (zIndependentCoefficient B) (identityDrift d) T F u) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      ((u ∘ sectionTwoPoint) ∘ (KineticPoint.equivProd d).symm)
      ((KineticPoint.equivProd d) '' localStrip a T v₀ R) ∧
    ContinuousOn (u ∘ sectionTwoPoint) (localClosedStrip a T v₀ R) ∧
    (∃ M : ℝ, ∀ Q ∈ localClosedStrip a T v₀ R, |u (sectionTwoPoint Q)| ≤ M) ∧
    ∀ Q ∈ localStrip a T v₀ R,
      forwardKineticOperator (ofTimeVelocityCoefficient B) (u ∘ sectionTwoPoint) Q = 0 := by
  have hswap : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : ℝ × PDE.Vec d × PDE.Vec d => (q.1, q.2.2, q.2.1)) :=
    contDiff_fst.prodMk (contDiff_snd.snd.prodMk contDiff_snd.fst)
  have hm : MapsTo (fun q : ℝ × PDE.Vec d × PDE.Vec d => (q.1, q.2.2, q.2.1))
      ((KineticPoint.equivProd d) '' localStrip a T v₀ R)
      (evolutionPastInteriorRaw (PDE.euclideanBall v₀ R) (fun _ => 0) T) := by
    rintro q ⟨Q, hQ, rfl⟩
    change Q.time < T ∧ Q.velocity ∈ movingDomain (PDE.euclideanBall v₀ R)
      (fun _ => 0) Q.time
    exact ⟨hQ.2.1, by simpa only [movingDomain_ball_zero] using hQ.2.2⟩
  refine ⟨hu.2.2.1.comp hswap.contDiffOn hm, ?_, ?_, ?_⟩
  · exact hu.2.1.comp (continuous_sectionTwoPoint d).continuousOn
      (fun Q hQ => exit_closed_into_past hQ)
  · obtain ⟨M, _, hM⟩ := hu.1
    exact ⟨M, fun Q hQ => hM _ (exit_closed_into_past hQ)⟩
  · intro Q hQ
    rw [forwardKineticOperator_eq_lop_identity]
    change transportedForwardOperator (zIndependentCoefficient B) (identityDrift d)
      ((u ∘ sectionTwoPoint) ∘ sectionTwoPoint) (sectionTwoPoint Q) = 0
    have heq : (u ∘ sectionTwoPoint) ∘ sectionTwoPoint = u := by
      funext p
      rfl
    rw [heq]
    exact hu.2.2.2.1 _ (exit_open_into_past hQ)

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
