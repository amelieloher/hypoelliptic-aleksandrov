module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceBall
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceInterior
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ClassicalTerminalWeak

/-! # Full bounded-source continuity and traces on the physical closed strip -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory SectionTwo Evolution TheoremA

/-- The literal signed bounded ball potential is continuous on the entire closed strip,
including its initial face and both zero trace faces. -/
theorem boundedBallSourcePotential_continuousOn
    (hH : HormanderHypoellipticityStatement) {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ}
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)
    (S : TerminalOperatorFamily (PDE.euclideanBall v₀ R) (fun _ => 0))
    (K : MovingFiberKernel (PDE.euclideanBall v₀ R) (fun _ => 0))
    (hreal : RealizesTerminalEvolution (PDE.euclideanBall v₀ R) (fun _ => 0)
      (PDE.isOpen_euclideanBall v₀ R).measurableSet
      (zIndependentCoefficient B) (identityDrift d) S K)
    (a T M : ℝ) (haT : a ≤ T) (hM : 0 ≤ M)
    (F : KineticPoint d → ℝ) (hF : Measurable F)
    (hb : ∀ P ∈ localStrip a T v₀ R, |F P| ≤ M) :
    ContinuousOn (boundedBallSourcePotential K a T F) (localClosedStrip a T v₀ R) := by
  obtain ⟨hBs, hBsym, hell⟩ := sectionTwoCoefficient_fullBounds lam Lam B hB
  obtain ⟨hgm, hgb⟩ := boundedBallSource_extension a T M v₀ R hM F hF hb
  let g := (localStrip a T v₀ R).indicator F ∘ sectionTwoPoint
  have hgz : ∀ Q, KineticPoint.equivProd d Q ∉
      boundedSourcePast (PDE.euclideanBall v₀ R) (fun _ => 0) T → g Q = 0 := by
    intro Q hQ
    by_cases hm : sectionTwoPoint Q ∈ localStrip a T v₀ R
    · have hpast : KineticPoint.equivProd d Q ∈
          boundedSourcePast (PDE.euclideanBall v₀ R) (fun _ => 0) T := by
        refine ⟨hm.2.1, ?_⟩
        rw [boundedSource_stationary_domain]
        exact hm.2.2
      exact False.elim (hQ hpast)
    · exact indicator_of_notMem hm F
  have hi := continuousOn_duhamelPotential_bounded_signed hH (localBall_admissible v₀ hR)
    (PDE.isOpen_euclideanBall v₀ R).measurableSet continuous_const
    (zIndependentCoefficient B) (identityDrift d) S K hreal hBs hBsym
    (identityDrift_smooth d) lam Lam 1 hB.1 zero_lt_one hell (identityDrift_bounds d).2
    T g hgm M hM hgb hgz
  intro P hP
  by_cases ht : P.time = T
  · exact boundedBallSourcePotential_continuousWithinAt_trace hH hd B hB v₀ hR S K hreal
      a T M hM F hF hb haT P (Or.inl ⟨ht, hP.2.2⟩)
  by_cases hv : P.velocity ∈ frontier (PDE.euclideanBall v₀ R)
  · exact boundedBallSourcePotential_continuousWithinAt_trace hH hd B hB v₀ hR S K hreal
      a T M hM F hF hb haT P (Or.inr ⟨hP.1, hP.2.1, hv⟩)
  have hball : P.velocity ∈ PDE.euclideanBall v₀ R := by
    by_contra hn
    apply hv
    rw [(PDE.isOpen_euclideanBall v₀ R).frontier_eq]
    exact ⟨hP.2.2, hn⟩
  have hpast : sectionTwoPoint P ∈
      evolutionPastOpenCylinder (PDE.euclideanBall v₀ R) (fun _ => 0) T := by
    refine ⟨lt_of_le_of_ne hP.2.1 ht, ?_⟩
    rw [boundedSource_stationary_domain]
    exact hball
  have hc := hi.continuousAt
    ((isOpen_evolutionPastOpenCylinder (PDE.isOpen_euclideanBall v₀ R)
      continuous_const T).mem_nhds hpast)
  exact (hc.comp (continuous_sectionTwoPoint d).continuousAt).continuousWithinAt

/-- Full bounded-source continuity, zero terminal/lateral traces, and the exact minimum
barrier are proved for the supplied actual ball evolution. -/
theorem boundedBallSourcePotential_bounded_traces
    (hH : HormanderHypoellipticityStatement) {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ}
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)
    (S : TerminalOperatorFamily (PDE.euclideanBall v₀ R) (fun _ => 0))
    (K : MovingFiberKernel (PDE.euclideanBall v₀ R) (fun _ => 0))
    (hreal : RealizesTerminalEvolution (PDE.euclideanBall v₀ R) (fun _ => 0)
      (PDE.isOpen_euclideanBall v₀ R).measurableSet
      (zIndependentCoefficient B) (identityDrift d) S K)
    (a T M : ℝ) (haT : a < T) (hM : 0 ≤ M)
    (F : KineticPoint d → ℝ) (hF : Measurable F)
    (hb : ∀ P ∈ localStrip a T v₀ R, |F P| ≤ M) :
    ContinuousOn (boundedBallSourcePotential K a T F) (localClosedStrip a T v₀ R) ∧
      (∀ P ∈ localTrace a T v₀ R, boundedBallSourcePotential K a T F P = 0) ∧
      ∀ P ∈ localStrip a T v₀ R,
        |boundedBallSourcePotential K a T F P| ≤ M * min (T - P.time)
          ((R ^ 2 - PDE.vecNormSq (P.velocity - v₀)) / (2 * (d : ℝ) * lam)) := by
  refine ⟨boundedBallSourcePotential_continuousOn hH hd B hB v₀ hR S K hreal
    a T M haT.le hM F hF hb, boundedBallSourcePotential_trace_zero K a T F, ?_⟩
  intro P hP
  exact boundedBallSourcePotential_abs_le hH hd B hB v₀ hR S K hreal a T M hM F hF hb
    P ⟨hP.1.le, hP.2.1.le, subset_closure hP.2.2⟩

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
