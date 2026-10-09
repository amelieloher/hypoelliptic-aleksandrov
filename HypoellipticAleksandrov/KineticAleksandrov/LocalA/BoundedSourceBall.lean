module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceTracesLateral
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceRestriction
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.GreenPotentialsGeometry

/-! # Literal finite-strip ball source potentials

The physical source is cut off by the finite open strip, then swapped to Section Two
coordinates. No boundary kernel or new evolution choice is introduced.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory SectionTwo Evolution TheoremA

/-- The killed source potential with the literal finite-strip zero extension. -/
def boundedBallSourcePotential {d : ℕ} {v₀ : PDE.Vec d} {R : ℝ}
    (K : MovingFiberKernel (PDE.euclideanBall v₀ R) (fun _ => 0))
    (a T : ℝ) (F : KineticPoint d → ℝ) (P : KineticPoint d) : ℝ :=
  duhamelPotential K T ((localStrip a T v₀ R).indicator F ∘ sectionTwoPoint)
    (sectionTwoPoint P)

/-- Strip-bounded sources have a globally bounded measurable literal zero extension. -/
theorem boundedBallSource_extension {d : ℕ} (a T M : ℝ) (v₀ : PDE.Vec d) (R : ℝ)
    (hM : 0 ≤ M) (F : KineticPoint d → ℝ) (hF : Measurable F)
    (hb : ∀ P ∈ localStrip a T v₀ R, |F P| ≤ M) :
    Measurable ((localStrip a T v₀ R).indicator F ∘ sectionTwoPoint) ∧
      ∀ Q, |(localStrip a T v₀ R).indicator F (sectionTwoPoint Q)| ≤ M := by
  refine ⟨(hF.indicator (measurableSet_localStrip a T v₀ R)).comp
    (continuous_sectionTwoPoint d).measurable, fun Q => ?_⟩
  by_cases hQ : sectionTwoPoint Q ∈ localStrip a T v₀ R
  · rw [indicator_of_mem hQ]
    exact hb _ hQ
  · rw [indicator_of_notMem hQ, abs_zero]
    exact hM

/-- The finite strip swaps into the existing past evolution domain. -/
theorem boundedBallSource_strip_subset_past {d : ℕ} (a T : ℝ) (v₀ : PDE.Vec d) (R : ℝ) :
    sectionTwoPoint '' localStrip a T v₀ R ⊆
      evolutionPastOpenCylinder (PDE.euclideanBall v₀ R) (fun _ => 0) T := by
  rintro Q ⟨P, hP, rfl⟩
  refine ⟨hP.2.1, ?_⟩
  rw [boundedSource_stationary_domain]
  exact hP.2.2

/-- Bounded physical strip sources satisfy the exact signed kinetic weak equation. -/
theorem boundedBallSourcePotential_weak {d : ℕ} {lam Lam : ℝ}
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)
    (S : TerminalOperatorFamily (PDE.euclideanBall v₀ R) (fun _ => 0))
    (K : MovingFiberKernel (PDE.euclideanBall v₀ R) (fun _ => 0))
    (hreal : RealizesTerminalEvolution (PDE.euclideanBall v₀ R) (fun _ => 0)
      (PDE.isOpen_euclideanBall v₀ R).measurableSet
      (zIndependentCoefficient B) (identityDrift d) S K)
    (a T M : ℝ) (hM : 0 ≤ M) (F : KineticPoint d → ℝ) (hF : Measurable F)
    (hb : ∀ P ∈ localStrip a T v₀ R, |F P| ≤ M) :
    IsKineticWeakTransportedSolution (zIndependentCoefficient B) (identityDrift d)
      (sectionTwoPoint '' localStrip a T v₀ R)
      (boundedBallSourcePotential K a T F ∘ sectionTwoPoint)
      (fun Q => -F (sectionTwoPoint Q)) := by
  obtain ⟨hBs, hBsym, _⟩ := sectionTwoCoefficient_fullBounds lam Lam B hB
  obtain ⟨hgm, hgb⟩ := boundedBallSource_extension a T M v₀ R hM F hF hb
  let g := (localStrip a T v₀ R).indicator F ∘ sectionTwoPoint
  have hw := duhamel_bounded_isKineticWeakTransportedSolution (localBall_admissible v₀ hR)
    (PDE.isOpen_euclideanBall v₀ R).measurableSet continuous_const
    (zIndependentCoefficient B) (identityDrift d) S K hreal hBs hBsym
    (identityDrift_smooth d) g hgm M hM hgb T
  have hsub := boundedBallSource_strip_subset_past a T v₀ R
  have hr := boundedSource_weak_restrict hsub (zIndependentCoefficient B) (identityDrift d)
    (duhamelPotential K T g) (fun Q => -g Q) hw
  have hU : MeasurableSet (sectionTwoPoint '' localStrip a T v₀ R) :=
    ((sectionTwoHomeomorph d).isOpenMap _ (isOpen_localStrip a T v₀ R)).measurableSet
  have hfg : EqOn (fun Q => -g Q) (fun Q => -F (sectionTwoPoint Q))
      (sectionTwoPoint '' localStrip a T v₀ R) := by
    rintro Q ⟨P, hP, rfl⟩
    change -(localStrip a T v₀ R).indicator F (sectionTwoPoint (sectionTwoPoint P)) =
      -F (sectionTwoPoint (sectionTwoPoint P))
    rw [sectionTwoPoint_involutive P, indicator_of_mem hP]
  have heq : boundedBallSourcePotential K a T F ∘ sectionTwoPoint = duhamelPotential K T g := by
    funext Q
    change duhamelPotential K T g (sectionTwoPoint (sectionTwoPoint Q)) = _
    rw [sectionTwoPoint_involutive Q]
  rw [heq]
  exact boundedSource_weak_source_congr hU _ _ _ _ _ hfg hr

/-- The physical finite-strip source potential has the exact time/quadratic minimum bound. -/
theorem boundedBallSourcePotential_abs_le
    (hH : HormanderHypoellipticityStatement) {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ}
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)
    (S : TerminalOperatorFamily (PDE.euclideanBall v₀ R) (fun _ => 0))
    (K : MovingFiberKernel (PDE.euclideanBall v₀ R) (fun _ => 0))
    (hreal : RealizesTerminalEvolution (PDE.euclideanBall v₀ R) (fun _ => 0)
      (PDE.isOpen_euclideanBall v₀ R).measurableSet
      (zIndependentCoefficient B) (identityDrift d) S K)
    (a T M : ℝ) (hM : 0 ≤ M) (F : KineticPoint d → ℝ) (hF : Measurable F)
    (hb : ∀ P ∈ localStrip a T v₀ R, |F P| ≤ M)
    (P : KineticPoint d) (hP : P ∈ localClosedStrip a T v₀ R) :
    |boundedBallSourcePotential K a T F P| ≤ M * min (T - P.time)
      ((R ^ 2 - PDE.vecNormSq (P.velocity - v₀)) / (2 * (d : ℝ) * lam)) := by
  obtain ⟨hBs, hBsym, hell⟩ := sectionTwoCoefficient_fullBounds lam Lam B hB
  obtain ⟨hgm, hgb⟩ := boundedBallSource_extension a T M v₀ R hM F hF hb
  have hp : sectionTwoPoint P ∈
      evolutionPastClosedCylinder (PDE.euclideanBall v₀ R) (fun _ => 0) T := by
    refine ⟨hP.2.1, ?_⟩
    rw [boundedSource_stationary_domain]
    exact hP.2.2
  have h := abs_duhamelPotential_le_time_min_quadratic hH (lt_of_lt_of_le Nat.zero_lt_one hd)
    hR hB.1 zero_lt_one (zIndependentCoefficient B) hBs hBsym hell (identityDrift d)
    (identityDrift_smooth d) (identityDrift_bounds d) S K hreal
    ((localStrip a T v₀ R).indicator F ∘ sectionTwoPoint) hgm M hM hgb T (sectionTwoPoint P) hp
  simpa only [boundedBallSourcePotential, boundedSourceQuadratic, sectionTwoPoint, mul_comm] using h

/-- The finite-strip literal potential vanishes on both trace faces, including their corner. -/
theorem boundedBallSourcePotential_trace_zero {d : ℕ} {v₀ : PDE.Vec d} {R : ℝ}
    (K : MovingFiberKernel (PDE.euclideanBall v₀ R) (fun _ => 0))
    (a T : ℝ) (F : KineticPoint d → ℝ) (P : KineticPoint d)
    (hp : P ∈ localTrace a T v₀ R) : boundedBallSourcePotential K a T F P = 0 := by
  rcases hp with hterm | hlat
  · exact duhamelPotential_eq_zero_of_terminal_le K T _ (sectionTwoPoint P) hterm.1.ge
  · apply duhamelPotential_eq_zero_of_not_mem
    rw [boundedSource_stationary_domain]
    rw [(PDE.isOpen_euclideanBall v₀ R).frontier_eq] at hlat
    exact hlat.2.2.2

/-- The physical potential is continuous within the closed strip at either trace face. -/
theorem boundedBallSourcePotential_continuousWithinAt_trace
    (hH : HormanderHypoellipticityStatement) {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ}
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)
    (S : TerminalOperatorFamily (PDE.euclideanBall v₀ R) (fun _ => 0))
    (K : MovingFiberKernel (PDE.euclideanBall v₀ R) (fun _ => 0))
    (hreal : RealizesTerminalEvolution (PDE.euclideanBall v₀ R) (fun _ => 0)
      (PDE.isOpen_euclideanBall v₀ R).measurableSet
      (zIndependentCoefficient B) (identityDrift d) S K)
    (a T M : ℝ) (hM : 0 ≤ M) (F : KineticPoint d → ℝ) (hF : Measurable F)
    (hb : ∀ P ∈ localStrip a T v₀ R, |F P| ≤ M)
    (haT : a ≤ T) (P : KineticPoint d) (hP : P ∈ localTrace a T v₀ R) :
    ContinuousWithinAt (boundedBallSourcePotential K a T F) (localClosedStrip a T v₀ R) P := by
  obtain ⟨hgm, hgb⟩ := boundedBallSource_extension a T M v₀ R hM F hF hb
  let g := (localStrip a T v₀ R).indicator F ∘ sectionTwoPoint
  rcases hP with ht | hl
  · have hc := continuousAt_duhamelPotential_terminal K g M hM hgb T (sectionTwoPoint P) ht.1
    exact (hc.comp (continuous_sectionTwoPoint d).continuousAt).continuousWithinAt
  · obtain ⟨hBs, hBsym, hell⟩ := sectionTwoCoefficient_fullBounds lam Lam B hB
    have hclosed := localTrace_subset_closed haT v₀ R (Or.inr hl)
    have hmaps : MapsTo sectionTwoPoint (localClosedStrip a T v₀ R)
        (evolutionPastClosedCylinder (PDE.euclideanBall v₀ R) (fun _ => 0) T) := by
      intro Q hQ
      refine ⟨hQ.2.1, ?_⟩
      rw [boundedSource_stationary_domain]
      exact hQ.2.2
    have hc := continuousWithinAt_duhamelPotential_bounded_lateral hH
      (lt_of_lt_of_le Nat.zero_lt_one hd) hR hB.1 zero_lt_one
      (zIndependentCoefficient B) hBs hBsym hell (identityDrift d)
      (identityDrift_smooth d) (identityDrift_bounds d) S K hreal
      g hgm M hM hgb T (sectionTwoPoint P) (hmaps hclosed) hl.2.2
    exact hc.comp (continuous_sectionTwoPoint d).continuousWithinAt hmaps

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
