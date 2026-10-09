module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BallEvolution
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceBallContinuity

/-! # Canonical ball evolution and the bounded-source theorems

The existence and uniqueness theorem selects the operator/kernel pair. The source
potential is its literal signed integral with the finite-strip cutoff and coordinate swap.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory SectionTwo Evolution TheoremA

variable (hH : HormanderHypoellipticityStatement)
  (hLE : LiebermanEllipsoidDirichletStatement)
  {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ}
  (hlam : 0 < lam) (hLam : lam ≤ Lam)
  (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
  (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)

/-- The uniquely characterized actual terminal evolution on the original Euclidean ball. -/
def localBallEvolution : LocalBallEvolution v₀ R :=
  (existsUnique_localBallEvolution hH hLE hd hlam hLam B hB v₀ hR).exists.choose

/-- The selected pair satisfies the full terminal-evolution characterization. -/
theorem localBallEvolution_realizes :
    RealizesTerminalEvolution (PDE.euclideanBall v₀ R) (fun _ => 0)
      (PDE.isOpen_euclideanBall v₀ R).measurableSet
      (zIndependentCoefficient B) (identityDrift d)
      (localBallEvolution hH hLE hd hlam hLam B hB v₀ hR).1
      (localBallEvolution hH hLE hd hlam hLam B hB v₀ hR).2 :=
  (existsUnique_localBallEvolution hH hLE hd hlam hLam B hB v₀ hR).exists.choose_spec

/-- Every actual realizing pair equals the chosen ball evolution. -/
theorem localBallEvolution_unique (E : LocalBallEvolution v₀ R)
    (hE : RealizesTerminalEvolution (PDE.euclideanBall v₀ R) (fun _ => 0)
      (PDE.isOpen_euclideanBall v₀ R).measurableSet
      (zIndependentCoefficient B) (identityDrift d) E.1 E.2) :
    E = localBallEvolution hH hLE hd hlam hLam B hB v₀ hR := by
  obtain ⟨E₀, hE₀, huniq⟩ := existsUnique_localBallEvolution hH hLE hd hlam hLam B hB v₀ hR
  exact (huniq E hE).trans (huniq _
    (localBallEvolution_realizes hH hLE hd hlam hLam B hB v₀ hR)).symm

/-- The master kernel is the second projection of that same unique evolution pair. -/
def localBallKernel : MovingFiberKernel (PDE.euclideanBall v₀ R) (fun _ => 0) :=
  (localBallEvolution hH hLE hd hlam hLam B hB v₀ hR).2

/-- The literal canonical signed finite-strip source potential in physical coordinates. -/
def ballSourcePotential (a T : ℝ) (F : KineticPoint d → ℝ) (P : KineticPoint d) : ℝ :=
  duhamelPotential (localBallKernel hH hLE hd hlam hLam B hB v₀ hR) T
    ((localStrip a T v₀ R).indicator F ∘ sectionTwoPoint) (sectionTwoPoint P)

/-- The canonical definition is exactly the potential used in the proof. -/
theorem ballSourcePotential_eq_boundedBallSourcePotential (a T : ℝ)
    (F : KineticPoint d → ℝ) :
    ballSourcePotential hH hLE hd hlam hLam B hB v₀ hR a T F =
      boundedBallSourcePotential (localBallKernel hH hLE hd hlam hLam B hB v₀ hR) a T F := by
  funext P
  rfl

/-- The exact planned signed bounded-source weak equation for the canonical ball potential. -/
theorem ballSourcePotential_weak
    (a T : ℝ) (haT : a < T) (F : KineticPoint d → ℝ)
    (hF : Measurable F) (hFb : ∃ M : ℝ, ∀ P ∈ localStrip a T v₀ R, |F P| ≤ M) :
    IsKineticWeakTransportedSolution (zIndependentCoefficient B) (identityDrift d)
      (sectionTwoPoint '' localStrip a T v₀ R)
      (ballSourcePotential hH hLE hd hlam hLam B hB v₀ hR a T F ∘ sectionTwoPoint)
      (fun Q => -F (sectionTwoPoint Q)) := by
  obtain ⟨M, hb⟩ := hFb
  rw [ballSourcePotential_eq_boundedBallSourcePotential]
  exact boundedBallSourcePotential_weak B hB v₀ hR
    (localBallEvolution hH hLE hd hlam hLam B hB v₀ hR).1
    (localBallKernel hH hLE hd hlam hLam B hB v₀ hR)
    (localBallEvolution_realizes hH hLE hd hlam hLam B hB v₀ hR)
    a T (max M 0) (le_max_right _ _) F hF
    (fun P hP => (hb P hP).trans (le_max_left _ _))

/-- The exact planned bounded-Borel continuity, traces, and minimum barrier, including
continuity at initial and interior points of the literal canonical potential. -/
theorem ballSourcePotential_bounded_traces
    (a T M : ℝ) (haT : a < T) (hM : 0 ≤ M)
    (F : KineticPoint d → ℝ) (hF : Measurable F)
    (hFb : ∀ P ∈ localStrip a T v₀ R, |F P| ≤ M) :
    ContinuousOn (ballSourcePotential hH hLE hd hlam hLam B hB v₀ hR a T F)
      (localClosedStrip a T v₀ R) ∧
      (∀ P ∈ localTrace a T v₀ R,
        ballSourcePotential hH hLE hd hlam hLam B hB v₀ hR a T F P = 0) ∧
      ∀ P ∈ localStrip a T v₀ R,
        |ballSourcePotential hH hLE hd hlam hLam B hB v₀ hR a T F P| ≤
          M * min (T - P.time)
            ((R ^ 2 - PDE.vecNormSq (P.velocity - v₀)) / (2 * (d : ℝ) * lam)) := by
  rw [ballSourcePotential_eq_boundedBallSourcePotential]
  exact boundedBallSourcePotential_bounded_traces hH hd B hB v₀ hR
    (localBallEvolution hH hLE hd hlam hLam B hB v₀ hR).1
    (localBallKernel hH hLE hd hlam hLam B hB v₀ hR)
    (localBallEvolution_realizes hH hLE hd hlam hLam B hB v₀ hR)
    a T M haT hM F hF hFb

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
