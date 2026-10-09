module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AutonomyPhysicalSemigroup
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TerminalMomentBoundsKernel
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SmoothAutonomousP6Statement
import Mathlib.Tactic

/-! # Literal physical semigroup notation for the return-time argument

The physical state order is `(X,v)`. All kernels are taken from the canonical full-space
evolution, with the existence hypotheses visible in the definitions.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Parabolic Set MeasureTheory
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

/-- Embed scalar physical coordinates in the one-dimensional vector carrier. -/
def physicalState (z : Z) : EvolutionAmbientState 1 := (fun _ => z.1, fun _ => z.2)

/-- Return from the vector carrier to scalar physical coordinates. -/
def scalarState (z : EvolutionAmbientState 1) : Z := (z.1 0, z.2 0)

/-- Scalar terminal data on the existing evolution carrier. -/
def scalarTerminalDatum (F : BoundedBorel Z) : BoundedBorel (EvolutionAmbientState 1) :=
  F.pullback scalarState (by unfold scalarState; fun_prop)

/-- The scalar physical spacetime point, with order `(t,X,v)`. -/
def point (t X v : ℝ) : Point := ⟨t, fun _ => X, fun _ => v⟩

/-- The full-space terminal measure pushed into physical scalar coordinate order. -/
def Kphysical (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement) {lam Lam : ℝ}
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)
    (t : ℝ) (z : Z) : Measure Z :=
  if ht : 0 ≤ t then
    ((fullSpaceEvolution hH hLE hlam hLam A).2.master
      (wholeSpaceQuery 0 t ht (physicalState z).2 (physicalState z).1)).map
      (fun x => scalarState x.swap)
  else Measure.dirac z

/-- The literal elapsed-time action of the canonical kernel on scalar physical data. -/
def S (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement) {lam Lam : ℝ}
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)
    (t : ℝ) (F : BoundedBorel Z) (z : Z) : ℝ :=
  fullSpaceAction (fullSpaceEvolution hH hLE hlam hLam A)
    (scalarTerminalDatum F) (point t z.1 z.2)

/-- The source reflected solution has position `-x`, with elapsed time and velocity fixed. -/
def reflectedSemigroupSolution (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement) {lam Lam : ℝ}
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)
    (F : BoundedBorel Z) : Point → ℝ :=
  fullSpaceAction (fullSpaceEvolution hH hLE hlam hLam A) (scalarTerminalDatum F) ∘
    autonomousPositionReflection

/-- Smooth scalar data remain smooth on the terminal-data carrier. -/
theorem scalarTerminalDatum_smooth (F : BoundedBorel Z)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ContDiff ℝ (⊤ : ℕ∞) (scalarTerminalDatum F) := by
  apply hF.comp
  unfold scalarState
  fun_prop

/-- The canonical reflected action satisfies the literal source homogeneous equation. -/
theorem reflectedSemigroupSolution_equation
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (F : BoundedBorel Z)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (p : Point) (hp : 0 < p.time) :
    autonomousScalarOperator (reflectedAutonomous A.a)
      (reflectedSemigroupSolution hH hLE hlam hLam A F) p = 0 :=
  fullSpaceAction_positionReflection hH hlam hLam A _
    (fullSpaceEvolution_spec hH hLE hlam hLam A) _ (scalarTerminalDatum_smooth F hF) p hp

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
