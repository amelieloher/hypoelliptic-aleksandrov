module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitsCells
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TerminalMomentBoundsKernel
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.DeterministicBoxOccupationMeasure

/-! # Active pieces in the canonical enlarged-strip decomposition

Source: companion paper, Lemma 8.6. These are actual kernel mixtures,
not arbitrary families with a proposed domination property.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory ProbabilityTheory HypoellipticAleksandrov
open scoped Classical

/-- The physical Green kernel before a finite horizon, including initial poles. -/
def enlargedVisitGreenKernel
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion) (T : ℝ) :
    Kernel Point Point :=
  visitExtendKernel (enlargedVisitPoleSet H T) (measurableSet_enlargedVisitPoleSet H T)
    (fun p => finiteUnionGreen hH hLE hlam hLam A H T (enlargedVisitPole H T p))
    ((finiteUnionGreen_measurable hH hLE hlam hLam A H T).comp
      (measurable_enlargedVisitPole H T))

/-- The occupation measure of active piece number `n+1`. -/
def enlargedActivePiece
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ)
    (P : Point) (n : ℕ) : Measure Point :=
  enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) T ∘ₘ
    enlargedVisitEntrance hH hLE hlam hLam A c J s T P n

/-- The actual terminal family at time `b`, with the zero-duration initial value included. -/
def enlargedActiveTerminalFamily
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b : ℝ)
    (p : Point) : Measure Point :=
  if p.time = b ∧ p.velocity 0 ∈ (visitActiveUnion c J).carrier then Measure.dirac p
  else (enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) b p).restrict
    {z | z.time = b}

/-- The first `N` active terminal measures, using actual mixtures against visit starts. -/
def enlargedActiveTerminal
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ)
    (P : Point) (N : ℕ) (b : ℝ) : Measure Point :=
  ∑ n ∈ Finset.range N,
    (enlargedVisitEntrance hH hLE hlam hLam A c J s T P n).bind
      (enlargedActiveTerminalFamily hH hLE hlam hLam A c J b)

/-- Insert the observation time into physical position-velocity coordinates. -/
def enlargedTerminalPoint (b : ℝ) (z : Z) : Point :=
  ⟨b, fun _ => z.1, fun _ => z.2⟩

/-- The source full-space terminal measure in the same physical spacetime coordinates. -/
def enlargedFullSpaceTerminal
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (P : Point) (b : ℝ) : Measure Point :=
  (kernelXV (fullSpaceEvolution hH hLE hlam hLam A) (Real.toNNReal (b - P.time))
    (P.position 0, P.velocity 0)).map (enlargedTerminalPoint b)

/-- Full-space occupation on the elapsed source window, retaining physical spacetime. -/
def enlargedFullSpaceOccupation
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (P : Point) (T : ℝ) : Measure Point :=
  ((volume.restrict (Ioc 0 T)) ⊗ₘ
    physicalElapsedKernel (fullSpaceEvolution hH hLE hlam hLam A)
      (P.position 0, P.velocity 0)).map
        (fun tz => enlargedTerminalPoint (P.time + tz.1) tz.2)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
