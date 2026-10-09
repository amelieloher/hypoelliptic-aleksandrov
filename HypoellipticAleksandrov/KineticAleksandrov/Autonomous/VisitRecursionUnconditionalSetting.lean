module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalDomains
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalKernels
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CapacityCylinder
import Mathlib.Tactic

/-! # Alternating visits using the actual clipped-domain exit families -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- The clock entrance interval in the existing scalar interval API. -/
def visitEntranceInterval (c : Clock) : Interval :=
  ⟨c.vbar - c.r / 2, c.vbar + c.r / 2, by linarith [c.positive]⟩

/-- The clock active interval in the existing scalar interval API. -/
def visitActiveInterval (c : Clock) : Interval :=
  ⟨c.vbar - 3 * c.r / 4, c.vbar + 3 * c.r / 4, by linarith [c.positive]⟩

/-- Actual entrance measure number `n+1`, with the source's clipped active and waiting domains. -/
def visitEntrancePiece
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ)
    (P : Point) (n : ℕ) : Measure Point :=
  visitGamma P (visitEntranceInterval c)
    (visitBoundary s T (visitEntranceInterval c) J)
    (visitBoundary s T (visitActiveInterval c) J)
    (visitUnionExitKernel hH hLE hlam hLam A (visitActiveUnion c J) s T)
    (visitUnionExitKernel hH hLE hlam hLam A (visitWaitingUnion c J) s T) n

/-- Actual outgoing measure after entrance number `n+1`. -/
def visitOutgoingPiece
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ)
    (P : Point) (n : ℕ) : Measure Point :=
  visitBeta P (visitEntranceInterval c)
    (visitBoundary s T (visitEntranceInterval c) J)
    (visitBoundary s T (visitActiveInterval c) J)
    (visitUnionExitKernel hH hLE hlam hLam A (visitActiveUnion c J) s T)
    (visitUnionExitKernel hH hLE hlam hLam A (visitWaitingUnion c J) s T) n

/-- Every actual entrance piece is finite before taking the infinite counting sum. -/
instance visitEntrancePiece_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ)
    (P : Point) (n : ℕ) :
    IsFiniteMeasure (visitEntrancePiece hH hLE hlam hLam A c J s T P n) := by
  unfold visitEntrancePiece
  infer_instance

/-- Every actual active outgoing piece is finite. -/
instance visitOutgoingPiece_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ)
    (P : Point) (n : ℕ) :
    IsFiniteMeasure (visitOutgoingPiece hH hLE hlam hLam A c J s T P n) := by
  unfold visitOutgoingPiece
  infer_instance

/-- The cylinder's actual counting measure includes the possible initial atom once. -/
def visitStartsQ
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (Z0 : Point) (R : ℝ) (hR : 0 < R)
    (P : Point) (_hP : P ∈ forwardCylinder Z0 R hR) : Measure Point :=
  Measure.sum (visitEntrancePiece hH hLE hlam hLam A c
    (capacityCylinderInterval Z0 R hR) Z0.time (Z0.time + R ^ 2) P)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
