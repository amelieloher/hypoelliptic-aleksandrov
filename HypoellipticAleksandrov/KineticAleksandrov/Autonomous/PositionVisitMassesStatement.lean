module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionVisitsStatement
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitsPieces

/-! # The source position-resolved visit measure and its mass and domination properties

Source: companion paper, Section 8, including the properties preceding the displayed
cell-mass definition. All clauses use the same enlarged-strip recursion.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory

/-- Finiteness, cell definitions, total count, and active domination for positioned visits. -/
def PositionVisitMassesStatement : Prop :=
  ∀ (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam),
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock)
      (J : Interval) (R T : ℝ) (P : Point),
      0 < R → ∀ (_hT : 0 < T), T ≤ R ^ 2 → |c.vbar| = 2 * c.r →
      ∀ (_hJ : closure c.active ⊆ J.carrier)
        (_hvel : P.velocity 0 ∈ closure c.entrance),
      let nu := visitsFromZero hH hLE hlam hLam A c J T P
      IsFiniteMeasure nu ∧
      (∀ᵐ p ∂nu, P.time ≤ p.time ∧ p.time < P.time + T ∧ p.velocity 0 ∈ closure c.entrance) ∧
      nu univ ≤ ENNReal.ofReal (C * (1 + R / c.r)) ∧
      (∀ j : ℕ, (∑' k : ℤ, enlargedPositionVisitMass nu c P.time 0 j k) =
        enlargedTimeVisitMass nu c P.time j) ∧
      (∀ N : ℕ,
        (∑ n ∈ Finset.range N, enlargedActivePiece hH hLE hlam hLam A c J P.time (P.time + T) P n) ≤
          enlargedFullSpaceOccupation hH hLE hlam hLam A P T) ∧
      (∀ (N : ℕ) (b : ℝ), P.time ≤ b → b ≤ P.time + T →
        enlargedActiveTerminal hH hLE hlam hLam A c J P.time (P.time + T) P N b ≤
          enlargedFullSpaceTerminal hH hLE hlam hLam A P b)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
