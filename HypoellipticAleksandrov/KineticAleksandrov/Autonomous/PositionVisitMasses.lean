module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionVisitMassesStatement
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionCells
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitMassCanonical
import Mathlib.Tactic

/-! # The source position-resolved mass package

Finiteness, support, the uniform count, the cell sum, and occupation domination
are proved internally. Only the precise full-space terminal domination conclusion
is taken as a hypothesis.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- The corrected mass conditions, assuming the terminal domination estimate. -/
theorem positionVisitMassesStatement_holds_of_terminal_domination
    (hTerminal : ∀ (hH : HormanderHypoellipticityStatement)
      (hLE : LiebermanEllipsoidDirichletStatement)
      (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
      (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (T : ℝ) (P : Point),
      |c.vbar| = 2 * c.r → 0 < T → closure c.active ⊆ J.carrier →
      P.velocity 0 ∈ closure c.entrance →
      ∀ (N : ℕ) (b : ℝ), P.time ≤ b → b ≤ P.time + T →
        enlargedActiveTerminal hH hLE hlam hLam A c J P.time (P.time + T) P N b ≤
          enlargedFullSpaceTerminal hH hLE hlam hLam A P b) :
    PositionVisitMassesStatement := by
  intro hH hLE lam Lam hlam hLam
  refine ⟨enlargedVisitMassConstant lam Lam, enlargedVisitMassConstant_pos hlam hLam, ?_⟩
  intro A c J R T P hR hT hTR hbar hJ hvel
  dsimp only
  have hPT : P.time < P.time + T := by linarith
  have : IsFiniteMeasure (visitsFromZero hH hLE hlam hLam A c J T P) :=
    enlargedVisitStarts_isFiniteMeasure hH hLE hlam hLam A c J R T P
      hR hT hTR hbar hJ hvel
  refine ⟨inferInstance, ?_, ?_, ?_, ?_, ?_⟩
  · exact enlargedVisitStarts_ae_support hH hLE hlam hLam A c J P.time (P.time + T)
      P le_rfl hPT
  · exact enlargedVisitStarts_mass_le hH hLE hlam hLam A c J R T P hR hT hTR hbar hJ hvel
  · intro j
    exact enlargedPositionVisitMass_sum _ c P.time 0 j
  · intro N
    exact enlarged_active_occupation_le_fullspace hH hLE hlam hLam A c J T hT P
      (hJ (subset_closure (enlarged_closedEntrance_subset_active c hvel))) N
  · exact hTerminal hH hLE lam Lam hlam hLam A c J T P hbar hT hJ hvel

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
