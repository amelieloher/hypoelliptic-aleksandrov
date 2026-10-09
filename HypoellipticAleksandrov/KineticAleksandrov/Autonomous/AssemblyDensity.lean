module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AssemblyFrontier
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PreliminaryP6
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.Entrance
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BelowFourDensity
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BelowFourBand
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.RestartTailHolds

/-! # Composition of autonomous density results

Entrance discharges preliminary exponent-six admissibility. The improved density
still depends on precisely the four source steps in the remaining frontier.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous

/-- Preliminary exponent-six admissibility, relative only to the three classical inputs. -/
theorem smoothAutonomousP6_holds
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement) :
    ∀ (lam Lam : ℝ), 0 < lam → lam ≤ Lam → SmoothAutonomousP6Statement lam Lam := by
  intro lam Lam hlam hLam
  exact smoothAutonomousP6_of_entrance (entranceStatement_holds)
    hH hLE lam Lam hlam hLam

/-- The improved cylinder density follows from exactly the remaining source frontier. -/
theorem below_four_density_of_frontier (hfront : AutonomousRemainingFrontier)
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement) : BelowFourDensityStatement := by
  obtain ⟨hTime, hStart, hTerminal, hCore⟩ := hfront
  have hpush := pushforwardStatement_holds
  have hvisits := positionVisitsStatement_holds_of_start_time
    (smoothAutonomousP6_holds hH hLE) hTime hStart
  have hmasses := positionVisitMassesStatement_holds_of_terminal_domination hTerminal
  exact below_four_density_of_band
    (below_four_band_of_predecessors hpush (restartTailStatement_holds)
      hvisits hmasses hCore) hpush

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
