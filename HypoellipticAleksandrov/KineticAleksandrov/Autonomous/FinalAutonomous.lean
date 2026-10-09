module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AssemblyTheoremAutonomous
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AssemblyLocalisedAutonomous
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AssemblyAutonomousHolder
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ReturnTime
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TimeBinCount
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionTerminalDomination
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TimedCoreDomination
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionStartSlabBound

/-! # Autonomous estimates relative to the Hörmander and Lieberman theorems

Composition discharges all four autonomous steps and preserves the statements' types.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov MeasureTheory Set Autonomous Holder
open scoped ENNReal

namespace Autonomous

/-- The enlarged terminal measures satisfy the exact frontier domination statement. -/
theorem terminalDominationStatement_holds : TerminalDominationStatement := by
  intro hH hLE lam Lam hlam hLam A c J T P _hbar hT hJ _hvel N b hb hBT
  exact enlarged_active_terminal_le_fullspace hH hLE hlam hLam A c J
    P.time (P.time + T) P le_rfl (lt_add_of_pos_right P.time hT) hJ N b hb hBT

/-- The exact time-bin count follows from exponent-six admissibility and return. -/
theorem timeBinCountStatement_holds : TimeBinCountStatement := by
  intro hH hLE lam Lam hlam hLam
  exact timeBinCount_holds_of_return_time hH hLE hlam hLam
    (return_time hH hLE lam Lam hlam hLam
      (smoothAutonomousP6_holds hH hLE lam Lam hlam hLam))

/-- All autonomous frontier steps hold relative to the source theorem. -/
theorem autonomousRemainingFrontier_holds : AutonomousRemainingFrontier := by
  exact ⟨timeBinCountStatement_holds,
    positionStartSlabBound_holds terminalDominationStatement_holds,
    terminalDominationStatement_holds, coreDominationStatement_holds⟩

end Autonomous

end HypoellipticAleksandrov.KineticAleksandrov
