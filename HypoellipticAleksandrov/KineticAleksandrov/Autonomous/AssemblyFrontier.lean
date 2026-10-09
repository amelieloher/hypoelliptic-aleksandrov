module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionVisits
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionVisitMasses
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationStatement

/-! # Exact remaining autonomous source steps

These predicates repeat the hypotheses of the conditional theorems verbatim.
Their conjunction records open steps; it does not prove them.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- Source l:timed-entrance#time-bin-count: the exact AU-14 hTime binder. -/
def TimeBinCountStatement : Prop :=
  ∀ (hH : HormanderHypoellipticityStatement)
      (hLE : LiebermanEllipsoidDirichletStatement)
      (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam),
      ∃ Ct : ℝ, 0 < Ct ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock)
      (J : Interval) (T : ℝ) (P : Point),
      |c.vbar| = 2 * c.r → closure c.active ⊆ J.carrier → 0 < T →
      P.velocity 0 ∈ closure c.entrance → ∀ j : ℕ,
        enlargedTimeVisitMass (visitsFromZero hH hLE hlam hLam A c J T P) c P.time j ≤
          Ct * (1 + (j : ℝ)) ^ (-1 / 2 : ℝ)

/-- Source e:position-start-identity: the exact AU-14 hStart binder. -/
def PositionStartStatement : Prop :=
  ∀ (hH : HormanderHypoellipticityStatement)
      (hLE : LiebermanEllipsoidDirichletStatement)
      (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam),
      ∃ A0 Cs : ℝ, 0 < A0 ∧ 0 < Cs ∧
      ∀ (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (T : ℝ) (P : Point),
      |c.vbar| = 2 * c.r → closure c.active ⊆ J.carrier → 0 < T →
      P.velocity 0 ∈ closure c.entrance → ∀ (a b : ℝ) (k : ℤ),
      0 ≤ a → a < b → b - a ≤ c.r ^ 2 → b ≤ T →
      enlargedPositionSlabMass (visitsFromZero hH hLE hlam hLam A c J T P)
        c P.time 0 a b k ≤ Cs *
          ((kernelXV (fullSpaceEvolution hH hLE hlam hLam A) (Real.toNNReal b)
            (P.position 0, P.velocity 0)
              (box A0 c.r (((k : ℝ) + 1 / 2) * c.r ^ 3))).toReal +
           c.r ^ (-2 : ℤ) * ∫ t in Ioc a b,
             (kernelXV (fullSpaceEvolution hH hLE hlam hLam A) (Real.toNNReal t)
               (P.position 0, P.velocity 0)
                 (box A0 c.r (((k : ℝ) + 1 / 2) * c.r ^ 3))).toReal)

/-- Source e:position-visit-masses (AU-14a): the exact hTerminal binder. -/
def TerminalDominationStatement : Prop :=
  ∀ (hH : HormanderHypoellipticityStatement)
      (hLE : LiebermanEllipsoidDirichletStatement)
      (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
      (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (T : ℝ) (P : Point),
      |c.vbar| = 2 * c.r → 0 < T → closure c.active ⊆ J.carrier →
      P.velocity 0 ∈ closure c.entrance →
      ∀ (N : ℕ) (b : ℝ), P.time ≤ b → b ≤ P.time + T →
        enlargedActiveTerminal hH hLE hlam hLam A c J P.time (P.time + T) P N b ≤
          enlargedFullSpaceTerminal hH hLE hlam hLam A P b

/-- Exactly the four still-open inputs of the autonomous conditional chain. -/
def AutonomousRemainingFrontier : Prop :=
  TimeBinCountStatement ∧ PositionStartStatement ∧
    TerminalDominationStatement ∧ CoreDominationStatement

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
