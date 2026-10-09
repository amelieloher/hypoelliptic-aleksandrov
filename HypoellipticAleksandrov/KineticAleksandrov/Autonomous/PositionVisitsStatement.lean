module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.RestartTailStatement
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BelowFourBandStatement

/-! # Counts and power sums for the canonical enlarged-strip visits

Source: companion paper, Section 8. Both clauses use the same canonical visit measure.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory

/-- The source admissible range of the barrier degree `alpha`. -/
def enlargedAdmissibleAlpha (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (alpha : ℝ) : Prop :=
  bellmanAdjointExponent (Lam / lam) ((le_div_iff₀ hlam).2
    (by simpa only [one_mul] using hLam)) - 2 < alpha ∧ alpha < 1

/-- The canonical count with time measured from its starting pole. -/
def visitsFromZero
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (T : ℝ)
    (P : Point) : Measure Point :=
  enlargedVisitStarts hH hLE hlam hLam A c J P.time (P.time + T) P

/-- Position visits: the q-independent counts and the q-dependent power-sum estimate. -/
def PositionVisitsStatement : Prop :=
  ∀ (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) (alpha : ℝ),
    enlargedAdmissibleAlpha lam Lam hlam hLam alpha →
    (∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock)
      (J : Interval) (T : ℝ) (P : Point),
      |c.vbar| = 2 * c.r → closure c.active ⊆ J.carrier → 0 < T →
      P.velocity 0 ∈ closure c.entrance →
      ∀ j : ℕ,
        enlargedTimeVisitMass (visitsFromZero hH hLE hlam hLam A c J T P) c P.time j ≤
          C * (1 + (j : ℝ)) ^ (-1 / 2 : ℝ) ∧
        ∀ k : ℤ,
          enlargedPositionVisitMass (visitsFromZero hH hLE hlam hLam A c J T P) c P.time 0 j k ≤
            C * (1 + (j : ℝ)) ^ (-(2 - alpha) / 2)) ∧
    (∀ q : ℝ, (1 < q ∧ q < 3 / 2) →
      ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock)
        (J : Interval) (R T : ℝ) (P : Point),
        0 < R → 0 < T → T ≤ R ^ 2 → |c.vbar| = 2 * c.r →
        closure c.active ⊆ J.carrier →
        P.velocity 0 ∈ closure c.entrance →
        (∑' j : ℕ, ∑' k : ℤ, ENNReal.ofReal
          (enlargedPositionVisitMass (visitsFromZero hH hLE hlam hLam A c J T P)
            c P.time 0 j k ^ q)) ≤
          ENNReal.ofReal (C * (1 + R / c.r) ^ (1 - (2 - alpha) * (q - 1))))

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
