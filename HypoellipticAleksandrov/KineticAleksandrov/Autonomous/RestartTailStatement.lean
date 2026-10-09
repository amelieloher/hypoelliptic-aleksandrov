module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitsCells

/-! # Literal restarted one-pole density tail

Source: companion paper, Corollary 8.4. This statement is an
explicit hypothesis where used.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory

/-- The source nonnegative density predicate, on an explicitly specified reference set. -/
def enlargedIsDensityOn (mu : Measure Point) (S : Set Point) (G : Point → ℝ) : Prop :=
  Measurable G ∧ (∀ p, 0 ≤ G p) ∧
    mu = (volume.restrict S).withDensity (fun p => ENNReal.ofReal (G p))

/-- The source `D` predicate, including its real norm bound. -/
def enlargedDensityBound (mu : Measure Point) (S : Set Point) (q K : ℝ) : Prop :=
  ∃ G : Point → ℝ, enlargedIsDensityOn mu S G ∧
    MemLp G (ENNReal.ofReal q) (volume.restrict S) ∧
    (eLpNorm G (ENNReal.ofReal q) (volume.restrict S)).toReal ≤ K

/-- Exponential all-time density tails for every active starting velocity. -/
def RestartTailStatement : Prop :=
  ∀ (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) (q : ℝ),
    (1 < q ∧ q < 3 / 2) →
    ∃ C c₀ : ℝ, 0 < C ∧ 0 < c₀ ∧ ∀ (A : SmoothAutonomous lam Lam)
      (c : Clock) (e : Point) (he : e.velocity 0 ∈ c.active),
      ∃ G : Point → ℝ,
        enlargedIsDensityOn
          (stripGreen hH hLE hlam hLam A c.activeInterval ⊤ (densityClockPole c e he))
          (densityClockStrip c e) G ∧
        ∀ t : ℝ, 0 ≤ t →
          MemLp G (ENNReal.ofReal q)
            (volume.restrict {p | e.time + t ≤ p.time ∧ p.velocity 0 ∈ c.active}) ∧
          (eLpNorm G (ENNReal.ofReal q)
            (volume.restrict {p | e.time + t ≤ p.time ∧ p.velocity 0 ∈ c.active})).toReal ≤
            C * Real.exp (-c₀ * t / c.r ^ 2) * c.r ^ (6 / q - 4)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
