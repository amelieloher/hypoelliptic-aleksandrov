module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockPushforwardValue
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BelowFourDensityStatement

/-! # The unproved source clock-pushforward proposition

This states companion paper, Proposition 8.3, including concentration,
weighted measure identification, and the uniform physical density estimate.
It is taken as an explicit hypothesis where used.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory

/-- The physical initial pole in the all-time active strip. -/
def densityClockPole (c : Clock) (e : Point) (he : e.velocity 0 ∈ c.active) :
    StripPole c.activeInterval ⊤ := ⟨e, WithTop.coe_lt_top _, he⟩

/-- The physical all-time strip on which the clock density is estimated. -/
def densityClockStrip (c : Clock) (e : Point) : Set Point :=
  {z | e.time < z.time ∧ z.velocity 0 ∈ c.active}

/-- The complete source clock-pushforward proposition, currently a conditional premise. -/
def PushforwardStatement : Prop :=
  ∀ (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam),
    (∀ (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point)
      (he : e.velocity 0 ∈ c.active),
      let Γ := stripGreen hH hLE hlam hLam A c.activeInterval ⊤ (densityClockPole c e he)
      Γ {z | ¬0 < Real.sign c.vbar * (z.position 0 - e.position 0)} = 0 ∧
        (Γ.withDensity (fun z => ENNReal.ofReal |z.velocity 0|)).map (c.map e) =
          ENNReal.ofReal (|c.vbar| * c.r ^ 2) • clockGreen hH hLE hlam hLam A c e he) ∧
    (∀ (q : ℝ), (1 < q ∧ q < 3 / 2) →
      ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point)
        (he : e.velocity 0 ∈ c.active),
        ∃ G : Point → ℝ, Measurable G ∧ (∀ z, 0 ≤ G z) ∧
          stripGreen hH hLE hlam hLam A c.activeInterval ⊤ (densityClockPole c e he) =
            (volume.restrict (densityClockStrip c e)).withDensity
              (fun z => ENNReal.ofReal (G z)) ∧
          MemLp G (ENNReal.ofReal q) (volume.restrict (densityClockStrip c e)) ∧
          (eLpNorm G (ENNReal.ofReal q)
            (volume.restrict (densityClockStrip c e))).toReal ≤ C * c.r ^ (6 / q - 4))

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
