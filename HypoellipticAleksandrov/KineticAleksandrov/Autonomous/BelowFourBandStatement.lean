module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BelowFourDensityStatement
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockPushforwardCone

/-! # The source improved core-band estimate as an explicit conditional input

Source: companion paper, (8.43).
The constant precedes coefficients, clocks, cylinders, and starting points.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory

/-- The observation strip with the source's lower and upper time endpoints. -/
def densityObservationStrip (Z₀ : Point) (R : ℝ) (hR : 0 < R) : Set Point :=
  {z | Z₀.time < z.time ∧ z.time < Z₀.time + R ^ 2 ∧
    z.velocity 0 ∈ (capacityCylinderInterval Z₀ R hR).carrier}

/-- The improved band estimate for arbitrary starting velocities after first arrival. -/
def BelowFourBandStatement : Prop :=
  ∀ (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) (alpha q : ℝ),
    (bellmanAdjointExponent (Lam / lam) ((le_div_iff₀ hlam).2
      (by simpa only [one_mul] using hLam)) - 2 < alpha ∧ alpha < 1) →
    (1 < q ∧ q < 3 / 2) →
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock)
      (Z₀ : Point) (R : ℝ) (hR : 0 < R) (P : Point)
      (hP : P ∈ forwardCylinder Z₀ R hR),
      |c.vbar| = 2 * c.r → c.r ≤ 6 * R →
      ∃ G : Point → ℝ, Measurable G ∧ (∀ z, 0 ≤ G z) ∧
        (stripGreen hH hLE hlam hLam A (capacityCylinderInterval Z₀ R hR)
          (Z₀.time + R ^ 2) (capacityCylinderPole Z₀ P R hR hP)).restrict
            {z | z.velocity 0 ∈ c.core} =
          (volume.restrict (densityObservationStrip Z₀ R hR)).withDensity
            (fun z => ENNReal.ofReal (G z)) ∧
        MemLp G (ENNReal.ofReal q)
          (volume.restrict (densityObservationStrip Z₀ R hR)) ∧
        (eLpNorm G (ENNReal.ofReal q)
          (volume.restrict (densityObservationStrip Z₀ R hR))).toReal ≤
          (C * R ^ (6 - 4 * q) *
            (c.r / R) ^ (4 - 3 * q + (1 - alpha) * (q - 1))) ^ (1 / q)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
