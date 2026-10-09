module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.RestartTailStatement
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BelowFourBandStatement

/-! # The literal cylinder entrance-counting lemma

Source: companion paper, Lemma 8.6. This count is clipped to J_Q, as in the
lemma; enlarged-strip counts used later are separately defined.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory

/-- All clauses of the source entrance lemma on its canonical clipped-cylinder count. -/
def EntranceStatement : Prop :=
  ∀ (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam),
    (∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock)
      (Z₀ : Point) (R : ℝ) (hR : 0 < R) (P : Point)
      (hP : P ∈ forwardCylinder Z₀ R hR),
      (c.core ∩ (capacityCylinderInterval Z₀ R hR).carrier).Nonempty →
      let nu := visitStartsQ hH hLE hlam hLam A c Z₀ R hR P hP
      IsFiniteMeasure nu ∧
      (∀ᵐ p ∂nu, p.velocity 0 ∈ closure c.entrance) ∧
      nu univ ≤ ENNReal.ofReal (C * (1 + R / c.r)) ∧
      (∀ a : ℝ, nu {p | p.time ∈ Ioc a (a + c.r ^ 2)} ≤ ENNReal.ofReal C) ∧
      (stripGreen hH hLE hlam hLam A (capacityCylinderInterval Z₀ R hR)
        (Z₀.time + R ^ 2) (capacityCylinderPole Z₀ P R hR hP)).restrict
          {p | p.velocity 0 ∈ c.core} ≤
        (enlargedActiveGreen hH hLE hlam hLam A c nu).restrict
          {p | p.velocity 0 ∈ c.core}) ∧
    (∀ q : ℝ, (1 < q ∧ q < 3 / 2) →
      ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock)
        (Z₀ : Point) (R : ℝ) (hR : 0 < R) (P : Point)
        (hP : P ∈ forwardCylinder Z₀ R hR),
        (c.core ∩ (capacityCylinderInterval Z₀ R hR).carrier).Nonempty →
        enlargedDensityBound
          ((stripGreen hH hLE hlam hLam A (capacityCylinderInterval Z₀ R hR)
            (Z₀.time + R ^ 2) (capacityCylinderPole Z₀ P R hR hP)).restrict
              {p | p.velocity 0 ∈ c.core})
          (densityObservationStrip Z₀ R hR) q
          (C * c.r ^ (6 / q - 4) * (1 + R / c.r) ^ (1 / q)))

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
