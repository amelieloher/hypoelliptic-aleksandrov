module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CapacityCylinder
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExponentChoice
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! # The explicitly conditional improved cylinder density statement

This is the exact source proposition `p:below-four-density`, not a proved density estimate.
The constant precedes all coefficient, cylinder, and pole data.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory

/-- The source's improved density assertion for the canonical strip Green measure. -/
def BelowFourDensityStatement : Prop :=
  ∀ (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) (alpha q : ℝ),
    (bellmanAdjointExponent (Lam / lam) ((le_div_iff₀ hlam).2
      (by simpa only [one_mul] using hLam)) - 2 < alpha ∧ alpha < 1) →
    (1 < q ∧ q < (4 - (1 - alpha)) / (3 - (1 - alpha))) →
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam)
      (Z₀ : Point) (R : ℝ) (hR : 0 < R) (P : Point)
      (hP : P ∈ forwardCylinder Z₀ R hR),
      ∃ G : Point → ℝ, Measurable G ∧ (∀ z, 0 ≤ G z) ∧
        (stripGreen hH hLE hlam hLam A (capacityCylinderInterval Z₀ R hR)
          (Z₀.time + R ^ 2) (capacityCylinderPole Z₀ P R hR hP)).restrict
            (forwardCylinder Z₀ R hR) =
          (volume.restrict (forwardCylinder Z₀ R hR)).withDensity
            (fun z => ENNReal.ofReal (G z)) ∧
        MemLp G (ENNReal.ofReal q) (volume.restrict (forwardCylinder Z₀ R hR)) ∧
        (eLpNorm G (ENNReal.ofReal q)
          (volume.restrict (forwardCylinder Z₀ R hR))).toReal ≤ C * R ^ (6 / q - 4)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
