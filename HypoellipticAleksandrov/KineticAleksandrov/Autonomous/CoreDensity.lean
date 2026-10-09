module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EntranceStatement
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.LogCover
import Mathlib.Tactic

/-! # Preliminary core density from the literal entrance estimate -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory

/-- At exponent six fifths the entrance estimate gives the preliminary core norm. -/
theorem preliminary_core_density_of_entrance (hentrance : EntranceStatement)
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock)
      (Z₀ : Point) (R : ℝ) (hR : 0 < R) (P : Point)
      (hP : P ∈ forwardCylinder Z₀ R hR),
      (c.core ∩ (capacityCylinderInterval Z₀ R hR).carrier).Nonempty →
      enlargedDensityBound
        ((stripGreen hH hLE hlam hLam A (capacityCylinderInterval Z₀ R hR)
          (Z₀.time + R ^ 2) (capacityCylinderPole Z₀ P R hR hP)).restrict
            {p | p.velocity 0 ∈ c.core})
        (densityObservationStrip Z₀ R hR) (6 / 5)
        (C * c.r * (1 + R / c.r) ^ (5 / 6 : ℝ)) := by
  obtain ⟨C, hC, hc⟩ := (hentrance hH hLE lam Lam hlam hLam).2 (6 / 5)
    (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro A c Z₀ R hR P hP hmeet
  simpa only [show (6 / (6 / 5) - 4 : ℝ) = 1 by norm_num,
    show (1 / (6 / 5) : ℝ) = 5 / 6 by norm_num, Real.rpow_one]
    using hc A c Z₀ R hR P hP hmeet

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
