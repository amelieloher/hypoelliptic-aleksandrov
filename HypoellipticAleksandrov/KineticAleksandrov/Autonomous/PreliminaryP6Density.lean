module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDensityNear
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FarVelocityDensity
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PoleDensityStatement
import Mathlib.Tactic

/-! # Uniform preliminary cylinder density at exponent six fifths -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory

/-- Entrance counting, capacity and the one-sign proposition give the preliminary density. -/
theorem preliminary_cylinder_density_of_entrance (hentrance : EntranceStatement)
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam)
      (Z₀ : Point) (R : ℝ) (hR : 0 < R) (P : Point)
      (hP : P ∈ forwardCylinder Z₀ R hR),
      enlargedDensityBound
        ((stripGreen hH hLE hlam hLam A (capacityCylinderInterval Z₀ R hR)
          (Z₀.time + R ^ 2) (capacityCylinderPole Z₀ P R hR hP)).restrict
            (forwardCylinder Z₀ R hR)) (forwardCylinder Z₀ R hR) (6 / 5) (C * R) := by
  obtain ⟨C₁, hC₁, hn⟩ := preliminary_near_density_of_entrance hentrance
    hH hLE lam Lam hlam hLam
  obtain ⟨C₂, hC₂, hf⟩ := cylinder_density_far (pushforwardStatement_holds)
    hH hLE lam Lam hlam hLam (6 / 5) (by norm_num)
  refine ⟨max C₁ C₂, hC₁.trans_le (le_max_left _ _), ?_⟩
  intro A Z₀ R hR P hP
  by_cases hnear : |Z₀.velocity 0| ≤ 8 * R
  · obtain ⟨g, hg, hgp, hgn⟩ := hn A Z₀ R hR P hP hnear
    exact ⟨g, hg, hgp, hgn.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hR.le)⟩
  · obtain ⟨g, hgm, hg0, hgd, hgp, hgn⟩ := hf A Z₀ R hR P hP (lt_of_not_ge hnear)
    norm_num only [show (6 / (6 / 5) - 4 : ℝ) = 1 by norm_num, Real.rpow_one] at hgn
    exact ⟨g, ⟨hgm, hg0, hgd⟩, hgp,
      hgn.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hR.le)⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
