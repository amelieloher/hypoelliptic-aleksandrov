module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.InkSpots.Assembly
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Setting

/-!
# Kinetic crawling ink spots

Companion paper, Theorem 9.4, with the geometry of Section 9.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Set MeasureTheory

/-- The measure-theoretic kinetic crawling ink-spots estimate, uniform in all data. -/
theorem kinetic_crawling_ink_spots (d : ℕ) (hd : 1 ≤ d) :
    ∃ c_d C_d : ℝ, 0 < c_d ∧ c_d < 1 ∧ 0 < C_d ∧
      ∀ (m : ℕ), 0 < m →
      ∀ (eta r₀ : ℝ), 0 < eta → eta < 1 → 0 < r₀ → r₀ < 1 →
      ∀ (E F : Set (KineticPoint d)),
        Bornology.IsBounded E → Bornology.IsBounded F →
        NullMeasurableSet E volume → NullMeasurableSet F volume →
        E ⊆ F ∩ backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1 →
        (∀ (P : KineticPoint d) (r : ℝ), 0 < r →
          backwardCylinder P r ⊆ backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1 →
          (1 - eta) * (volume (backwardCylinder P r)).toReal ≤
            (volume (E ∩ backwardCylinder P r)).toReal →
          r < r₀ ∧ forwardStack P r m ⊆ F) →
        (volume E).toReal ≤
          (((m : ℝ) + 1) / (m : ℝ)) * (1 - c_d * eta) *
            ((volume (F ∩ backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1)).toReal +
              C_d * (m : ℝ) * r₀ ^ 2) := by
  exact HypoellipticAleksandrov.KineticAleksandrov.Holder.kinetic_crawling_ink_spots_aux
    d hd

end HypoellipticAleksandrov.KineticAleksandrov.Holder
