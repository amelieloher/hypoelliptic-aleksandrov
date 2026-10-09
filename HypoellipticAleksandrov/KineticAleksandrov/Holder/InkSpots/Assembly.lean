module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.InkSpots.AssemblySmall
import Mathlib.Tactic

/-! # Internally proved kinetic crawling ink spots

The theorem retains the full statement, including every quantifier and both error
and delay factors. Critical cylinders, density reduction, delayed unions and leakage
are all proved internally. No external covering premise is used.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Set MeasureTheory Covering InkSpots

/-- Kinetic crawling ink spots with dimension-only constants and the leakage error. -/
theorem kinetic_crawling_ink_spots_aux (d : ℕ) (_hd : 1 ≤ d) :
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
  obtain ⟨hc, hc1⟩ := coveringGain_bounds d
  obtain ⟨hC, hCV⟩ := coveringLeakage_bounds d
  refine ⟨coveringGain d, coveringLeakage d, hc, by linarith, hC, ?_⟩
  intro m hm eta R heta heta1 hR hR1 E F hEb _hFb hE _hF hEF hstack
  have hEQ : E ⊆ unitCylinder d := fun X hX => (hEF hX).2
  have hs : ∀ P r, 0 < r → backwardCylinder P r ⊆ unitCylinder d →
      (1-eta)*(volume (backwardCylinder P r)).toReal ≤
        (volume (E ∩ backwardCylinder P r)).toReal →
      r < R ∧ forwardStack P r m ⊆ F := hstack
  by_cases hsmall : R ≤ 1/4
  · by_cases hheight : (m : ℝ)*R^2 ≤ 1
    · exact ink_spots_small_cutoff hE hEb hEQ heta heta1 hR hsmall m hm hheight hs
    · have hlarge : 1/16 ≤ (m : ℝ)*R^2 := by linarith only [hheight]
      have hbound := trivial_large_height
        (ENNReal.toReal_nonneg (a := volume (unitCylinder d)))
        (ENNReal.toReal_nonneg (a := volume (F ∩ unitCylinder d))) hCV
        (delay_multiplier_ge_one hm) (density_factor_bounds d heta heta1).1 hlarge
      have hmono := ENNReal.toReal_mono (volume_cylinder_pos_ne_top _ zero_lt_one).2
        (measure_mono hEQ)
      exact hmono.trans (by simpa only [mul_assoc, unitCylinder] using hbound)
  · have hm1 : 1 ≤ (m : ℝ) := by exact_mod_cast hm
    have hlarge : 1/16 ≤ (m : ℝ)*R^2 := by nlinarith
    have hbound := trivial_large_height
      (ENNReal.toReal_nonneg (a := volume (unitCylinder d)))
      (ENNReal.toReal_nonneg (a := volume (F ∩ unitCylinder d))) hCV
      (delay_multiplier_ge_one hm) (density_factor_bounds d heta heta1).1 hlarge
    have hmono := ENNReal.toReal_mono (volume_cylinder_pos_ne_top _ zero_lt_one).2
      (measure_mono hEQ)
    exact hmono.trans (by simpa only [mul_assoc, unitCylinder] using hbound)

end HypoellipticAleksandrov.KineticAleksandrov.Holder
