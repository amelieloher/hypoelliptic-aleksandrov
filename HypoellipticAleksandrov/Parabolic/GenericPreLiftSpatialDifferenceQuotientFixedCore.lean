module

public import HypoellipticAleksandrov.Parabolic.GenericPreLiftSpatialDifferenceQuotientFixedDirection

/-!
# Fixed-cylinder generic spatial difference-quotient estimate

This module aggregates the one-direction estimate over all spatial directions.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory Set
open scoped Convex ENNReal MatrixOrder

/-- Fixed-cylinder spatial difference-quotient control for the gradient in a
tested divergence-form equation. -/
theorem exists_gradient_spatialDifferenceQuotient_estimate_of_testedEquation
    (d : ℕ) (s₀ t₁ t₂ s₁ : ℝ)
    (hs₀t₁ : s₀ < t₁) (ht₁t₂ : t₁ < t₂) (ht₂s₁ : t₂ < s₁)
    (O₀ O₁ : Set (PDE.Vec d))
    (hO₀ : IsOpen O₀) (hO₁ : IsOpen O₁) (hO₁ne : O₁.Nonempty)
    (hO₁compact : IsCompact (closure O₁))
    (hO₁O₀ : closure O₁ ⊆ O₀)
    (lam Lam Ma : ℝ)
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam) (hMa : 0 ≤ Ma) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ (A : TimeVelocity d → PDE.Mat d) (q : TimeVelocity d → ℝ)
        (G : Fin d → TimeVelocity d → ℝ) (R : TimeVelocity d → ℝ),
        (∀ z ∈ Set.Ioo s₀ s₁ ×ˢ O₀, (A z).IsSymm) →
        (∀ z ∈ Set.Ioo s₀ s₁ ×ˢ O₀,
          lam • (1 : PDE.Mat d) ≤ A z ∧ A z ≤ Lam • (1 : PDE.Mat d)) →
        (∀ i j, ContDiffOn ℝ 1 (fun z : TimeVelocity d => A z i j)
          (Set.Ioo s₀ s₁ ×ˢ O₀)) →
        (∀ i j k z, z ∈ Set.Ioo s₀ s₁ ×ˢ O₀ →
          |spatialPartial k
              (fun y : PDE.Vec d => A (z.1, y) i j) z.2| ≤ Ma) →
        ParabolicMemLpOn (Set.Ioo s₀ s₁ ×ˢ O₀) 2 q →
        (∀ j, ParabolicMemLpOn (Set.Ioo s₀ s₁ ×ˢ O₀) 2 (G j)) →
        ParabolicMemLpOn (Set.Ioo s₀ s₁ ×ˢ O₀) 2 R →
        (∀ j, HasWeakVelocityPartialDerivOn
          (Set.Ioo s₀ s₁ ×ˢ O₀) j q (G j)) →
        (∀ φ : TimeVelocity d → ℝ,
          ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          tsupport φ ⊆ Set.Ioo s₀ s₁ ×ˢ O₀ →
          -(∫ z in Set.Ioo s₀ s₁ ×ˢ O₀,
              q z * timeDerivative φ z) -
              (∑ i, ∑ j, ∫ z in Set.Ioo s₀ s₁ ×ˢ O₀,
                A z i j * G j z * velocityGradient φ z i) =
            ∫ z in Set.Ioo s₀ s₁ ×ˢ O₀, R z * φ z) →
        ∀ h : ℝ, 0 < h → h < δ →
          (∀ j k, ParabolicMemLpOn (Set.Ioo t₁ t₂ ×ˢ O₁) 2
            (spatialDifferenceQuotient k h (G j))) ∧
          (∑ j, ∑ k, (ENNReal.toReal (eLpNorm
            (spatialDifferenceQuotient k h (G j)) 2
            (timeVelocityVolumeOn (Set.Ioo t₁ t₂ ×ˢ O₁)))) ^ 2) ≤
            C * ((ENNReal.toReal (eLpNorm q 2
              (timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O₀)))) ^ 2 +
              (∑ j, (ENNReal.toReal (eLpNorm (G j) 2
                (timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O₀)))) ^ 2) +
              (ENNReal.toReal (eLpNorm R 2
                (timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O₀)))) ^ 2) := by
  classical
  by_cases hd : d = 0
  · subst d
    refine ⟨0, 1, le_rfl, zero_lt_one, ?_⟩
    intro A q G R hSymm hEll hA hAbound hq hG hR hWeak hEq h hh hhone
    constructor
    · intro j
      exact Fin.elim0 j
    · simp
  · obtain ⟨C, δ, hC, hδ, hfixed⟩ :=
      exists_fixedDirection_gradient_spatialDifferenceQuotient_estimate_of_testedEquation
        d s₀ t₁ t₂ s₁ hs₀t₁ ht₁t₂ ht₂s₁ O₀ O₁ hO₀ hO₁ hO₁ne
        hO₁compact hO₁O₀ lam Lam Ma hlam hlamLam hMa
    refine ⟨(d : ℝ) * C, δ, mul_nonneg (Nat.cast_nonneg d) hC, hδ, ?_⟩
    intro A q G R hSymm hEll hA hAbound hq hG hR hWeak hEq h hh hhd
    have hk (k : Fin d) := hfixed A q G R hSymm hEll hA hAbound hq hG hR
      hWeak hEq k h hh hhd
    constructor
    · exact fun j k ↦ (hk k).1 j
    · have hsum := Finset.sum_le_sum fun k (_hk : k ∈ Finset.univ) ↦ (hk k).2
      rw [Finset.sum_comm]
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_ofNat, Nat.cast_id, mul_assoc] using hsum

end HypoellipticAleksandrov.Parabolic
