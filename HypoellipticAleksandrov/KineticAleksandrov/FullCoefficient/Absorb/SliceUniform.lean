module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Absorb.SlicePowBeta

/-!
# Uniform bounds on the slice `h`-derivatives

The time-integrated identities: the slice derivatives
`∫ q r^{q-1} (M^h : D² r)` and `∫ ∂_h (r^q |β|²)` are bounded uniformly over all finite slice
measures of mass at most `M` and over `h` in a compact subset of `(0, ∞)`. This is what allows
differentiating under the integral in the slice time `τ`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ} {lam Lam : ℝ} (Φ : SmoothingKernelFamily d lam) {q : ℝ}

local instance volumeIsAddHaarMeasureAbsorb (d : ℕ) :
    Measure.IsAddHaarMeasure (volume : Measure (EvolutionAmbientState d)) :=
  Measure.prod.instIsAddHaarMeasure _ _

theorem integrandPowDeriv_zero {h : ℝ} (hq : 1 < q) (y : EvolutionAmbientState d) :
    integrandPowDeriv Φ h q (0 : Measure (EvolutionAmbientState d)) y = 0 := by
  simp [integrandPowDeriv, smoothDensity_zero, Real.zero_rpow (by linarith : q - 1 ≠ 0)]

theorem integrandPowBetaDeriv_zero {h : ℝ} {F : EvolutionAmbientState d → PDE.Mat d}
    (y : EvolutionAmbientState d) :
    integrandPowBetaDeriv Φ h F (0 : Measure (EvolutionAmbientState d)) q y = 0 := by
  simp [integrandPowBetaDeriv, smoothFluxEntry]

theorem exists_bound_powDeriv {K : Set ℝ} (hK : IsCompact K) (hsub : K ⊆ Set.Ioi 0)
    (hq : 1 < q) {M : ℝ} (hM : 0 ≤ M) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ (m : Measure (EvolutionAmbientState d)) [IsFiniteMeasure m],
      m.real Set.univ ≤ M → ∀ s ∈ K, |∫ y, integrandPowDeriv Φ s q m y| ≤ b := by
  obtain ⟨G, A, Cs, hGc, hGi, hG0, hA0, hCs0, hdom⟩ := exists_heat_dominator_uniform Φ hK hsub
  have hR0 : 0 ≤ Cs * M := by positivity
  have hq0 : 0 ≤ q := by linarith
  refine ⟨q * (Cs * M) ^ (q - 1) * (A * (M * ∫ y, G y)), ?_, ?_⟩
  · have : 0 ≤ ∫ y, G y := integral_nonneg hG0
    have := Real.rpow_nonneg hR0 (q - 1)
    positivity
  intro m _ hmM s hs
  by_cases hm : m = 0
  · subst hm
    simp only [integrandPowDeriv_zero Φ hq, integral_zero, abs_zero]
    have : 0 ≤ ∫ y, G y := integral_nonneg hG0
    have := Real.rpow_nonneg hR0 (q - 1)
    positivity
  · have hdom' : ∀ h ∈ K, (∀ y, smoothDensity Φ h m y ≤ Cs * M) ∧
        ∀ (f : EvolutionAmbientState d → ℝ) (Cf : ℝ), Measurable f → (∀ a, |f a| ≤ Cf) →
          ∀ y, |heatOperator lam h (smoothWeighted Φ h f m) y| ≤
            Cf * A * ∫ a, G (y - a) ∂m := fun h hh => by
      obtain ⟨h1, h2⟩ := hdom m h hh
      exact ⟨fun y => (h1 y).trans (mul_le_mul_of_nonneg_left hmM hCs0), h2⟩
    obtain ⟨hDi, hDint⟩ := integrable_smoothing_translate hGi hGc m
    have hbound : ∀ y, ‖integrandPowDeriv Φ s q m y‖ ≤
        q * (Cs * M) ^ (q - 1) * (A * ∫ a, G (y - a) ∂m) := fun y => by
      rw [Real.norm_eq_abs]
      exact abs_density_deriv_le Φ m hm hq hsub hR0 hdom' hs y
    have := norm_integral_le_of_norm_le ((hDi.const_mul A).const_mul (q * (Cs * M) ^ (q - 1)))
      (Filter.Eventually.of_forall hbound)
    rw [integral_const_mul, integral_const_mul, hDint] at this
    rw [Real.norm_eq_abs] at this
    refine this.trans ?_
    have hI : 0 ≤ ∫ y, G y := integral_nonneg hG0
    have := Real.rpow_nonneg hR0 (q - 1)
    gcongr

theorem exists_bound_powBetaDeriv {K : Set ℝ} (hK : IsCompact K) (hsub : K ⊆ Set.Ioi 0)
    (hlam : 0 < lam) (hLam' : lam ≤ Lam) (hq : 1 < q) {M : ℝ} (hM : 0 ≤ M) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ (m : Measure (EvolutionAmbientState d)) [IsFiniteMeasure m]
      (F : EvolutionAmbientState d → PDE.Mat d), IsAdmissibleCoefficient lam Lam F →
      m.real Set.univ ≤ M → ∀ s ∈ K, |∫ y, integrandPowBetaDeriv Φ s F m q y| ≤ b := by
  obtain ⟨G, A, Cs, hGc, hGi, hG0, hA0, hCs0, hdom⟩ := exists_heat_dominator_uniform Φ hK hsub
  have hR0 : 0 ≤ Cs * M := by positivity
  have hLam : 0 ≤ Lam := (hlam.trans_le hLam').le
  set Bd : ℝ := (d : ℝ) ^ 2 * ((|q - 2| + 2) * Lam ^ 2 * (Cs * M) ^ (q - 1)) with hBd
  have hBd0 : 0 ≤ Bd := by
    have := Real.rpow_nonneg hR0 (q - 1)
    positivity
  refine ⟨Bd * (A * (M * ∫ y, G y)), ?_, ?_⟩
  · have : 0 ≤ ∫ y, G y := integral_nonneg hG0
    positivity
  intro m _ F hF hmM s hs
  by_cases hm : m = 0
  · subst hm
    simp only [integrandPowBetaDeriv_zero Φ, integral_zero, abs_zero]
    have : 0 ≤ ∫ y, G y := integral_nonneg hG0
    positivity
  · have hdom' : ∀ h ∈ K, (∀ y, smoothDensity Φ h m y ≤ Cs * M) ∧
        ∀ (f : EvolutionAmbientState d → ℝ) (Cf : ℝ), Measurable f → (∀ a, |f a| ≤ Cf) →
          ∀ y, |heatOperator lam h (smoothWeighted Φ h f m) y| ≤
            Cf * A * ∫ a, G (y - a) ∂m := fun h hh => by
      obtain ⟨h1, h2⟩ := hdom m h hh
      exact ⟨fun y => (h1 y).trans (mul_le_mul_of_nonneg_left hmM hCs0), h2⟩
    obtain ⟨hDi, hDint⟩ := integrable_smoothing_translate hGi hGc m
    have hbound : ∀ y, ‖integrandPowBetaDeriv Φ s F m q y‖ ≤
        Bd * (A * ∫ a, G (y - a) ∂m) := fun y => by
      rw [Real.norm_eq_abs]
      exact abs_powBeta_deriv_le Φ m hlam hLam' hF hm hq hsub hdom' hs y
    have := norm_integral_le_of_norm_le ((hDi.const_mul A).const_mul Bd)
      (Filter.Eventually.of_forall hbound)
    rw [integral_const_mul, integral_const_mul, hDint] at this
    rw [Real.norm_eq_abs] at this
    refine this.trans ?_
    have hI : 0 ≤ ∫ y, G y := integral_nonneg hG0
    gcongr

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
