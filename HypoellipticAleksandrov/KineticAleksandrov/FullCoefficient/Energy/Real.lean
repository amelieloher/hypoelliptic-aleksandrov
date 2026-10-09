module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Energy.Product

/-!
# The energy inequality for real integrals

The energy inequality: if the slice integrals of `ρ^q |Dβ|²` are uniformly
bounded, then all the space-time integrals are finite, and the energy inequality holds for
Bochner integrals over `(τ₁, τ₂) × ℝ^{2d}`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ} {lam h q τ₁ τ₂ : ℝ} {ρ : ℝ → EvolutionAmbientState d → ℝ}
  {β J : ℝ → EvolutionAmbientState d → PDE.Mat d}

/-- From an inequality of lower integrals of non-negative functions with finite right-hand side
to the corresponding inequality of Bochner integrals. -/
theorem real_of_lintegral_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {FA FB : α → ℝ}
    (hA : Measurable FA) (hB : Measurable FB) (hA0 : ∀ a, 0 ≤ FA a) (hB0 : ∀ a, 0 ≤ FB a)
    {c₁ c₂ I₀ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 ≤ c₂) (hI₀ : 0 ≤ I₀)
    (hB' : ∫⁻ a, ENNReal.ofReal (FB a) ∂μ < ⊤)
    (h : ENNReal.ofReal c₁ * ∫⁻ a, ENNReal.ofReal (FA a) ∂μ ≤
      ENNReal.ofReal I₀ + ENNReal.ofReal c₂ * ∫⁻ a, ENNReal.ofReal (FB a) ∂μ) :
    Integrable FA μ ∧ Integrable FB μ ∧
      c₁ * ∫ a, FA a ∂μ ≤ I₀ + c₂ * ∫ a, FB a ∂μ := by
  have hr : ENNReal.ofReal I₀ + ENNReal.ofReal c₂ * ∫⁻ a, ENNReal.ofReal (FB a) ∂μ < ⊤ :=
    ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, ENNReal.mul_lt_top ENNReal.ofReal_lt_top hB'⟩
  have hXlt : ∫⁻ a, ENNReal.ofReal (FA a) ∂μ < ⊤ := by
    by_contra hcon
    have htop : ∫⁻ a, ENNReal.ofReal (FA a) ∂μ = ⊤ := not_lt_top_iff.1 hcon
    rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.2 hc₁).ne'] at h
    exact absurd h (not_le.2 hr)
  have iA : Integrable FA μ :=
    (lintegral_ofReal_ne_top_iff_integrable hA.aestronglyMeasurable
      (Filter.Eventually.of_forall hA0)).1 hXlt.ne
  have iB : Integrable FB μ :=
    (lintegral_ofReal_ne_top_iff_integrable hB.aestronglyMeasurable
      (Filter.Eventually.of_forall hB0)).1 hB'.ne
  refine ⟨iA, iB, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal iA (Filter.Eventually.of_forall hA0),
    ← ofReal_integral_eq_lintegral_ofReal iB (Filter.Eventually.of_forall hB0),
    ← ENNReal.ofReal_mul hc₁.le, ← ENNReal.ofReal_mul hc₂,
    ← ENNReal.ofReal_add hI₀ (mul_nonneg hc₂ (integral_nonneg hB0))] at h
  exact (ENNReal.ofReal_le_ofReal_iff (add_nonneg hI₀ (mul_nonneg hc₂
    (integral_nonneg hB0)))).1 h

namespace EnergySetting

variable (S : EnergySetting lam h q τ₁ τ₂ ρ β J)

include S

/-- The coefficient term is finite when the slice integrals of `ρ^q |Dβ|²` are bounded. -/
theorem lintegral_FB_lt_top {C' : ℝ}
    (hC' : ∀ τ ∈ Set.Ioo τ₁ τ₂, ∫ y, ρ τ y ^ q * coefficientGradNormSq (β τ) y ≤ C') :
    ∫⁻ τ in Set.Ioo τ₁ τ₂, ∫⁻ y,
      ENNReal.ofReal (ρ τ y ^ q * coefficientGammaSum lam h (β τ) y) < ⊤ := by
  have hq := S.one_lt
  have hq0 : q ≠ 0 := by linarith
  obtain ⟨C, hC0, hC⟩ := S.slices
  have hK : 0 ≤ lam / 2 * (3 * h ^ 2 + 2) := by
    have := S.lam_pos
    positivity
  have hle : ∀ τ ∈ Set.Ioo τ₁ τ₂, ∫⁻ y, ENNReal.ofReal
      (ρ τ y ^ q * coefficientGammaSum lam h (β τ) y) ≤
      ENNReal.ofReal (lam / 2 * (3 * h ^ 2 + 2) * C') := fun τ hτ => by
    rcases hC τ hτ with hz | ⟨hS, -, -⟩
    · have : ∀ y, ρ τ y ^ q * coefficientGammaSum lam h (β τ) y = 0 := fun y => by
        rw [hz y, Real.zero_rpow hq0, zero_mul]
      simp only [this, ENNReal.ofReal_zero, lintegral_zero]
      exact zero_le
    · have hint := hS.integrable.betaGradSq.const_mul (lam / 2 * (3 * h ^ 2 + 2))
      calc ∫⁻ y, ENNReal.ofReal (ρ τ y ^ q * coefficientGammaSum lam h (β τ) y)
          ≤ ∫⁻ y, ENNReal.ofReal (lam / 2 * (3 * h ^ 2 + 2) *
              (ρ τ y ^ q * coefficientGradNormSq (β τ) y)) := by
            refine lintegral_mono fun y => ENNReal.ofReal_le_ofReal ?_
            have h0 : 0 ≤ ρ τ y ^ q := Real.rpow_nonneg (S.nonneg _ _) _
            have := coefficientGammaSum_le (h := h) S.lam_pos (β τ) y
            calc ρ τ y ^ q * coefficientGammaSum lam h (β τ) y
                ≤ ρ τ y ^ q * (lam / 2 * (3 * h ^ 2 + 2) * coefficientGradNormSq (β τ) y) :=
                  mul_le_mul_of_nonneg_left this h0
              _ = _ := by ring
        _ = ENNReal.ofReal (∫ y, lam / 2 * (3 * h ^ 2 + 2) *
              (ρ τ y ^ q * coefficientGradNormSq (β τ) y)) :=
            (ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun y =>
              mul_nonneg hK (mul_nonneg (Real.rpow_nonneg (S.nonneg _ _) _)
                (coefficientGradNormSq_nonneg _ _)))).symm
        _ ≤ ENNReal.ofReal (lam / 2 * (3 * h ^ 2 + 2) * C') := by
            rw [integral_const_mul]
            exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hC' τ hτ) hK)
  calc ∫⁻ τ in Set.Ioo τ₁ τ₂, ∫⁻ y, ENNReal.ofReal
        (ρ τ y ^ q * coefficientGammaSum lam h (β τ) y)
      ≤ ∫⁻ _τ in Set.Ioo τ₁ τ₂, ENNReal.ofReal (lam / 2 * (3 * h ^ 2 + 2) * C') :=
        setLIntegral_mono' measurableSet_Ioo hle
    _ = ENNReal.ofReal (lam / 2 * (3 * h ^ 2 + 2) * C') * volume (Set.Ioo τ₁ τ₂) :=
        setLIntegral_const _ _
    _ < ⊤ := by
        rw [Real.volume_Ioo]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

/-- **The energy inequality for real integrals**: finiteness and the
inequality for Bochner integrals over `(τ₁, τ₂) × ℝ^{2d}`. -/
theorem energy_inequality_real {C' : ℝ}
    (hC' : ∀ τ ∈ Set.Ioo τ₁ τ₂, ∫ y, ρ τ y ^ q * coefficientGradNormSq (β τ) y ≤ C') :
    Integrable (fun p : ℝ × EvolutionAmbientState d =>
        ρ p.1 p.2 ^ (q - 2) * flowGamma lam h (ρ p.1) (ρ p.1) p.2)
      (volume.restrict (Set.Ioo τ₁ τ₂ ×ˢ (Set.univ : Set (EvolutionAmbientState d)))) ∧
    Integrable (fun p : ℝ × EvolutionAmbientState d =>
        ρ p.1 p.2 ^ q * coefficientGammaSum lam h (β p.1) p.2)
      (volume.restrict (Set.Ioo τ₁ τ₂ ×ˢ (Set.univ : Set (EvolutionAmbientState d)))) ∧
    q * (q - 1) / 4 * ∫ p in Set.Ioo τ₁ τ₂ ×ˢ (Set.univ : Set (EvolutionAmbientState d)),
        ρ p.1 p.2 ^ (q - 2) * flowGamma lam h (ρ p.1) (ρ p.1) p.2 ≤
      (∫ y, ρ τ₁ y ^ q) + 4 * d * q * (q - 1) / lam ^ 2 *
        ∫ p in Set.Ioo τ₁ τ₂ ×ˢ (Set.univ : Set (EvolutionAmbientState d)),
          ρ p.1 p.2 ^ q * coefficientGammaSum lam h (β p.1) p.2 := by
  have hq := S.one_lt
  have hlam := S.lam_pos
  have hY := S.lintegral_FB_lt_top hC'
  have hBm : Measurable fun p : ℝ × EvolutionAmbientState d =>
      ENNReal.ofReal (ρ p.1 p.2 ^ q * coefficientGammaSum lam h (β p.1) p.2) :=
    ENNReal.measurable_ofReal.comp S.measurable_FB
  have hYμ : ∫⁻ p, ENNReal.ofReal (ρ p.1 p.2 ^ q * coefficientGammaSum lam h (β p.1) p.2)
      ∂(volume.restrict (Set.Ioo τ₁ τ₂ ×ˢ (Set.univ : Set (EvolutionAmbientState d)))) < ⊤ := by
    calc _ = ∫⁻ τ in Set.Ioo τ₁ τ₂, ∫⁻ y,
          ENNReal.ofReal (ρ τ y ^ q * coefficientGammaSum lam h (β τ) y) :=
          lintegral_Ioo_prod τ₁ τ₂ hBm
      _ < ⊤ := hY
  have hL : ENNReal.ofReal (∫ y, ρ τ₁ y ^ q) = ∫⁻ y, ENNReal.ofReal (ρ τ₁ y ^ q) :=
    ofReal_integral_eq_lintegral_ofReal (S.pow_integrable τ₁ ⟨le_rfl, S.lt.le⟩)
      (Filter.Eventually.of_forall fun y => Real.rpow_nonneg (S.nonneg _ _) _)
  have hc₁ : 0 < q * (q - 1) / 4 := by
    have : 0 < q - 1 := by linarith
    positivity
  have hc₂ : 0 ≤ 4 * (d : ℝ) * q * (q - 1) / lam ^ 2 := by
    have : 0 < q - 1 := by linarith
    positivity
  have hI₀ : 0 ≤ ∫ y, ρ τ₁ y ^ q := integral_nonneg fun y => Real.rpow_nonneg (S.nonneg _ _) _
  have hmain := S.energy_inequality_prod
  rw [← hL] at hmain
  exact real_of_lintegral_le (S.measurable_FA) (S.measurable_FB) S.measurable_FA_nonneg
    S.FB_nonneg hc₁ hc₂ hI₀ hYμ hmain

end EnergySetting

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
