module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Energy.Green

/-!
# The energy inequality over the product `(τ₁, τ₂) × ℝ^{2d}`

The energy inequality: the iterated integrals of `Energy.Abstract` are
integrals over the product space `(τ₁, τ₂) × ℝ^{2d}` with respect to Lebesgue measure, by
Tonelli's theorem (the integrands are jointly measurable).
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ}

/-- Tonelli for the slab `(a, b) × ℝ^{2d}`. -/
theorem lintegral_Ioo_prod (a b : ℝ) {f : ℝ × EvolutionAmbientState d → ENNReal}
    (hf : Measurable f) :
    ∫⁻ p in Set.Ioo a b ×ˢ (Set.univ : Set (EvolutionAmbientState d)), f p =
      ∫⁻ τ in Set.Ioo a b, ∫⁻ y, f (τ, y) := by
  have : (volume : Measure (ℝ × EvolutionAmbientState d)).restrict
      (Set.Ioo a b ×ˢ (Set.univ : Set (EvolutionAmbientState d))) =
      (volume.restrict (Set.Ioo a b)).prod volume := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  rw [this, lintegral_prod _ hf.aemeasurable]

variable {lam h q τ₁ τ₂ : ℝ} {ρ : ℝ → EvolutionAmbientState d → ℝ}
  {β J : ℝ → EvolutionAmbientState d → PDE.Mat d}

/-- **The energy inequality over the product**. -/
theorem EnergySetting.energy_inequality_prod (S : EnergySetting lam h q τ₁ τ₂ ρ β J) :
    ENNReal.ofReal (q * (q - 1) / 4) *
        ∫⁻ p in Set.Ioo τ₁ τ₂ ×ˢ (Set.univ : Set (EvolutionAmbientState d)),
          ENNReal.ofReal (ρ p.1 p.2 ^ (q - 2) * flowGamma lam h (ρ p.1) (ρ p.1) p.2) ≤
      (∫⁻ y, ENNReal.ofReal (ρ τ₁ y ^ q)) +
        ENNReal.ofReal (4 * d * q * (q - 1) / lam ^ 2) *
          ∫⁻ p in Set.Ioo τ₁ τ₂ ×ˢ (Set.univ : Set (EvolutionAmbientState d)),
            ENNReal.ofReal (ρ p.1 p.2 ^ q * coefficientGammaSum lam h (β p.1) p.2) := by
  have hA : Measurable fun p : ℝ × EvolutionAmbientState d =>
      ENNReal.ofReal (ρ p.1 p.2 ^ (q - 2) * flowGamma lam h (ρ p.1) (ρ p.1) p.2) :=
    ENNReal.measurable_ofReal.comp S.measurable_FA
  have hB : Measurable fun p : ℝ × EvolutionAmbientState d =>
      ENNReal.ofReal (ρ p.1 p.2 ^ q * coefficientGammaSum lam h (β p.1) p.2) :=
    ENNReal.measurable_ofReal.comp S.measurable_FB
  rw [lintegral_Ioo_prod τ₁ τ₂ hA, lintegral_Ioo_prod τ₁ τ₂ hB]
  exact S.energy_inequality

section Datum

variable {δ : ℝ} {η : ℝ → ℝ} {Lam T : ℝ} {Bt : ℝ → EvolutionAmbientState d → PDE.Mat d}
  {Γ' : Measure (ℝ × EvolutionAmbientState d)}

/-- **The energy inequality for a smoothing datum, over the product**. -/
theorem energy_inequality_datum_prod (Φ : SmoothingKernelFamily d lam) (hη : IsMollifier δ η)
    (hD : IsSmoothingDatum lam Lam Bt Γ') (hh : 0 < h) (hδ : 0 < δ) (hq : 1 < q)
    (hτ : τ₁ < τ₂) (hτ₁ : δ < τ₁) (hτ₂ : τ₂ + δ < T) (hfwd : IsForwardMeasure T Bt Γ')
    (hcomm : ∀ w, transportDerivative (Φ.kernel h) w =
      lam * h ^ 2 / 2 * positionLaplacian (Φ.kernel h) w -
        lam * h * mixedDivergence (Φ.kernel h) w) :
    ENNReal.ofReal (q * (q - 1) / 4) *
        ∫⁻ p in Set.Ioo τ₁ τ₂ ×ˢ (Set.univ : Set (EvolutionAmbientState d)),
          ENNReal.ofReal (smoothedDensity Φ η h Γ' p.1 p.2 ^ (q - 2) *
            flowGamma lam h (smoothedDensity Φ η h Γ' p.1) (smoothedDensity Φ η h Γ' p.1) p.2) ≤
      (∫⁻ y, ENNReal.ofReal (smoothedDensity Φ η h Γ' τ₁ y ^ q)) +
        ENNReal.ofReal (4 * d * q * (q - 1) / lam ^ 2) *
          ∫⁻ p in Set.Ioo τ₁ τ₂ ×ˢ (Set.univ : Set (EvolutionAmbientState d)),
            ENNReal.ofReal (smoothedDensity Φ η h Γ' p.1 p.2 ^ q *
              coefficientGammaSum lam h (smoothedBeta Φ η Bt Lam h Γ' p.1) p.2) :=
  (energySetting_of_datum Φ hη hD hh hδ hq hτ hτ₁ hτ₂ hfwd hcomm).energy_inequality_prod

end Datum

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
