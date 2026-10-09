module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Energy.Family

/-!
# The energy inequality integrated in `τ`, for a fixed cut-off

The energy inequality: integrate the slice inequality over `(τ₁, τ₂)`,
use the fundamental theorem of calculus for the time term, and drop the non-negative endpoint term
at `τ₂`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory Matrix
open scoped MatrixOrder

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ} {lam h q τ₁ τ₂ : ℝ} {ρ : ℝ → EvolutionAmbientState d → ℝ}
  {β J : ℝ → EvolutionAmbientState d → PDE.Mat d}

namespace EnergySetting

variable (S : EnergySetting lam h q τ₁ τ₂ ρ β J)

include S

theorem timeHyp {R₀ : ℝ} (hR : ∀ τ y, ρ τ y ≤ R₀) {D : EvolutionAmbientState d → ℝ}
    (hD : Integrable D) (hdt : ∀ τ y, |deriv (fun τ' => ρ τ' y) τ| ≤ D y) :
    TimeHyp q ρ R₀ D :=
  ⟨S.one_lt, S.smooth_rho, S.nonneg, hR, hD, hdt⟩

theorem stronglyMeasurable_energyA {ζ : EvolutionAmbientState d → ℝ} (hζ : Continuous ζ) :
    StronglyMeasurable (energyA lam h q ρ ζ) :=
  (((hζ.measurable.comp measurable_snd).mul S.measurable_FA).stronglyMeasurable
    ).integral_prod_right'

theorem stronglyMeasurable_energyB {ζ : EvolutionAmbientState d → ℝ} (hζ : Continuous ζ) :
    StronglyMeasurable (energyB lam h q ρ β ζ) :=
  (((hζ.measurable.comp measurable_snd).mul S.measurable_FB).stronglyMeasurable
    ).integral_prod_right'

theorem energyA_nonneg {ζ : EvolutionAmbientState d → ℝ} (hζ : ∀ y, 0 ≤ ζ y) (τ : ℝ) :
    0 ≤ energyA lam h q ρ ζ τ :=
  integral_nonneg fun y => mul_nonneg (hζ y) (S.measurable_FA_nonneg (τ, y))

theorem energyB_nonneg {ζ : EvolutionAmbientState d → ℝ} (hζ : ∀ y, 0 ≤ ζ y) (τ : ℝ) :
    0 ≤ energyB lam h q ρ β ζ τ :=
  integral_nonneg fun y => mul_nonneg (hζ y) (S.FB_nonneg (τ, y))

/-- The integrated energy inequality for a fixed cut-off, as an inequality of reals. -/
theorem integrated_real {Bv ε : ℝ} {ζ : EvolutionAmbientState d → ℝ} (Z : CutoffData Bv ε ζ)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ τ ∈ Set.Ioo τ₁ τ₂, (∀ y, ρ τ y = 0) ∨
      (NonzeroSlice lam h q (ρ τ) (fun y => deriv (fun τ' => ρ τ' y) τ) (β τ) (J τ) ∧
        (∫ y, ρ τ y ^ (q - 1) * gradNorm (ρ τ) y) ≤ C ∧
        (∫ y, ρ τ y ^ (q - 1) * coefficientGradNorm (J τ) y) ≤ C))
    (hB : IntegrableOn (energyB lam h q ρ β ζ) (Set.Ioo τ₁ τ₂)) :
    IntegrableOn (energyA lam h q ρ ζ) (Set.Ioo τ₁ τ₂) ∧
    q * (q - 1) / 4 * (∫ τ in Set.Ioo τ₁ τ₂, energyA lam h q ρ ζ τ) ≤
      (∫ y, ρ τ₁ y ^ q) +
        4 * d * q * (q - 1) / lam ^ 2 * (∫ τ in Set.Ioo τ₁ τ₂, energyB lam h q ρ β ζ τ) +
        q * ε * d * ((|lam * h / 2| + d) * C) * (τ₂ - τ₁) := by
  have hq := S.one_lt
  have hlam := S.lam_pos
  have h12 := S.lt
  obtain ⟨R₀, hR⟩ := S.bounded
  obtain ⟨D, hD, hdt⟩ := S.time_dom
  have TH := S.timeHyp hR hD hdt
  have hζc := Z.smooth.continuous
  have hc₁pos : 0 < q * (q - 1) / 4 := by
    have : 0 < q - 1 := by linarith
    positivity
  have hf1 : IntegrableOn (cutoffMassDeriv q ρ ζ) (Set.Ioo τ₁ τ₂) :=
    ((TH.intervalIntegrable_cutoffMassDeriv hζc Z.abs_le_one τ₁ τ₂).1).mono_set
      Set.Ioo_subset_Ioc_self
  have hpt : ∀ τ ∈ Set.Ioo τ₁ τ₂, q * (q - 1) / 4 * energyA lam h q ρ ζ τ ≤
      4 * d * q * (q - 1) / lam ^ 2 * energyB lam h q ρ β ζ τ +
        q * ε * d * ((|lam * h / 2| + d) * C) - cutoffMassDeriv q ρ ζ τ := fun τ hτ => by
    have h1 := S.slice_inequality Z hC hτ
    have h2 := S.energyG_le hC0 hC hτ
    have h3 : 0 ≤ q * ε * d := by
      have := Z.eps_nonneg
      have : 0 ≤ q := by linarith
      positivity
    have h4 := mul_le_mul_of_nonneg_left h2 h3
    linarith
  have hgint : Integrable (fun τ => 4 * d * q * (q - 1) / lam ^ 2 * energyB lam h q ρ β ζ τ +
      q * ε * d * ((|lam * h / 2| + d) * C) - cutoffMassDeriv q ρ ζ τ)
      (volume.restrict (Set.Ioo τ₁ τ₂)) :=
    ((hB.const_mul _).add (integrable_const _)).sub hf1
  have hAmeas : AEStronglyMeasurable (energyA lam h q ρ ζ) (volume.restrict (Set.Ioo τ₁ τ₂)) :=
    (S.stronglyMeasurable_energyA hζc).aestronglyMeasurable
  have hAint : Integrable (energyA lam h q ρ ζ) (volume.restrict (Set.Ioo τ₁ τ₂)) := by
    refine (hgint.div_const (q * (q - 1) / 4)).mono' hAmeas ?_
    refine (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun τ hτ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (S.energyA_nonneg Z.nonneg τ), le_div_iff₀ hc₁pos]
    have := hpt τ hτ
    linarith
  have hmono := integral_mono_ae (hAint.const_mul (q * (q - 1) / 4)) hgint
    ((ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall hpt))
  have hg1 : Integrable (fun τ => 4 * d * q * (q - 1) / lam ^ 2 * energyB lam h q ρ β ζ τ +
      q * ε * d * ((|lam * h / 2| + d) * C)) (volume.restrict (Set.Ioo τ₁ τ₂)) :=
    (hB.const_mul _).add (integrable_const _)
  rw [integral_const_mul, integral_sub hg1 hf1,
    integral_add (hB.const_mul _) (integrable_const _), integral_const_mul] at hmono
  have hconst : ∫ _τ in Set.Ioo τ₁ τ₂, q * ε * d * ((|lam * h / 2| + d) * C) =
      q * ε * d * ((|lam * h / 2| + d) * C) * (τ₂ - τ₁) := by
    rw [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Ioo,
      ENNReal.toReal_ofReal (by linarith)]
    ring
  rw [hconst] at hmono
  have hFTC : ∫ τ in Set.Ioo τ₁ τ₂, cutoffMassDeriv q ρ ζ τ =
      cutoffMass q ρ ζ τ₂ - cutoffMass q ρ ζ τ₁ := by
    rw [← TH.integral_cutoffMassDeriv hζc Z.abs_le_one h12.le S.pow_integrable,
      intervalIntegral.integral_of_le h12.le, integral_Ioc_eq_integral_Ioo]
  have ha2 : 0 ≤ cutoffMass q ρ ζ τ₂ :=
    integral_nonneg fun y => mul_nonneg (Z.nonneg y) (Real.rpow_nonneg (S.nonneg _ _) _)
  have ha1 : cutoffMass q ρ ζ τ₁ ≤ ∫ y, ρ τ₁ y ^ q := by
    refine integral_mono ?_ (S.pow_integrable τ₁ ⟨le_rfl, h12.le⟩) fun y => ?_
    · exact integrable_cutoff_mul Z.smooth.continuous Z.abs_le_one
        (S.pow_integrable τ₁ ⟨le_rfl, h12.le⟩)
    · exact mul_le_of_le_one_left (Real.rpow_nonneg (S.nonneg _ _) _) (Z.le_one y)
  rw [hFTC] at hmono
  refine ⟨hAint, ?_⟩
  linarith

end EnergySetting

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
