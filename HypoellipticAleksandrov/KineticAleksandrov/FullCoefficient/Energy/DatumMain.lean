module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Energy.Datum

/-!
# The energy inequality for a smoothing datum: statement

The energy inequality, for the abstract smoothing datum of `Smoothed/*`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory
open scoped MatrixOrder

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ} {δ : ℝ} {η : ℝ → ℝ} {lam Lam : ℝ}
  {Bt : ℝ → EvolutionAmbientState d → PDE.Mat d} {Γ' : Measure (ℝ × EvolutionAmbientState d)}

/-- The hypotheses of the energy inequality hold for the smoothed density, flux and coefficient
of a smoothing datum. -/
theorem energySetting_of_datum (Φ : SmoothingKernelFamily d lam) (hη : IsMollifier δ η)
    (hD : IsSmoothingDatum lam Lam Bt Γ') {h q τ₁ τ₂ T : ℝ} (hh : 0 < h) (hδ : 0 < δ)
    (hq : 1 < q) (hτ : τ₁ < τ₂) (hτ₁ : δ < τ₁) (hτ₂ : τ₂ + δ < T)
    (hfwd : IsForwardMeasure T Bt Γ')
    (hcomm : ∀ w, transportDerivative (Φ.kernel h) w =
      lam * h ^ 2 / 2 * positionLaplacian (Φ.kernel h) w -
        lam * h * mixedDivergence (Φ.kernel h) w) :
    EnergySetting lam h q τ₁ τ₂ (smoothedDensity Φ η h Γ') (smoothedBeta Φ η Bt Lam h Γ')
      (smoothedFlux Φ η Bt Lam h Γ') := by
  have := hD.finite
  have hK : IsCompact ({h} : Set ℝ) := isCompact_singleton
  have hsub : ({h} : Set ℝ) ⊆ Set.Ioi 0 := by simpa using hh
  obtain ⟨C₀, hC₀, hP⟩ := smoothed_package_uniform Φ hη hD hq hK hsub
  obtain ⟨C1, C2, Cfi, hCfi, hk⟩ := exists_kernelConsts (Φ := Φ) hK hsub
  obtain ⟨Cs, hCs0, hCs⟩ := Φ.exists_sup_bound hK hsub
  obtain ⟨B, hB0, hB⟩ := exists_abs_deriv_le hη
  have hfinτ : ∀ τ, IsFiniteMeasure (averagedSlice η τ Γ') := fun τ =>
    isFiniteMeasure_averagedSlice_of_datum hη hD
  have hRle : ∀ τ y, smoothedDensity Φ η h Γ' τ y ≤ Cs := fun τ y => by
    have := hfinτ τ
    calc _ ≤ Cs * (averagedSlice η τ Γ').real Set.univ :=
          smoothDensity_le_of_kernel_le Φ hh (fun z => hCs h rfl z) _ y
      _ ≤ Cs * 1 := mul_le_mul_of_nonneg_left (averagedSlice_real_univ_le_of_datum hη hD) hCs0
      _ = Cs := mul_one _
  refine ⟨hD.lam_pos, hq, hτ, contDiff_smoothedDensity Φ hη hh,
    fun i j => contDiff_smoothedFlux Φ hη hD.marginal hD.measurable hD.abs_apply_le
      hD.lam_nonneg_Lam hD.loewner hh i j,
    fun τ y => smoothDensity_nonneg Φ _ hh y, ⟨Cs, hRle⟩,
    ⟨fun y => B * smoothDensity Φ h (Γ'.map Prod.snd) y,
      (integrable_smoothDensity Φ _ hh).const_mul B,
      fun τ y => abs_deriv_smoothedDensity_le Φ hη hh hB τ y⟩,
    fun τ _ => (hP h rfl τ).pow.1,
    fun i j c => measurable_partial_smoothedBeta Φ hη hD.marginal hD.measurable
      hD.abs_apply_le hD.lam_nonneg_Lam hD.loewner hh i j c,
    ⟨C₀, hC₀, fun τ hτ' => ?_⟩⟩
  by_cases hm : averagedSlice η τ Γ' = 0
  · left
    intro y
    unfold smoothedDensity
    rw [hm]
    exact smoothDensity_zero Φ y
  · right
    have := hfinτ τ
    have hPτ := hP h rfl τ
    have hadm := isAdmissibleCoefficient_of_datum (η := η) (τ := τ) hD
    exact ⟨⟨contDiff_smoothDensity Φ _ hh, smoothDensity_pos Φ _ hh hm,
      fun i j => contDiff_smoothCoefficient_entry Φ _ hD.lam_pos hadm hh hm i j,
      fun i j y => smoothFluxEntry_eq_mul Φ _ hh hm i j y,
      fun y => (smoothCoefficient_loewner Φ _ hD.lam_pos hadm hh y).1,
      fun y => smoothed_equation Φ hη hD hh hδ (hτ₁.trans hτ'.1) (by linarith [hτ'.2]) hfwd
        hcomm y,
      ⟨hPτ.pow.1, hPτ.grad.1, hPτ.hess.1, hPτ.fisher.1, hPτ.fluxGrad.1, hPτ.fluxHess.1,
        hPτ.fluxFisher.1, integrable_powBetaGradSq _ hD.lam_pos hadm hh hm (hk h rfl) hq
          (fun y => hRle τ y)⟩⟩, hPτ.grad.2, hPτ.fluxGrad.2⟩

/-- **The energy inequality for a smoothing datum**: for `1 < q`,
`h > 0`, and `δ < τ₁ < τ₂ < T - δ`, with `ρ`, `β_h` the smoothed density and coefficient and
`|Dρ|²_{M^h} = flowGamma lam h ρ ρ`, `|Dβ|²_{M^h} = coefficientGammaSum lam h β`:
`(q(q-1)/4) ∫∫ ρ^{q-2} |Dρ|²_{M^h} ≤ ∫ ρ(τ₁)^q + (4dq(q-1)/λ²) ∫∫ ρ^q |Dβ|²_{M^h}`, as an
inequality in `[0, ∞]` between iterated lower integrals over `(τ₁, τ₂) × ℝ^{2d}`. -/
theorem energy_inequality_datum (Φ : SmoothingKernelFamily d lam) (hη : IsMollifier δ η)
    (hD : IsSmoothingDatum lam Lam Bt Γ') {h q τ₁ τ₂ T : ℝ} (hh : 0 < h) (hδ : 0 < δ)
    (hq : 1 < q) (hτ : τ₁ < τ₂) (hτ₁ : δ < τ₁) (hτ₂ : τ₂ + δ < T)
    (hfwd : IsForwardMeasure T Bt Γ')
    (hcomm : ∀ w, transportDerivative (Φ.kernel h) w =
      lam * h ^ 2 / 2 * positionLaplacian (Φ.kernel h) w -
        lam * h * mixedDivergence (Φ.kernel h) w) :
    ENNReal.ofReal (q * (q - 1) / 4) *
        ∫⁻ τ in Set.Ioo τ₁ τ₂, ∫⁻ y, ENNReal.ofReal (smoothedDensity Φ η h Γ' τ y ^ (q - 2) *
          flowGamma lam h (smoothedDensity Φ η h Γ' τ) (smoothedDensity Φ η h Γ' τ) y) ≤
      (∫⁻ y, ENNReal.ofReal (smoothedDensity Φ η h Γ' τ₁ y ^ q)) +
        ENNReal.ofReal (4 * d * q * (q - 1) / lam ^ 2) *
          ∫⁻ τ in Set.Ioo τ₁ τ₂, ∫⁻ y, ENNReal.ofReal (smoothedDensity Φ η h Γ' τ y ^ q *
            coefficientGammaSum lam h (smoothedBeta Φ η Bt Lam h Γ' τ) y) :=
  (energySetting_of_datum Φ hη hD hh hδ hq hτ hτ₁ hτ₂ hfwd hcomm).energy_inequality

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
