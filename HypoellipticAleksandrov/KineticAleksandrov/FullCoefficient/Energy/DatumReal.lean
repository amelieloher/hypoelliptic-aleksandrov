module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Energy.Real
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Energy.Green

/-!
# The energy inequality for real integrals: smoothing datum and Green measure

The energy inequality: for a smoothing datum and for the Green measure the
slice integrals of `ρ^q |Dβ|²` are bounded uniformly in `τ` (by the smoothing estimates), hence all
the
space-time integrals are finite and the energy inequality holds for Bochner integrals.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory
open scoped MatrixOrder

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ} {δ : ℝ} {η : ℝ → ℝ} {lam Lam : ℝ}
  {Bt : ℝ → EvolutionAmbientState d → PDE.Mat d} {Γ' : Measure (ℝ × EvolutionAmbientState d)}

/-- The slice integrals of `ρ^q |Dβ|²` are bounded uniformly in `τ`. -/
theorem betaSq_bound_of_datum (Φ : SmoothingKernelFamily d lam) (hη : IsMollifier δ η)
    (hD : IsSmoothingDatum lam Lam Bt Γ') {h q : ℝ} (hh : 0 < h) (hq : 1 < q) :
    ∃ C' : ℝ, ∀ τ : ℝ, ∫ y, smoothedDensity Φ η h Γ' τ y ^ q *
      coefficientGradNormSq (smoothedBeta Φ η Bt Lam h Γ' τ) y ≤ C' := by
  have := hD.finite
  have hK : IsCompact ({h} : Set ℝ) := isCompact_singleton
  have hsub : ({h} : Set ℝ) ⊆ Set.Ioi 0 := by simpa using hh
  obtain ⟨C1, C2, Cfi, hCfi, hk⟩ := exists_kernelConsts (Φ := Φ) hK hsub
  obtain ⟨Cs, hCs0, hCs⟩ := Φ.exists_sup_bound hK hsub
  have hW : 0 ≤ ∫ z, weight2 Φ h z := integral_nonneg fun z => weight2_nonneg hh z
  refine ⟨Cs ^ (q - 1) * (4 * d ^ 2 * Lam ^ 2 * Cfi) * (1 * ∫ z, weight2 Φ h z), fun τ => ?_⟩
  have hnn : 0 ≤ Cs ^ (q - 1) * (4 * d ^ 2 * Lam ^ 2 * Cfi) * (1 * ∫ z, weight2 Φ h z) := by
    have := Real.rpow_nonneg hCs0 (q - 1)
    positivity
  by_cases hm : averagedSlice η τ Γ' = 0
  · have hz : ∀ y, smoothedDensity Φ η h Γ' τ y ^ q *
        coefficientGradNormSq (smoothedBeta Φ η Bt Lam h Γ' τ) y = 0 := fun y => by
      have : smoothedDensity Φ η h Γ' τ y = 0 := by
        unfold smoothedDensity
        rw [hm]
        exact smoothDensity_zero Φ y
      rw [this, Real.zero_rpow (by linarith), zero_mul]
    simp only [hz, integral_zero]
    exact hnn
  · have := isFiniteMeasure_averagedSlice_of_datum (τ := τ) hη hD
    have hadm := isAdmissibleCoefficient_of_datum (η := η) (τ := τ) hD
    have hRle : ∀ y, smoothDensity Φ h (averagedSlice η τ Γ') y ≤ Cs := fun y =>
      calc _ ≤ Cs * (averagedSlice η τ Γ').real Set.univ :=
            smoothDensity_le_of_kernel_le Φ hh (fun z => hCs h rfl z) _ y
        _ ≤ Cs * 1 := mul_le_mul_of_nonneg_left (averagedSlice_real_univ_le_of_datum hη hD) hCs0
        _ = Cs := mul_one _
    have hb := (integrableBy_powBetaGradSq (Φ := Φ) (averagedSlice η τ Γ') hD.lam_pos hadm hh hm
      (hk h rfl) hq hRle).2
    refine hb.trans ?_
    have hmass := averagedSlice_real_univ_le_of_datum (τ := τ) hη hD
    have h0 : 0 ≤ Cs ^ (q - 1) * (4 * d ^ 2 * Lam ^ 2 * Cfi) := by
      have := Real.rpow_nonneg hCs0 (q - 1)
      positivity
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmass hW) h0

/-- **The energy inequality for a smoothing datum, for real integrals**. -/
theorem energy_inequality_datum_real (Φ : SmoothingKernelFamily d lam) (hη : IsMollifier δ η)
    (hD : IsSmoothingDatum lam Lam Bt Γ') {h q τ₁ τ₂ T : ℝ} (hh : 0 < h) (hδ : 0 < δ)
    (hq : 1 < q) (hτ : τ₁ < τ₂) (hτ₁ : δ < τ₁) (hτ₂ : τ₂ + δ < T)
    (hfwd : IsForwardMeasure T Bt Γ')
    (hcomm : ∀ w, transportDerivative (Φ.kernel h) w =
      lam * h ^ 2 / 2 * positionLaplacian (Φ.kernel h) w -
        lam * h * mixedDivergence (Φ.kernel h) w) :
    Integrable (fun p : ℝ × EvolutionAmbientState d =>
        smoothedDensity Φ η h Γ' p.1 p.2 ^ (q - 2) *
          flowGamma lam h (smoothedDensity Φ η h Γ' p.1) (smoothedDensity Φ η h Γ' p.1) p.2)
      (volume.restrict (Set.Ioo τ₁ τ₂ ×ˢ (Set.univ : Set (EvolutionAmbientState d)))) ∧
    Integrable (fun p : ℝ × EvolutionAmbientState d =>
        smoothedDensity Φ η h Γ' p.1 p.2 ^ q *
          coefficientGammaSum lam h (smoothedBeta Φ η Bt Lam h Γ' p.1) p.2)
      (volume.restrict (Set.Ioo τ₁ τ₂ ×ˢ (Set.univ : Set (EvolutionAmbientState d)))) ∧
    q * (q - 1) / 4 * ∫ p in Set.Ioo τ₁ τ₂ ×ˢ (Set.univ : Set (EvolutionAmbientState d)),
        smoothedDensity Φ η h Γ' p.1 p.2 ^ (q - 2) *
          flowGamma lam h (smoothedDensity Φ η h Γ' p.1) (smoothedDensity Φ η h Γ' p.1) p.2 ≤
      (∫ y, smoothedDensity Φ η h Γ' τ₁ y ^ q) + 4 * d * q * (q - 1) / lam ^ 2 *
        ∫ p in Set.Ioo τ₁ τ₂ ×ˢ (Set.univ : Set (EvolutionAmbientState d)),
          smoothedDensity Φ η h Γ' p.1 p.2 ^ q *
            coefficientGammaSum lam h (smoothedBeta Φ η Bt Lam h Γ' p.1) p.2 := by
  obtain ⟨C', hC'⟩ := betaSq_bound_of_datum (Bt := Bt) (Γ' := Γ') Φ hη hD hh hq
  exact (energySetting_of_datum Φ hη hD hh hδ hq hτ hτ₁ hτ₂ hfwd hcomm).energy_inequality_real
    (fun τ _ => hC' τ)

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
