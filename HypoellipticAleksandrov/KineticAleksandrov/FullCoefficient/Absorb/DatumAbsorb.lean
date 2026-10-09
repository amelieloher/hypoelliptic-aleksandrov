module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Absorb.DatumIneq
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Absorb.CoreReal

/-!
# Absorption for a smoothing datum

The absorption estimate, for the smoothed density of a smoothing datum with
fixed `δ, τ₁, τ₂`: for `1 < q ≤ 4/3`, `2d(q-1) < 1` and `16 d q(q-1) d Λ²/λ² ≤ 1/2`,
`E(ε) ≤ 2 c^{q-1} (1 + 4/(1-θ)) T^{1-θ}` with `θ = 2d(q-1)`, for every `ε > 0` and `τ₂ - τ₁ ≤ T`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ} {δ : ℝ} {η : ℝ → ℝ} {lam Lam : ℝ} (Φ : SmoothingKernelFamily d lam)
  {Bt : ℝ → EvolutionAmbientState d → PDE.Mat d} {Γ' : Measure (ℝ × EvolutionAmbientState d)}
  [IsFiniteMeasure Γ'] {h q τ₁ τ₂ T : ℝ}

omit [IsFiniteMeasure Γ'] in
theorem slice_pow_nonneg (hh : 0 < h) (τ : ℝ) :
    0 ≤ ∫ y, smoothedDensity Φ η h Γ' τ y ^ q :=
  integral_nonneg fun y => Real.rpow_nonneg (smoothDensity_nonneg Φ _ hh y) _

theorem integrable_tau_pow (hη : IsMollifier δ η) (hD : IsSmoothingDatum lam Lam Bt Γ')
    (hh : 0 < h) (hq : 1 < q) :
    Integrable (fun τ => ∫ y, smoothedDensity Φ η h Γ' τ y ^ q)
      (volume.restrict (Set.Ioo τ₁ τ₂)) := by
  refine Integrable.of_bound (C := (Φ.supConst * (h ^ (2 * d))⁻¹) ^ (q - 1))
    ((measurable_smoothedDensity_pow Φ hη hh).stronglyMeasurable.integral_prod_right
      (f := fun τ y => smoothedDensity Φ η h Γ' τ y ^ q)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun τ => ?_)
  have := isFiniteMeasure_averagedSlice_of_datum (τ := τ) hη hD
  rw [Real.norm_eq_abs, abs_of_nonneg (slice_pow_nonneg Φ hh τ)]
  exact (integral_smoothDensity_pow_le Φ (averagedSlice η τ Γ')
    (averagedSlice_real_univ_le_of_datum hη hD) hh hq).2

theorem integrable_tau_powBeta (hη : IsMollifier δ η) (hD : IsSmoothingDatum lam Lam Bt Γ')
    (hh : 0 < h) (hq : 1 < q) :
    Integrable (fun τ => ∫ y, integrandPowBeta Φ h (averagedCoefficient η Bt lam Lam τ Γ')
      (averagedSlice η τ Γ') q y) (volume.restrict (Set.Ioo τ₁ τ₂)) := by
  have hKc : IsCompact ({h} : Set ℝ) := isCompact_singleton
  have hKs : ({h} : Set ℝ) ⊆ Set.Ioi 0 := by simpa using hh
  obtain ⟨C, hC0, hC⟩ := smoothed_package_uniform Φ hη hD hq hKc hKs
  refine Integrable.of_bound (C := C)
    ((measurable_integrandPowBeta Φ hη hD hh hq).stronglyMeasurable.integral_prod_right
      (f := fun τ y => integrandPowBeta Φ h (averagedCoefficient η Bt lam Lam τ Γ')
        (averagedSlice η τ Γ') q y)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun τ => ?_)
  have := isFiniteMeasure_averagedSlice_of_datum (τ := τ) hη hD
  have hnn : 0 ≤ ∫ y, integrandPowBeta Φ h (averagedCoefficient η Bt lam Lam τ Γ')
      (averagedSlice η τ Γ') q y := integral_nonneg fun y => integrandPowBeta_nonneg Φ _ hh y
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  exact (hC h rfl τ).powBeta.2

theorem totalPow_le (hη : IsMollifier δ η) (hD : IsSmoothingDatum lam Lam Bt Γ')
    (hh : 0 < h) (hq : 1 < q) (hτ : τ₁ < τ₂) :
    ∫ τ in Set.Ioo τ₁ τ₂, ∫ y, smoothedDensity Φ η h Γ' τ y ^ q ≤
      (τ₂ - τ₁) * (Φ.supConst ^ (q - 1) * h ^ (-(2 * d * (q - 1)))) := by
  have hc := supConst_nonneg Φ hh
  have hb : ∀ τ, ∫ y, smoothedDensity Φ η h Γ' τ y ^ q ≤
      Φ.supConst ^ (q - 1) * h ^ (-(2 * d * (q - 1))) := fun τ => by
    have := isFiniteMeasure_averagedSlice_of_datum (τ := τ) hη hD
    rw [← supBound_eq Φ hh hc]
    exact (integral_smoothDensity_pow_le Φ (averagedSlice η τ Γ')
      (averagedSlice_real_univ_le_of_datum hη hD) hh hq).2
  calc _ ≤ ∫ τ in Set.Ioo τ₁ τ₂, Φ.supConst ^ (q - 1) * h ^ (-(2 * d * (q - 1))) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun τ => slice_pow_nonneg Φ hh τ)
          (integrable_const _) (Filter.Eventually.of_forall hb)
    _ = _ := by
        rw [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Ioo,
          ENNReal.toReal_ofReal (by linarith)]

theorem totalPowBeta_le (hη : IsMollifier δ η) (hD : IsSmoothingDatum lam Lam Bt Γ')
    (hh : 0 < h) (hq : 1 < q) :
    ∫ τ in Set.Ioo τ₁ τ₂, ∫ y, integrandPowBeta Φ h (averagedCoefficient η Bt lam Lam τ Γ')
        (averagedSlice η τ Γ') q y ≤
      d * Lam ^ 2 * ∫ τ in Set.Ioo τ₁ τ₂, ∫ y, smoothedDensity Φ η h Γ' τ y ^ q := by
  rw [← integral_const_mul]
  refine integral_mono (integrable_tau_powBeta Φ hη hD hh hq)
    ((integrable_tau_pow Φ hη hD hh hq).const_mul _) fun τ => ?_
  have := isFiniteMeasure_averagedSlice_of_datum (τ := τ) hη hD
  rw [← integral_const_mul]
  have hKc : IsCompact ({h} : Set ℝ) := isCompact_singleton
  have hKs : ({h} : Set ℝ) ⊆ Set.Ioi 0 := by simpa using hh
  obtain ⟨C, hC0, hC⟩ := smoothed_package_uniform Φ hη hD hq hKc hKs
  exact integral_mono (hC h rfl τ).powBeta.1 ((hC h rfl τ).pow.1.const_mul _) fun y =>
    integrandPowBeta_le Φ (averagedSlice η τ Γ') hD.lam_pos hD.lam_le
      (isAdmissibleCoefficient_of_datum hD) hh y

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
