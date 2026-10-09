module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Absorb.SliceBounds
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Energy.DatumReal

/-!
# The differential inequality for a smoothing datum

The time-integrated identities combined with the energy inequality: for `0 < h`,
`-E'(h) ≤ 4 c^{q-1} h^{-2d(q-1)} - κ F'(h)` with `κ = 16 d q (q-1)/λ²`, where `E'` and `F'` are
the `τ`-integrals of the slice derivatives (the derivatives of `E` and `F` by `TauDeriv`).
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

theorem integral_Ioo_univ_eq {d : ℕ} {a b : ℝ} {f : ℝ × EvolutionAmbientState d → ℝ}
    (hf : Integrable f (volume.restrict
      (Set.Ioo a b ×ˢ (Set.univ : Set (EvolutionAmbientState d))))) :
    ∫ p in Set.Ioo a b ×ˢ (Set.univ : Set (EvolutionAmbientState d)), f p =
      ∫ τ in Set.Ioo a b, ∫ y, f (τ, y) := by
  have e : (volume : Measure (ℝ × EvolutionAmbientState d)).restrict
      (Set.Ioo a b ×ˢ (Set.univ : Set (EvolutionAmbientState d))) =
      (volume.restrict (Set.Ioo a b)).prod (volume : Measure (EvolutionAmbientState d)) := by
    rw [Measure.volume_eq_prod,
      ← Measure.restrict_univ (μ := (volume : Measure (EvolutionAmbientState d))),
      Measure.prod_restrict, Measure.restrict_univ]
  rw [e] at hf ⊢
  exact integral_prod f hf

variable {d : ℕ} {δ : ℝ} {η : ℝ → ℝ} {lam Lam : ℝ} (Φ : SmoothingKernelFamily d lam)
  {Bt : ℝ → EvolutionAmbientState d → PDE.Mat d} {Γ' : Measure (ℝ × EvolutionAmbientState d)}
  [IsFiniteMeasure Γ'] {h q τ₁ τ₂ T : ℝ}

theorem datum_ineq (hη : IsMollifier δ η) (hD : IsSmoothingDatum lam Lam Bt Γ')
    (hh : 0 < h) (hδ : 0 < δ) (hq : 1 < q) (hq2 : q ≤ 4 / 3) (hτ : τ₁ < τ₂) (hτ₁ : δ < τ₁)
    (hτ₂ : τ₂ + δ < T) (hfwd : IsForwardMeasure T Bt Γ')
    (hcomm : ∀ w, transportDerivative (Φ.kernel h) w =
      lam * h ^ 2 / 2 * positionLaplacian (Φ.kernel h) w -
        lam * h * mixedDivergence (Φ.kernel h) w) :
    -(∫ τ in Set.Ioo τ₁ τ₂, ∫ y, integrandPowDeriv Φ h q (averagedSlice η τ Γ') y) ≤
      4 * (Φ.supConst ^ (q - 1) * h ^ (-(2 * d * (q - 1)))) -
        (16 * d * q * (q - 1) / lam ^ 2) *
          ∫ τ in Set.Ioo τ₁ τ₂, ∫ y, integrandPowBetaDeriv Φ h
            (averagedCoefficient η Bt lam Lam τ Γ') (averagedSlice η τ Γ') q y := by
  obtain ⟨hZi, hVi, hen⟩ := energy_inequality_datum_real Φ hη hD hh hδ hq hτ hτ₁ hτ₂ hfwd hcomm
  have hKc : IsCompact ({h} : Set ℝ) := isCompact_singleton
  have hKs : ({h} : Set ℝ) ⊆ Set.Ioi 0 := by simpa using hh
  obtain ⟨C, hC0, hC⟩ := smoothed_package_uniform Φ hη hD hq hKc hKs
  have hP : ∀ τ, PackageIntegrable Φ h (averagedCoefficient η Bt lam Lam τ Γ')
      (averagedSlice η τ Γ') q C := fun τ => hC h rfl τ
  have hfin : ∀ τ, IsFiniteMeasure (averagedSlice η τ Γ') := fun τ =>
    isFiniteMeasure_averagedSlice_of_datum hη hD
  set μ : Measure ℝ := volume.restrict (Set.Ioo τ₁ τ₂) with hμ
  -- slice identities
  have hsl : ∀ τ, ∫ y, integrandPowDeriv Φ h q (averagedSlice η τ Γ') y =
      -(q * (q - 1)) * ∫ y, smoothedDensity Φ η h Γ' τ y ^ (q - 2) *
        flowGamma lam h (smoothedDensity Φ η h Γ' τ) (smoothedDensity Φ η h Γ' τ) y := fun τ =>
    (slice_pow Φ (averagedSlice η τ Γ') hD.lam_pos hD.lam_le (isAdmissibleCoefficient_of_datum hD)
      hh hq (hP τ)).2.2
  have hE : ∫ τ in Set.Ioo τ₁ τ₂, ∫ y, integrandPowDeriv Φ h q (averagedSlice η τ Γ') y =
      -(q * (q - 1)) * ∫ p in Set.Ioo τ₁ τ₂ ×ˢ (Set.univ : Set (EvolutionAmbientState d)),
        smoothedDensity Φ η h Γ' p.1 p.2 ^ (q - 2) *
          flowGamma lam h (smoothedDensity Φ η h Γ' p.1) (smoothedDensity Φ η h Γ' p.1) p.2 := by
    rw [integral_Ioo_univ_eq hZi]
    simp only [hsl]
    rw [integral_const_mul]
  -- the coefficient inequality
  have hVt : ∫ p in Set.Ioo τ₁ τ₂ ×ˢ (Set.univ : Set (EvolutionAmbientState d)),
      smoothedDensity Φ η h Γ' p.1 p.2 ^ q *
        coefficientGammaSum lam h (smoothedBeta Φ η Bt Lam h Γ' p.1) p.2 ≤
      -∫ τ in Set.Ioo τ₁ τ₂, ∫ y, integrandPowBetaDeriv Φ h
          (averagedCoefficient η Bt lam Lam τ Γ') (averagedSlice η τ Γ') q y := by
    obtain ⟨hGi, -⟩ := hasDerivAt_totalPowBeta Φ (τ₁ := τ₁) (τ₂ := τ₂) hη hD hh hq
    rw [integral_Ioo_univ_eq hVi, ← integral_neg]
    have hint : Integrable (fun τ => ∫ y, smoothedDensity Φ η h Γ' τ y ^ q *
        coefficientGammaSum lam h (smoothedBeta Φ η Bt Lam h Γ' τ) y) μ := by
      have := hVi
      rw [Measure.volume_eq_prod, ← Measure.restrict_univ
        (μ := (volume : Measure (EvolutionAmbientState d))), ← Measure.prod_restrict,
        Measure.restrict_univ] at this
      simpa using this.integral_prod_left
    refine integral_mono hint hGi.neg fun τ => ?_
    have := slice_powBeta Φ (averagedSlice η τ Γ') hD.lam_pos hD.lam_le
      (isAdmissibleCoefficient_of_datum hD) hh hq hq2 (hP τ)
    exact this.2.2
  -- the initial slice
  have hI : ∫ y, smoothedDensity Φ η h Γ' τ₁ y ^ q ≤
      Φ.supConst ^ (q - 1) * h ^ (-(2 * d * (q - 1))) := by
    rw [← supBound_eq Φ hh (supConst_nonneg Φ hh)]
    exact (integral_smoothDensity_pow_le Φ (averagedSlice η τ₁ Γ')
      (averagedSlice_real_univ_le_of_datum hη hD) hh hq).2
  have hqq : 0 < q * (q - 1) := by nlinarith
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  rw [hE]
  have hk : 4 * d * q * (q - 1) / lam ^ 2 * 4 = 16 * d * q * (q - 1) / lam ^ 2 := by ring
  have hk0 : 0 ≤ 4 * d * q * (q - 1) / lam ^ 2 := by
    have : 0 ≤ q - 1 := by linarith
    positivity
  have hmul := mul_le_mul_of_nonneg_left hVt hk0
  have h1 := le_trans hen (add_le_add hI hmul)
  rw [← hk]
  linarith

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
