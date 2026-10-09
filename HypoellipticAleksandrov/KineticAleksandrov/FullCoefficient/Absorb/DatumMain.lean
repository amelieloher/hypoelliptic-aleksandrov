module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Absorb.DatumAbsorb

/-!
# Proposition the absorption estimate for a smoothing datum
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ} {δ : ℝ} {η : ℝ → ℝ} {lam Lam : ℝ} (Φ : SmoothingKernelFamily d lam)
  {Bt : ℝ → EvolutionAmbientState d → PDE.Mat d} {Γ' : Measure (ℝ × EvolutionAmbientState d)}
  [IsFiniteMeasure Γ'] {q τ₁ τ₂ T ε : ℝ}

/-- **The absorption estimate** for the smoothed density of a smoothing datum at fixed
`δ, τ₁, τ₂`: `E(ε) ≤ 2 c^{q-1} (1 + 4/(1-θ)) T^{1-θ}` with `θ = 2d(q-1)`. -/
theorem absorb_datum (hη : IsMollifier δ η) (hD : IsSmoothingDatum lam Lam Bt Γ')
    (hδ : 0 < δ) (hq : 1 < q) (hq2 : q ≤ 4 / 3) (hθ : 2 * d * (q - 1) < 1)
    (hκ : 16 * d * q * (q - 1) / lam ^ 2 * (d * Lam ^ 2) ≤ 1 / 2)
    (hτ : τ₁ < τ₂) (hτ₁ : δ < τ₁) (hτ₂ : τ₂ + δ < T) (hTτ : τ₂ - τ₁ ≤ T)
    (hfwd : IsForwardMeasure T Bt Γ')
    (hcomm : ∀ h : ℝ, 0 < h → ∀ w, transportDerivative (Φ.kernel h) w =
      lam * h ^ 2 / 2 * positionLaplacian (Φ.kernel h) w -
        lam * h * mixedDivergence (Φ.kernel h) w)
    (hε : 0 < ε) :
    ∫ τ in Set.Ioo τ₁ τ₂, ∫ y, smoothedDensity Φ η ε Γ' τ y ^ q ≤
      2 * Φ.supConst ^ (q - 1) * (1 + 4 / (1 - 2 * d * (q - 1))) *
        T ^ (1 - 2 * d * (q - 1)) := by
  have hT0 : 0 < T := by linarith
  have hc := supConst_nonneg Φ hε
  have ha : 0 ≤ Φ.supConst ^ (q - 1) := Real.rpow_nonneg hc _
  set θ : ℝ := 2 * d * (q - 1) with hθdef
  have hθ0 : 0 ≤ θ := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have : 0 ≤ q - 1 := by linarith
    positivity
  have h1θ : 0 < 1 - θ := by linarith
  set a : ℝ := Φ.supConst ^ (q - 1) with hadef
  have hTpow : 0 ≤ T ^ (1 - θ) := Real.rpow_nonneg hT0.le _
  have hTT : T * T ^ (-θ) = T ^ (1 - θ) := by
    rw [← Real.rpow_one_add' hT0.le (by intro h0; linarith)]; ring_nf
  have hET : ∫ τ in Set.Ioo τ₁ τ₂, ∫ y, smoothedDensity Φ η T Γ' τ y ^ q ≤ a * T ^ (1 - θ) := by
    refine (totalPow_le Φ hη hD hT0 hq hτ).trans ?_
    calc (τ₂ - τ₁) * (a * T ^ (-θ)) ≤ T * (a * T ^ (-θ)) :=
          mul_le_mul_of_nonneg_right hTτ (by positivity)
      _ = a * T ^ (1 - θ) := by rw [← hTT]; ring
  have hC : 0 ≤ 4 / (1 - θ) := by positivity
  by_cases hεT : T ≤ ε
  · -- trivial case
    refine (totalPow_le Φ hη hD hε hq hτ).trans ?_
    have hle : ε ^ (-θ) ≤ T ^ (-θ) := Real.rpow_le_rpow_of_nonpos hT0 hεT (by linarith)
    calc (τ₂ - τ₁) * (a * ε ^ (-θ)) ≤ T * (a * T ^ (-θ)) :=
          mul_le_mul hTτ (mul_le_mul_of_nonneg_left hle ha) (by positivity) hT0.le
      _ = a * T ^ (1 - θ) := by rw [← hTT]; ring
      _ ≤ _ := by nlinarith [mul_nonneg ha hTpow, mul_nonneg (mul_nonneg ha hTpow) hC]
  · rw [not_le] at hεT
    set κ : ℝ := 16 * d * q * (q - 1) / lam ^ 2 with hκdef
    have hmain := absorb_core (E := fun s => ∫ τ in Set.Ioo τ₁ τ₂, ∫ y,
        smoothedDensity Φ η s Γ' τ y ^ q)
      (Fx := fun s => ∫ τ in Set.Ioo τ₁ τ₂, ∫ y, integrandPowBeta Φ s
        (averagedCoefficient η Bt lam Lam τ Γ') (averagedSlice η τ Γ') q y)
      (E' := fun s => ∫ τ in Set.Ioo τ₁ τ₂, ∫ y, integrandPowDeriv Φ s q (averagedSlice η τ Γ') y)
      (F' := fun s => ∫ τ in Set.Ioo τ₁ τ₂, ∫ y, integrandPowBetaDeriv Φ s
        (averagedCoefficient η Bt lam Lam τ Γ') (averagedSlice η τ Γ') q y)
      (a := a) (θ := θ) (κ := κ) (ε := ε) (S := T) hε hεT.le hθ
      (fun h hh => (hasDerivAt_totalPow Φ hη hD (lt_of_lt_of_le hε hh.1) hq).2)
      (fun h hh => (hasDerivAt_totalPowBeta Φ hη hD (lt_of_lt_of_le hε hh.1) hq).2)
      (fun h hh => by
        have hh0 : 0 < h := lt_of_lt_of_le hε hh.1
        have := datum_ineq Φ hη hD hh0 hδ hq hq2 hτ hτ₁ hτ₂ hfwd (hcomm h hh0)
        linarith)
    have hFε := totalPowBeta_le Φ (τ₁ := τ₁) (τ₂ := τ₂) hη hD hε hq
    have hFT : 0 ≤ ∫ τ in Set.Ioo τ₁ τ₂, ∫ y, integrandPowBeta Φ T
        (averagedCoefficient η Bt lam Lam τ Γ') (averagedSlice η τ Γ') q y :=
      integral_nonneg fun τ => integral_nonneg fun y => by
        have := isFiniteMeasure_averagedSlice_of_datum (τ := τ) hη hD
        exact integrandPowBeta_nonneg Φ _ hT0 y
    have hκ0 : 0 ≤ κ := by
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      have : 0 ≤ q - 1 := by linarith
      positivity
    have hεpow : 0 ≤ ε ^ (1 - θ) := Real.rpow_nonneg hε.le _
    set Eε := ∫ τ in Set.Ioo τ₁ τ₂, ∫ y, smoothedDensity Φ η ε Γ' τ y ^ q with hEε
    have hEε0 : 0 ≤ Eε := integral_nonneg fun τ => slice_pow_nonneg Φ hε τ
    have h2 : κ * (d * Lam ^ 2 * Eε) ≤ 1 / 2 * Eε := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hκ hEε0
    have h3 := mul_le_mul_of_nonneg_left hFε hκ0
    have h4 : 0 ≤ 4 * a / (1 - θ) * ε ^ (1 - θ) := by positivity
    have h5 : 4 * a / (1 - θ) * (T ^ (1 - θ) - ε ^ (1 - θ)) ≤ 4 * a / (1 - θ) * T ^ (1 - θ) := by
      nlinarith
    have h6 : 4 * a / (1 - θ) * T ^ (1 - θ) = a * T ^ (1 - θ) * (4 / (1 - θ)) := by ring
    have h7 : 0 ≤ κ * ∫ τ in Set.Ioo τ₁ τ₂, ∫ y, integrandPowBeta Φ T
        (averagedCoefficient η Bt lam Lam τ Γ') (averagedSlice η τ Γ') q y := mul_nonneg hκ0 hFT
    have : Eε ≤ 2 * (a * T ^ (1 - θ) + a * T ^ (1 - θ) * (4 / (1 - θ))) := by
      nlinarith
    calc Eε ≤ _ := this
      _ = _ := by ring

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
