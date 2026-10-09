module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.Package

/-!
# Proof of the integrability list of the smoothing estimates for fixed `h`, `m`, `F`

For `m ≠ 0` each of the ten integrands is continuous, nonnegative and bounded by
`pkgCoefSum * smoothWeight2`, so Tonelli (`integrable_of_le_smoothWeight2`) applies. For `m = 0`
all integrands vanish.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ} {lam Lam : ℝ} {Φ : SmoothingKernelFamily d lam} {h : ℝ}
  {F : EvolutionAmbientState d → PDE.Mat d} {m : Measure (EvolutionAmbientState d)} {q : ℝ}

theorem le_coefSum_mul {T Rq S c Sig : ℝ} (hT : T ≤ Rq * (c * S)) (hc : c ≤ Sig) (hRq : 0 ≤ Rq)
    (hS : 0 ≤ S) : T ≤ (Rq * Sig) * S := by
  refine hT.trans ?_
  have : c * S ≤ Sig * S := mul_le_mul_of_nonneg_right hc hS
  nlinarith [mul_le_mul_of_nonneg_left this hRq]

theorem packageIntegrable_of_ne_zero [IsFiniteMeasure m] {C1 C2 Cfi R : ℝ} (hlam : 0 < lam)
    (hLam' : lam ≤ Lam) (hF : IsAdmissibleCoefficient lam Lam F) (hh : 0 < h) (hm : m ≠ 0)
    (hk : KernelConsts Φ h C1 C2 Cfi) (hq : 1 < q) (hCfi : 0 ≤ Cfi)
    (hR : ∀ y, smoothDensity Φ h m y ≤ R) :
    PackageIntegrable Φ h F m q
      (pkgCoefSum d Lam q C1 C2 Cfi R * (m.real Set.univ * ∫ z, weight2 Φ h z)) := by
  have hLam : 0 ≤ Lam := (hlam.trans_le hLam').le
  have hr0 : ∀ y, 0 < smoothDensity Φ h m y := smoothDensity_pos Φ m hh hm
  have hRpos : 0 < R := (hr0 0).trans_le (hR 0)
  have hRq : 0 ≤ R ^ (q - 1) := Real.rpow_nonneg hRpos.le _
  have hrc : Continuous (smoothDensity Φ h m) := continuous_smoothDensity Φ m hh
  have hrd : ContDiff ℝ (⊤ : ℕ∞) (smoothDensity Φ h m) := contDiff_smoothDensity Φ m hh
  have hpow : ∀ e : ℝ, Continuous fun y => smoothDensity Φ h m y ^ e := fun e =>
    hrc.rpow_const fun y => Or.inl (hr0 y).ne'
  have hβ : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun y => smoothCoefficient Φ h F m y i j) :=
    fun i j => contDiff_smoothCoefficient_entry Φ m hlam hF hh hm i j
  have hJ : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun y => smoothFlux Φ h F m y i j) :=
    fun i j => contDiff_smoothFluxEntry Φ m hlam hF hh i j
  have hfrob : Continuous (fun y => frobeniusSq (smoothCoefficient Φ h F m y)) :=
    continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => (hβ i j).continuous.pow 2
  have hS := smoothWeight2_nonneg (Φ := Φ) m hh
  have hr := fun y => (hr0 y).le
  have hCfi' := hCfi
  have n1 : ∀ y, 0 ≤ smoothDensity Φ h m y ^ q := fun y => Real.rpow_nonneg (hr y) _
  have hsig : ∀ t : ℝ, 0 ≤ t → t ≤ t := fun _ _ => le_rfl
  -- the coefficient terms are nonnegative
  have c1 : 0 ≤ d * Lam ^ 2 := by positivity
  have c2 : 0 ≤ (2 * (d : ℝ) + 1) * |C1| := by positivity
  have c3 : 0 ≤ ((2 * (d : ℝ)) ^ 2 + 1) * |C2| := by positivity
  have c4 : 0 ≤ (1 + 4 * (d : ℝ) ^ 2 * Lam ^ 2 * Cfi) / 2 := by positivity
  have c5 : 0 ≤ ((d : ℝ) ^ 2 * (2 * d) + 1) * Lam * |C1| := by positivity
  have c6 : 0 ≤ ((d : ℝ) ^ 2 * (2 * d) ^ 2 + 1) * Lam * |C2| := by positivity
  have c7 : 0 ≤ (d : ℝ) ^ 2 * Lam ^ 2 * Cfi := by positivity
  have c8 : 0 ≤ 2 * (d : ℝ) * Lam * Cfi := by positivity
  set Sig : ℝ := 1 + d * Lam ^ 2 + (2 * d + 1) * |C1| + ((2 * d) ^ 2 + 1) * |C2| + Cfi +
    (1 + 4 * d ^ 2 * Lam ^ 2 * Cfi) / 2 + (d ^ 2 * (2 * d) + 1) * Lam * |C1| +
    (d ^ 2 * (2 * d) ^ 2 + 1) * Lam * |C2| + d ^ 2 * Lam ^ 2 * Cfi + 2 * d * Lam * Cfi with hSig
  have hfin : ∀ {T : EvolutionAmbientState d → ℝ} {c : ℝ}, Continuous T → (∀ y, 0 ≤ T y) →
      (∀ y, T y ≤ R ^ (q - 1) * (c * smoothWeight2 Φ h m y)) → c ≤ Sig →
      IntegrableBy T (pkgCoefSum d Lam q C1 C2 Cfi R * (m.real Set.univ * ∫ z, weight2 Φ h z)) :=
    fun hTc hT0 hTb hc =>
      integrable_of_le_smoothWeight2 hh hTc hT0 fun y =>
        le_coefSum_mul (hTb y) hc hRq (hS y)
  have e1 : ∀ y, smoothDensity Φ h m y ^ q ≤
      R ^ (q - 1) * (1 * smoothWeight2 Φ h m y) := fun y => by
    simpa using target_rpow_le m hh hm hq hR y
  refine ⟨hfin (c := 1) (hpow q) n1 e1 (by nlinarith), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine hfin (c := d * Lam ^ 2) ((hpow q).mul hfrob) (fun y => mul_nonneg (n1 y)
      (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)) (fun y => ?_)
      (by nlinarith)
    have := target_rpow_frobenius_le m hlam hLam' hF hh hm hq hR y
    calc _ ≤ _ := this
      _ = _ := by ring
  · refine hfin (c := (2 * d + 1) * |C1|) ?_ ?_ (fun y => ?_) (by linarith)
    · exact (hpow (q - 1)).mul (continuous_gradNorm hrd)
    · exact fun y => mul_nonneg (Real.rpow_nonneg (hr y) _) (Real.sqrt_nonneg _)
    · have := target_gradNorm_le m hh hm hk hq hR y
      calc _ ≤ _ := this
        _ = _ := by ring
  · refine hfin (c := ((2 * d) ^ 2 + 1) * |C2|) ?_ ?_ (fun y => ?_) (by linarith)
    · exact (hpow (q - 1)).mul (continuous_hessNorm hrd)
    · exact fun y => mul_nonneg (Real.rpow_nonneg (hr y) _) (Real.sqrt_nonneg _)
    · have := target_hessNorm_le m hh hm hk hq hR y
      calc _ ≤ _ := this
        _ = _ := by ring
  · refine hfin (c := Cfi) ?_ ?_ (fun y => ?_) (by linarith)
    · exact (hpow (q - 2)).mul (continuous_gradNormSq hrd)
    · exact fun y => mul_nonneg (Real.rpow_nonneg (hr y) _) (gradNormSq_nonneg _ _)
    · exact target_fisher_le m hh hm hk hq hR y
  · refine hfin (c := (1 + 4 * d ^ 2 * Lam ^ 2 * Cfi) / 2) ?_ ?_ (fun y => ?_) (by linarith)
    · exact (hpow q).mul (continuous_coefficientGradNormSq hβ).sqrt
    · exact fun y => mul_nonneg (n1 y) (Real.sqrt_nonneg _)
    · exact target_coefficientGradNorm_le m hlam hF hh hm hk hq hR y
  · refine hfin (c := (d ^ 2 * (2 * d) + 1) * Lam * |C1|) ?_ ?_ (fun y => ?_) (by linarith)
    · exact (hpow (q - 1)).mul (continuous_coefficientGradNormSq hJ).sqrt
    · exact fun y => mul_nonneg (Real.rpow_nonneg (hr y) _) (Real.sqrt_nonneg _)
    · have := target_fluxGradNorm_le m hlam hLam' hF hh hm hk hq hR y
      calc _ ≤ _ := this
        _ = _ := by ring
  · refine hfin (c := (d ^ 2 * (2 * d) ^ 2 + 1) * Lam * |C2|) ?_ ?_ (fun y => ?_) (by linarith)
    · exact (hpow (q - 1)).mul (continuous_coefficientHessNormSq hJ).sqrt
    · exact fun y => mul_nonneg (Real.rpow_nonneg (hr y) _) (Real.sqrt_nonneg _)
    · have := target_fluxHessNorm_le m hlam hLam' hF hh hm hk hq hR y
      calc _ ≤ _ := this
        _ = _ := by ring
  · refine hfin (c := d ^ 2 * Lam ^ 2 * Cfi) ?_ ?_ (fun y => ?_) (by linarith)
    · exact (hpow (q - 2)).mul (continuous_coefficientGradNormSq hJ)
    · exact fun y => mul_nonneg (Real.rpow_nonneg (hr y) _) (coefficientGradNormSq_nonneg _ _)
    · exact target_fluxFisher_le m hlam hF hh hm hk hq hR y
  · refine hfin (c := 2 * d * Lam * Cfi) ?_ ?_ (fun y => ?_) (by linarith)
    · exact ((hpow (q - 1)).mul (continuous_gradNorm hrd)).mul
        (continuous_coefficientGradNormSq hβ).sqrt
    · exact fun y => mul_nonneg (mul_nonneg (Real.rpow_nonneg (hr y) _) (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _)
    · exact target_mixed_le m hlam hLam' hF hh hm hk hq hR y

theorem coordPartial_const (c : Fin d ⊕ Fin d) (a : ℝ) :
    coordPartial c (fun _ : EvolutionAmbientState d => a) = fun _ => 0 := by
  funext y; simp [coordPartial]

theorem gradNormSq_const (a : ℝ) (y : EvolutionAmbientState d) :
    gradNormSq (fun _ : EvolutionAmbientState d => a) y = 0 := by
  simp [gradNormSq, coordPartial_const]

theorem hessNormSq_const (a : ℝ) (y : EvolutionAmbientState d) :
    hessNormSq (fun _ : EvolutionAmbientState d => a) y = 0 := by
  simp [hessNormSq, coordPartial_const]

/-- For `m = 0` all ten integrands vanish. -/
theorem packageIntegrable_zero (hq : 1 < q) {C : ℝ} (hC : 0 ≤ C) :
    PackageIntegrable Φ h F (0 : Measure (EvolutionAmbientState d)) q C := by
  have hr0 : smoothDensity Φ h (0 : Measure (EvolutionAmbientState d)) = fun _ => 0 :=
    funext (smoothDensity_zero Φ)
  have hJ0 : ∀ i j : Fin d, (fun y => smoothFlux Φ h F (0 : Measure (EvolutionAmbientState d))
      y i j) = fun _ => 0 := fun i j => by
    funext y; simp [smoothFlux, smoothFluxEntry]
  have hβ0 : ∀ i j : Fin d, (fun y => smoothCoefficient Φ h F
      (0 : Measure (EvolutionAmbientState d)) y i j) = fun _ => lam * (1 : PDE.Mat d) i j := by
    intro i j; funext y; simp [smoothCoefficient]
  have hq0 : q ≠ 0 := by linarith
  have hq1 : q - 1 ≠ 0 := by linarith
  have hz : ∀ T : EvolutionAmbientState d → ℝ, (∀ y, T y = 0) → IntegrableBy T C := fun T hT => by
    have : T = fun _ => 0 := funext hT
    subst this
    exact ⟨integrable_zero _ _ _, by simpa using hC⟩
  have gJ : ∀ y, coefficientGradNormSq (smoothFlux Φ h F (0 : Measure (EvolutionAmbientState d)))
      y = 0 := fun y => by simp [coefficientGradNormSq, hJ0, gradNormSq_const]
  have gβ : ∀ y, coefficientGradNormSq (smoothCoefficient Φ h F
      (0 : Measure (EvolutionAmbientState d))) y = 0 := fun y => by
    simp [coefficientGradNormSq, hβ0, gradNormSq_const]
  have hJ2 : ∀ y, coefficientHessNormSq (smoothFlux Φ h F (0 : Measure (EvolutionAmbientState d)))
      y = 0 := fun y => by simp [coefficientHessNormSq, hJ0, hessNormSq_const]
  refine ⟨hz _ fun y => ?_, hz _ fun y => ?_, hz _ fun y => ?_, hz _ fun y => ?_,
    hz _ fun y => ?_, hz _ fun y => ?_, hz _ fun y => ?_, hz _ fun y => ?_, hz _ fun y => ?_,
    hz _ fun y => ?_⟩
  · simp [integrandPow, smoothDensity_zero, Real.zero_rpow hq0]
  · simp [integrandPowBeta, smoothDensity_zero, Real.zero_rpow hq0]
  · simp [integrandGrad, smoothDensity_zero, Real.zero_rpow hq1]
  · simp [integrandHess, smoothDensity_zero, Real.zero_rpow hq1]
  · simp [integrandFisher, hr0, gradNormSq_const]
  · simp [integrandBetaGrad, smoothDensity_zero, Real.zero_rpow hq0]
  · simp [integrandFluxGrad, smoothDensity_zero, Real.zero_rpow hq1]
  · simp [integrandFluxHess, smoothDensity_zero, Real.zero_rpow hq1]
  · simp [integrandFluxFisher, gJ]
  · simp [integrandMixed, smoothDensity_zero, Real.zero_rpow hq1]

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
