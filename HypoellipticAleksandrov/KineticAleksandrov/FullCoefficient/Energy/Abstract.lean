module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Energy.Integrated
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Energy.Limit
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Energy.Cutoff

/-!
# The energy inequality, abstract form

For `1 < q`, a setting `EnergySetting` on `(τ₁, τ₂)` at smoothing `h`:
`(q(q-1)/4) ∫∫ ρ^{q-2} |Dρ|²_{M^h} ≤ ∫ ρ(τ₁)^q + (4dq(q-1)/λ²) ∫∫ ρ^q |Dβ|²_{M^h}`,
as an inequality in `[0, ∞]` between iterated lower integrals. The cut-off is removed by Fatou.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory Filter Topology

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ} {lam h q τ₁ τ₂ : ℝ} {ρ : ℝ → EvolutionAmbientState d → ℝ}
  {β J : ℝ → EvolutionAmbientState d → PDE.Mat d}

namespace EnergySetting

variable (S : EnergySetting lam h q τ₁ τ₂ ρ β J)

include S

/-- **The energy inequality**: iterated lower integrals over
`(τ₁, τ₂) × ℝ^{2d}`. -/
theorem energy_inequality :
    ENNReal.ofReal (q * (q - 1) / 4) *
        ∫⁻ τ in Set.Ioo τ₁ τ₂, ∫⁻ y,
          ENNReal.ofReal (ρ τ y ^ (q - 2) * flowGamma lam h (ρ τ) (ρ τ) y) ≤
      (∫⁻ y, ENNReal.ofReal (ρ τ₁ y ^ q)) +
        ENNReal.ofReal (4 * d * q * (q - 1) / lam ^ 2) *
          ∫⁻ τ in Set.Ioo τ₁ τ₂, ∫⁻ y,
            ENNReal.ofReal (ρ τ y ^ q * coefficientGammaSum lam h (β τ) y) := by
  have hq := S.one_lt
  have hlam := S.lam_pos
  have h12 := S.lt
  set Y : ENNReal := ∫⁻ τ in Set.Ioo τ₁ τ₂, ∫⁻ y,
    ENNReal.ofReal (ρ τ y ^ q * coefficientGammaSum lam h (β τ) y) with hY
  set L : ENNReal := ∫⁻ y, ENNReal.ofReal (ρ τ₁ y ^ q) with hL
  have hq0 : 0 < q := by linarith
  have hq1 : 0 < q - 1 := by linarith
  have hc₂nn : 0 ≤ 4 * (d : ℝ) * q * (q - 1) / lam ^ 2 := by positivity
  by_cases hYtop : Y = ⊤
  · -- the right-hand side is infinite unless `d = 0`, where `Y = 0`
    have hd : d ≠ 0 := by
      rintro rfl
      have : Y = 0 := by
        rw [hY]
        simp [coefficientGammaSum]
      rw [hYtop] at this
      exact ENNReal.top_ne_zero this
    have hc₂pos : 0 < 4 * (d : ℝ) * q * (q - 1) / lam ^ 2 := by
      have : (0 : ℝ) < d := Nat.cast_pos.2 (Nat.pos_of_ne_zero hd)
      positivity
    rw [hYtop, ENNReal.mul_top (ENNReal.ofReal_pos.2 hc₂pos).ne', add_top]
    exact le_top
  · have hYlt : Y < ⊤ := lt_top_iff_ne_top.2 hYtop
    obtain ⟨C, hC0, hC⟩ := S.slices
    set b := cutoffBump d with hb
    obtain ⟨M, hM0, hM⟩ := exists_fderiv_bound b
    set ζ : ℕ → EvolutionAmbientState d → ℝ := fun n => velocityCutoff b ((n : ℝ) + 1) with hζ
    have Zn : ∀ n : ℕ, CutoffData (b.rOut * ((n : ℝ) + 1)) (M / ((n : ℝ) + 1)) (ζ n) :=
      fun n => by
      have hR : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      exact ⟨contDiff_velocityCutoff b _, velocityCutoff_nonneg b _, velocityCutoff_le_one b _,
        coordPartial_velocityCutoff_inr b _, fun i y => abs_velocityCutoff_mul_le b _ hR i y,
        fun i y => abs_coordPartial_velocityCutoff_le b hM hR i y, div_nonneg hM0 hR.le⟩
    have hζm : ∀ n, Measurable (ζ n) := fun n =>
      (contDiff_velocityCutoff b _).continuous.measurable
    have hFB_le : ∀ n (p : ℝ × EvolutionAmbientState d),
        ζ n p.2 * (ρ p.1 p.2 ^ q * coefficientGammaSum lam h (β p.1) p.2) ≤
          ρ p.1 p.2 ^ q * coefficientGammaSum lam h (β p.1) p.2 := fun n p =>
      mul_le_of_le_one_left (S.FB_nonneg p) (velocityCutoff_le_one b _ _)
    have hBint : ∀ n : ℕ, IntegrableOn (energyB lam h q ρ β (ζ n)) (Set.Ioo τ₁ τ₂) := fun n => by
      have hmeas : Measurable fun p : ℝ × EvolutionAmbientState d =>
          ζ n p.2 * (ρ p.1 p.2 ^ q * coefficientGammaSum lam h (β p.1) p.2) :=
        ((hζm n).comp measurable_snd).mul S.measurable_FB
      have hprod : Integrable (fun p : ℝ × EvolutionAmbientState d =>
          ζ n p.2 * (ρ p.1 p.2 ^ q * coefficientGammaSum lam h (β p.1) p.2))
          ((volume.restrict (Set.Ioo τ₁ τ₂)).prod volume) := by
        refine ⟨hmeas.aestronglyMeasurable, ?_⟩
        have : ∫⁻ p, ‖ζ n p.2 * (ρ p.1 p.2 ^ q * coefficientGammaSum lam h (β p.1) p.2)‖ₑ
            ∂((volume.restrict (Set.Ioo τ₁ τ₂)).prod volume) ≤ Y := by
          rw [lintegral_prod _ hmeas.enorm.aemeasurable]
          refine lintegral_mono fun τ => lintegral_mono fun y => ?_
          rw [Real.enorm_eq_ofReal (mul_nonneg (velocityCutoff_nonneg b _ _) (S.FB_nonneg (τ, y)))]
          exact ENNReal.ofReal_le_ofReal (hFB_le n (τ, y))
        exact lt_of_le_of_lt this hYlt
      exact hprod.integral_prod_left
    have hXA : ∀ n, ∫⁻ τ in Set.Ioo τ₁ τ₂, ∫⁻ y, ENNReal.ofReal (ζ n y *
        (ρ τ y ^ (q - 2) * flowGamma lam h (ρ τ) (ρ τ) y)) =
        ENNReal.ofReal (∫ τ in Set.Ioo τ₁ τ₂, energyA lam h q ρ (ζ n) τ) := fun n => by
      obtain ⟨hAint, -⟩ := S.integrated_real (Zn n) hC0 hC (hBint n)
      rw [ofReal_integral_eq_lintegral_ofReal hAint
        (Filter.Eventually.of_forall fun τ => S.energyA_nonneg (Zn n).nonneg τ)]
      refine setLIntegral_congr_fun measurableSet_Ioo fun τ hτ => ?_
      exact (ofReal_integral_eq_lintegral_ofReal (S.integrable_slice (Zn n) hC hτ).1
        (Filter.Eventually.of_forall fun y => mul_nonneg ((Zn n).nonneg y)
          (S.measurable_FA_nonneg (τ, y)))).symm
    have hXB : ∀ n, ∫⁻ τ in Set.Ioo τ₁ τ₂, ∫⁻ y, ENNReal.ofReal (ζ n y *
        (ρ τ y ^ q * coefficientGammaSum lam h (β τ) y)) =
        ENNReal.ofReal (∫ τ in Set.Ioo τ₁ τ₂, energyB lam h q ρ β (ζ n) τ) := fun n => by
      rw [ofReal_integral_eq_lintegral_ofReal (hBint n)
        (Filter.Eventually.of_forall fun τ => S.energyB_nonneg (Zn n).nonneg τ)]
      refine setLIntegral_congr_fun measurableSet_Ioo fun τ hτ => ?_
      exact (ofReal_integral_eq_lintegral_ofReal (S.integrable_slice (Zn n) hC hτ).2
        (Filter.Eventually.of_forall fun y => mul_nonneg ((Zn n).nonneg y)
          (S.FB_nonneg (τ, y)))).symm
    have hXB_le : ∀ n, ENNReal.ofReal (∫ τ in Set.Ioo τ₁ τ₂, energyB lam h q ρ β (ζ n) τ) ≤ Y :=
      fun n => by
      rw [← hXB n]
      refine setLIntegral_mono' measurableSet_Ioo fun τ _ => lintegral_mono fun y => ?_
      exact ENNReal.ofReal_le_ofReal (hFB_le n (τ, y))
    have hI₀ : ENNReal.ofReal (∫ y, ρ τ₁ y ^ q) = L := by
      rw [hL]
      exact ofReal_integral_eq_lintegral_ofReal (S.pow_integrable τ₁ ⟨le_rfl, h12.le⟩)
        (Filter.Eventually.of_forall fun y => Real.rpow_nonneg (S.nonneg _ _) _)
    obtain ⟨K', hK'⟩ : ∃ K' : ℝ, K' = q * M * d * ((|lam * h / 2| + d) * C) * (τ₂ - τ₁) :=
      ⟨_, rfl⟩
    have hK'nn : 0 ≤ K' := by
      have h12' : 0 ≤ τ₂ - τ₁ := by linarith
      rw [hK']; positivity
    have hc₁nn : 0 ≤ q * (q - 1) / 4 := by positivity
    have hbd : ∀ n : ℕ, ENNReal.ofReal (q * (q - 1) / 4) * ∫⁻ τ in Set.Ioo τ₁ τ₂, ∫⁻ y,
        ENNReal.ofReal (ζ n y * (ρ τ y ^ (q - 2) * flowGamma lam h (ρ τ) (ρ τ) y)) ≤
        L + ENNReal.ofReal (4 * d * q * (q - 1) / lam ^ 2) * Y +
          ENNReal.ofReal (K' * (1 / ((n : ℝ) + 1))) := fun n => by
      obtain ⟨hAint, hreal⟩ := S.integrated_real (Zn n) hC0 hC (hBint n)
      have hI0 : 0 ≤ ∫ y, ρ τ₁ y ^ q :=
        integral_nonneg fun y => Real.rpow_nonneg (S.nonneg _ _) _
      have hB0 : 0 ≤ ∫ τ in Set.Ioo τ₁ τ₂, energyB lam h q ρ β (ζ n) τ :=
        setIntegral_nonneg measurableSet_Ioo fun τ _ => S.energyB_nonneg (Zn n).nonneg τ
      have hKn : 0 ≤ K' * (1 / ((n : ℝ) + 1)) := mul_nonneg hK'nn (by positivity)
      have hKe : q * (M / ((n : ℝ) + 1)) * d * ((|lam * h / 2| + d) * C) * (τ₂ - τ₁) =
          K' * (1 / ((n : ℝ) + 1)) := by rw [hK']; ring
      rw [hXA n, ← ENNReal.ofReal_mul hc₁nn]
      refine (ENNReal.ofReal_le_ofReal hreal).trans ?_
      rw [hKe, ENNReal.ofReal_add (add_nonneg hI0 (mul_nonneg hc₂nn hB0)) hKn,
        ENNReal.ofReal_add hI0 (mul_nonneg hc₂nn hB0), ENNReal.ofReal_mul hc₂nn, hI₀]
      exact add_le_add (add_le_add le_rfl (mul_le_mul' le_rfl (hXB_le n))) le_rfl
    have hK : Tendsto (fun n : ℕ => K' * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul K'
    have hWt : Tendsto (fun n : ℕ => L + ENNReal.ofReal (4 * d * q * (q - 1) / lam ^ 2) * Y +
        ENNReal.ofReal (K' * (1 / ((n : ℝ) + 1)))) atTop
        (𝓝 (L + ENNReal.ofReal (4 * d * q * (q - 1) / lam ^ 2) * Y + ENNReal.ofReal 0)) :=
      tendsto_const_nhds.add (ENNReal.tendsto_ofReal hK)
    have hc : ENNReal.ofReal (q * (q - 1) / 4) ≠ 0 :=
      (ENNReal.ofReal_pos.2 (by positivity)).ne'
    have := lintegral_cutoff_le_of_bound (S := Set.Ioo τ₁ τ₂)
      (fun p : ℝ × EvolutionAmbientState d =>
        ρ p.1 p.2 ^ (q - 2) * flowGamma lam h (ρ p.1) (ρ p.1) p.2) S.measurable_FA hζm
      (fun y => tendsto_velocityCutoff b y) hc ENNReal.ofReal_ne_top hWt hbd
    simpa only [ENNReal.ofReal_zero, add_zero] using this

end EnergySetting

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
