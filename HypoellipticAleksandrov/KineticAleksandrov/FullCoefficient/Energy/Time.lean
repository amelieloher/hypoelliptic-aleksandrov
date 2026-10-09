module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Energy.SliceDeriv

/-!
# The time term of the energy inequality

The energy inequality, "Time": for a jointly smooth `ρ ≥ 0`, bounded, with
`|∂_τ ρ| ≤ D(y)` for an integrable `D`, the cut-off mass `a(τ) = ∫ ζ ρ(τ)^q` is differentiable with
derivative `∫ ζ q ρ^{q-1} ∂_τ ρ`, and the fundamental theorem of calculus holds in `τ`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory Metric

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ} {ρ : ℝ → EvolutionAmbientState d → ℝ} {q : ℝ}

/-- The cut-off mass `a(τ) = ∫ ζ ρ(τ)^q`. -/
def cutoffMass (q : ℝ) (ρ : ℝ → EvolutionAmbientState d → ℝ) (ζ : EvolutionAmbientState d → ℝ)
    (τ : ℝ) : ℝ := ∫ y, ζ y * ρ τ y ^ q

/-- The derivative `∫ ζ q ρ^{q-1} ∂_τ ρ` of the cut-off mass. -/
def cutoffMassDeriv (q : ℝ) (ρ : ℝ → EvolutionAmbientState d → ℝ)
    (ζ : EvolutionAmbientState d → ℝ) (τ : ℝ) : ℝ :=
  ∫ y, ζ y * (q * ρ τ y ^ (q - 1) * deriv (fun τ' => ρ τ' y) τ)

/-- The time-regularity hypotheses on `ρ`. -/
structure TimeHyp (q : ℝ) (ρ : ℝ → EvolutionAmbientState d → ℝ) (R₀ : ℝ)
    (D : EvolutionAmbientState d → ℝ) : Prop where
  one_lt : 1 < q
  smooth : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × EvolutionAmbientState d => ρ p.1 p.2)
  nonneg : ∀ τ y, 0 ≤ ρ τ y
  le : ∀ τ y, ρ τ y ≤ R₀
  dom_integrable : Integrable D
  dom : ∀ τ y, |deriv (fun τ' => ρ τ' y) τ| ≤ D y

variable {R₀ : ℝ} {D : EvolutionAmbientState d → ℝ} {ζ : EvolutionAmbientState d → ℝ}

namespace TimeHyp

variable (H : TimeHyp q ρ R₀ D)

include H

theorem continuous_pow (s : ℝ) (hs : 0 ≤ s) :
    Continuous fun p : ℝ × EvolutionAmbientState d => ρ p.1 p.2 ^ s :=
  H.smooth.continuous.rpow_const fun _ => Or.inr hs

theorem abs_integrand_le (hζ : ∀ y, |ζ y| ≤ 1) (τ : ℝ) (y : EvolutionAmbientState d) :
    |ζ y * (q * ρ τ y ^ (q - 1) * deriv (fun τ' => ρ τ' y) τ)| ≤ q * R₀ ^ (q - 1) * D y := by
  have hq := H.one_lt
  have h0 := H.nonneg τ y
  have h1 : ρ τ y ^ (q - 1) ≤ R₀ ^ (q - 1) := Real.rpow_le_rpow h0 (H.le τ y) (by linarith)
  have h2 : 0 ≤ ρ τ y ^ (q - 1) := Real.rpow_nonneg h0 _
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ q), abs_of_nonneg h2]
  have h3 := H.dom τ y
  have hD : 0 ≤ D y := (abs_nonneg _).trans h3
  have hR : 0 ≤ R₀ ^ (q - 1) := h2.trans h1
  have hq0 : 0 ≤ q := by linarith
  calc |ζ y| * (q * ρ τ y ^ (q - 1) * |deriv (fun τ' => ρ τ' y) τ|)
      ≤ 1 * (q * R₀ ^ (q - 1) * D y) :=
        mul_le_mul (hζ y) (mul_le_mul (mul_le_mul_of_nonneg_left h1 hq0) h3 (abs_nonneg _)
          (mul_nonneg hq0 hR)) (mul_nonneg (mul_nonneg hq0 h2) (abs_nonneg _)) zero_le_one
    _ = _ := by ring

theorem hasDerivAt_cutoffMass (hζ : Continuous ζ) (hζ1 : ∀ y, |ζ y| ≤ 1) (τ : ℝ)
    (hint : Integrable fun y => ρ τ y ^ q) :
    HasDerivAt (cutoffMass q ρ ζ) (cutoffMassDeriv q ρ ζ τ) τ := by
  have hq := H.one_lt
  have hcy : ∀ τ, Continuous fun y => ρ τ y := fun τ =>
    H.smooth.continuous.comp (Continuous.prodMk_right τ)
  have hcpow : ∀ τ (s : ℝ), 0 ≤ s → Continuous fun y => ρ τ y ^ s := fun τ s hs =>
    (hcy τ).rpow_const fun y => Or.inr hs
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun τ y => ζ y * ρ τ y ^ q)
    (F' := fun τ y => ζ y * (q * ρ τ y ^ (q - 1) * deriv (fun τ' => ρ τ' y) τ)) (x₀ := τ)
    (bound := fun y => q * R₀ ^ (q - 1) * D y) (s := ball τ 1) (ball_mem_nhds τ one_pos)
    (Filter.Eventually.of_forall fun x =>
      (hζ.mul (hcpow x q (by linarith))).aestronglyMeasurable)
    (integrable_cutoff_mul hζ hζ1 hint)
    (hζ.mul (((hcpow τ (q - 1) (by linarith)).const_mul q).mul
      ((continuous_deriv_slice H.smooth).comp (Continuous.prodMk_right τ)))).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y x _ => by
      rw [Real.norm_eq_abs]; exact H.abs_integrand_le hζ1 x y)
    (H.dom_integrable.const_mul _)
    (Filter.Eventually.of_forall fun y x _ => by
      have h1 := hasDerivAt_slice H.smooth x y
      have h2 := (h1.rpow_const (p := q) (Or.inr hq.le)).const_mul (ζ y)
      refine h2.congr_deriv ?_
      ring)
  exact key.2

theorem continuous_integrand (hζ : Continuous ζ) :
    Continuous fun p : ℝ × EvolutionAmbientState d =>
      ζ p.2 * (q * ρ p.1 p.2 ^ (q - 1) * deriv (fun τ' => ρ τ' p.2) p.1) := by
  have hq := H.one_lt
  exact (hζ.comp continuous_snd).mul (((H.continuous_pow (q - 1) (by linarith)).const_mul q).mul
    (continuous_deriv_slice H.smooth))

theorem stronglyMeasurable_cutoffMassDeriv (hζ : Continuous ζ) :
    StronglyMeasurable (cutoffMassDeriv q ρ ζ) :=
  (H.continuous_integrand hζ).stronglyMeasurable.integral_prod_right'

theorem abs_cutoffMassDeriv_le (hζ1 : ∀ y, |ζ y| ≤ 1) (τ : ℝ) :
    |cutoffMassDeriv q ρ ζ τ| ≤ ∫ y, q * R₀ ^ (q - 1) * D y := by
  have := norm_integral_le_of_norm_le
    (f := fun y => ζ y * (q * ρ τ y ^ (q - 1) * deriv (fun τ' => ρ τ' y) τ))
    (H.dom_integrable.const_mul (q * R₀ ^ (q - 1)))
    (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact H.abs_integrand_le hζ1 τ y)
  rw [Real.norm_eq_abs] at this
  exact this

theorem intervalIntegrable_cutoffMassDeriv (hζ : Continuous ζ) (hζ1 : ∀ y, |ζ y| ≤ 1)
    (τ₁ τ₂ : ℝ) : IntervalIntegrable (cutoffMassDeriv q ρ ζ) volume τ₁ τ₂ := by
  have hm : AEStronglyMeasurable (cutoffMassDeriv q ρ ζ) volume :=
    (H.stronglyMeasurable_cutoffMassDeriv hζ).aestronglyMeasurable
  have hb : ∀ s : Set ℝ, volume s ≠ ⊤ → IntegrableOn (cutoffMassDeriv q ρ ζ) s volume :=
    fun s hs => Measure.integrableOn_of_bounded (M := ∫ y, q * R₀ ^ (q - 1) * D y) hs
      hm (Filter.Eventually.of_forall fun τ => by
        rw [Real.norm_eq_abs]; exact H.abs_cutoffMassDeriv_le hζ1 τ)
  exact ⟨hb _ (by simp), hb _ (by simp)⟩

/-- The fundamental theorem of calculus for the cut-off mass. -/
theorem integral_cutoffMassDeriv (hζ : Continuous ζ) (hζ1 : ∀ y, |ζ y| ≤ 1) {τ₁ τ₂ : ℝ}
    (h12 : τ₁ ≤ τ₂) (hint : ∀ τ ∈ Set.Icc τ₁ τ₂, Integrable fun y => ρ τ y ^ q) :
    ∫ τ in τ₁..τ₂, cutoffMassDeriv q ρ ζ τ = cutoffMass q ρ ζ τ₂ - cutoffMass q ρ ζ τ₁ :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx =>
    H.hasDerivAt_cutoffMass hζ hζ1 x (hint x (by rwa [Set.uIcc_of_le h12] at hx)))
    (H.intervalIntegrable_cutoffMassDeriv hζ hζ1 τ₁ τ₂)

end TimeHyp

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
