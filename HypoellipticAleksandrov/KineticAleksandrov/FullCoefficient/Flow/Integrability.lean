module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Flow.Moments

/-!
# Integrability of the derivatives of the flow kernel

The Gaussian flow estimates: `∫ ‖y‖^k Φ_h`, `∫ |DΦ_h|² / Φ_h`,
`∫ |v| |∇_z Φ_h|` and `∫ |v| |D² Φ_h|` are finite.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ}

theorem integrable_pow_mul_abs_iterPartial {lam h : ℝ} (hl : 0 < lam) (hh : 0 < h)
    (l : List (Fin d ⊕ Fin d)) (j : ℕ) :
    Integrable (fun y : EvolutionAmbientState d =>
      (1 + ‖y‖) ^ j * |iterPartial l (flowKernel lam h) y|) := by
  obtain ⟨C, hC⟩ := flowKernel_iterPartial_bound (d := d) hl hh l
  have hint := (integrable_pow_mul_flowKernel (d := d) hl hh (j + l.length)).const_mul |C|
  refine hint.mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
  · exact ((by fun_prop : Continuous fun y : EvolutionAmbientState d => (1 + ‖y‖) ^ j).mul
      (iterPartial_flowKernel_continuous hl hh l).abs).aestronglyMeasurable
  · have h1 := hC h le_rfl y
    have hp : 0 ≤ (1 + ‖y‖) ^ j * |iterPartial l (flowKernel lam h) y| := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hp]
    have hpow : 0 ≤ (1 + ‖y‖) ^ j := by positivity
    calc (1 + ‖y‖) ^ j * |iterPartial l (flowKernel lam h) y|
        ≤ (1 + ‖y‖) ^ j * (C * (1 + ‖y‖) ^ l.length * flowKernel lam h y) :=
          mul_le_mul_of_nonneg_left h1 hpow
      _ ≤ (1 + ‖y‖) ^ j * (|C| * (1 + ‖y‖) ^ l.length * flowKernel lam h y) := by
          have hk := flowKernel_pos hl hh y
          gcongr
          exact le_abs_self C
      _ = |C| * ((1 + ‖y‖) ^ (j + l.length) * flowKernel lam h y) := by
          rw [pow_add]; ring

/-- The Gaussian flow estimates: the moments `‖y‖^k Φ_h` are integrable. -/
theorem integrable_norm_pow_mul_flowKernel {lam h : ℝ} (hl : 0 < lam) (hh : 0 < h) (k : ℕ) :
    Integrable (fun y : EvolutionAmbientState d => ‖y‖ ^ k * flowKernel lam h y) := by
  refine (integrable_pow_mul_flowKernel (d := d) hl hh k).mono' ?_
    (Filter.Eventually.of_forall fun y => ?_)
  · exact ((by fun_prop : Continuous fun y : EvolutionAmbientState d => ‖y‖ ^ k).mul
      (flowKernel_continuous hl hh)).aestronglyMeasurable
  · have hk := flowKernel_pos hl hh y
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    gcongr
    linarith

/-- The Gaussian flow estimates: `(∂_δ Φ_h)² / Φ_h` is integrable for each coordinate direction. -/
theorem integrable_sq_div_dirPartial_flowKernel {lam h : ℝ} (hl : 0 < lam) (hh : 0 < h)
    (δ : Fin d ⊕ Fin d) :
    Integrable (fun y : EvolutionAmbientState d =>
      dirPartial δ (flowKernel lam h) y ^ 2 / flowKernel lam h y) := by
  obtain ⟨C, hC⟩ := flowKernel_iterPartial_bound (d := d) hl hh [δ]
  have hint := (integrable_pow_mul_flowKernel (d := d) hl hh 2).const_mul (C ^ 2)
  refine hint.mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
  · have hc := iterPartial_flowKernel_continuous (d := d) hl hh [δ]
    have hΦ := flowKernel_continuous (d := d) hl hh
    exact ((hc.pow 2).div hΦ fun y => (flowKernel_pos hl hh y).ne').aestronglyMeasurable
  · have hk := flowKernel_pos hl hh y
    have h1 := hC h le_rfl y
    simp only [iterPartial, List.length_singleton, pow_one] at h1
    have hnn : 0 ≤ dirPartial δ (flowKernel lam h) y ^ 2 / flowKernel lam h y := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnn, div_le_iff₀ hk]
    have h2 : dirPartial δ (flowKernel lam h) y ^ 2 ≤
        (C * (1 + ‖y‖) * flowKernel lam h y) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    calc dirPartial δ (flowKernel lam h) y ^ 2
        ≤ (C * (1 + ‖y‖) * flowKernel lam h y) ^ 2 := h2
      _ = C ^ 2 * ((1 + ‖y‖) ^ 2 * flowKernel lam h y) * flowKernel lam h y := by ring

/-- The Gaussian flow estimates: `|DΦ_h|² / Φ_h` is integrable, where `DΦ_h` is the full phase-space
gradient (all velocity and position partials). -/
theorem integrable_gradient_sq_div_flowKernel {lam h : ℝ} (hl : 0 < lam) (hh : 0 < h) :
    Integrable (fun y : EvolutionAmbientState d =>
      (∑ i, (velocityPartial i (flowKernel lam h) y ^ 2 +
        positionPartial i (flowKernel lam h) y ^ 2)) / flowKernel lam h y) := by
  simp_rw [Finset.sum_div, add_div]
  refine integrable_finsetSum _ fun i _ => ?_
  exact (integrable_sq_div_dirPartial_flowKernel hl hh (Sum.inl i)).add
    (integrable_sq_div_dirPartial_flowKernel hl hh (Sum.inr i))

/-- The Gaussian flow estimates: `|v| |∂_{z_i} Φ_h|` is integrable. -/
theorem integrable_norm_velocity_mul_positionPartial {lam h : ℝ} (hl : 0 < lam) (hh : 0 < h)
    (i : Fin d) :
    Integrable (fun y : EvolutionAmbientState d =>
      ‖y.1‖ * |positionPartial i (flowKernel lam h) y|) := by
  refine (integrable_pow_mul_abs_iterPartial (d := d) hl hh [Sum.inr i] 1).mono' ?_
    (Filter.Eventually.of_forall fun y => ?_)
  · exact ((continuous_norm.comp continuous_fst).mul
      (iterPartial_flowKernel_continuous (d := d) hl hh [Sum.inr i]).abs).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    simp only [iterPartial, pow_one]
    exact mul_le_mul_of_nonneg_right (by linarith [norm_fst_le y, norm_nonneg y])
      (abs_nonneg _)

/-- The Gaussian flow estimates: `|v| |∂_δ' ∂_δ Φ_h|` is integrable for all coordinate directions.
-/
theorem integrable_norm_velocity_mul_dirPartial_dirPartial {lam h : ℝ} (hl : 0 < lam)
    (hh : 0 < h) (δ δ' : Fin d ⊕ Fin d) :
    Integrable (fun y : EvolutionAmbientState d =>
      ‖y.1‖ * |dirPartial δ' (dirPartial δ (flowKernel lam h)) y|) := by
  refine (integrable_pow_mul_abs_iterPartial (d := d) hl hh [δ', δ] 1).mono' ?_
    (Filter.Eventually.of_forall fun y => ?_)
  · exact ((continuous_norm.comp continuous_fst).mul
      (iterPartial_flowKernel_continuous (d := d) hl hh [δ', δ]).abs).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    simp only [iterPartial, pow_one]
    gcongr
    have := norm_fst_le y
    linarith [this]

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
