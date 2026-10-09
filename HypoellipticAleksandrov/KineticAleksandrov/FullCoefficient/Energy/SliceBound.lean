module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Energy.Slice

/-!
# The slice energy inequality

The energy inequality: on a non-zero slice,
`∫ ζ q ρ^{q-1} ∂_τ ρ + (q(q-1)/4) ∫ ζ ρ^{q-2} |Dρ|²_M ≤ (4dq(q-1)/λ²) ∫ ζ ρ^q |Dβ|²_M + error`,
where the error is `O(ε)` for a cut-off with `|∂_v ζ| ≤ ε`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory Matrix
open scoped MatrixOrder

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ} {lam h q Bv ε : ℝ} {ρ dρ ζ : EvolutionAmbientState d → ℝ}
  {β J : EvolutionAmbientState d → PDE.Mat d}

theorem continuous_flowGamma_self {F : EvolutionAmbientState d → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (lam h : ℝ) : Continuous (flowGamma lam h F F) := by
  have hp : ∀ i, Continuous (positionPartial i F) := fun i =>
    continuous_coordPartial hF (Sum.inr i)
  have hv : ∀ i, Continuous (velocityPartial i F) := fun i =>
    continuous_coordPartial hF (Sum.inl i)
  unfold flowGamma gradZZ gradZV gradVV
  fun_prop

theorem continuous_coefficientGammaSum {B : EvolutionAmbientState d → PDE.Mat d}
    (hB : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) fun y => B y i j) (lam h : ℝ) :
    Continuous (coefficientGammaSum lam h B) := by
  unfold coefficientGammaSum
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    continuous_flowGamma_self (hB i j) lam h

theorem coefficientGammaSum_le (hlam : 0 < lam) (B : EvolutionAmbientState d → PDE.Mat d)
    (y : EvolutionAmbientState d) :
    coefficientGammaSum lam h B y ≤ lam / 2 * (3 * h ^ 2 + 2) * coefficientGradNormSq B y := by
  unfold coefficientGammaSum coefficientGradNormSq
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => flowGamma_self_le hlam _ y

namespace SliceHyp

variable (H : SliceHyp lam h q Bv ε ρ dρ ζ β J)

include H

/-- The integrability of the three weighted integrands of the slice energy inequality. -/
theorem integrable_gamma :
    Integrable (fun y => ζ y * (ρ y ^ (q - 2) * flowGamma lam h ρ ρ y)) := by
  have hρ := H.smooth_rho
  refine integrable_of_abs_le (K := lam / 2 * (3 * h ^ 2 + 2)) ?_ H.integrable.fisher fun y => ?_
  · exact (H.smooth_cutoff.continuous.mul (((contDiff_rpow_of_pos hρ H.pos _).continuous).mul
      (continuous_flowGamma_self hρ lam h))).aestronglyMeasurable
  · have h0 := flowGamma_self_nonneg (h := h) H.lam_pos ρ y
    have h1 := flowGamma_self_le (h := h) H.lam_pos ρ y
    have hr : 0 ≤ ρ y ^ (q - 2) := (Real.rpow_pos_of_pos (H.pos y) _).le
    rw [abs_of_nonneg (mul_nonneg (H.cutoff_nonneg y) (mul_nonneg hr h0))]
    calc ζ y * (ρ y ^ (q - 2) * flowGamma lam h ρ ρ y)
        ≤ 1 * (ρ y ^ (q - 2) * flowGamma lam h ρ ρ y) :=
          mul_le_mul_of_nonneg_right (H.cutoff_le_one y) (mul_nonneg hr h0)
      _ ≤ ρ y ^ (q - 2) * (lam / 2 * (3 * h ^ 2 + 2) * gradNormSq ρ y) := by
          rw [one_mul]; exact mul_le_mul_of_nonneg_left h1 hr
      _ = _ := by ring

theorem integrable_beta :
    Integrable (fun y => ζ y * (ρ y ^ q * coefficientGammaSum lam h β y)) := by
  have hρ := H.smooth_rho
  refine integrable_of_abs_le (K := lam / 2 * (3 * h ^ 2 + 2)) ?_ H.integrable.betaGradSq
    fun y => ?_
  · exact (H.smooth_cutoff.continuous.mul (((contDiff_rpow_of_pos hρ H.pos _).continuous).mul
      (continuous_coefficientGammaSum H.smooth_beta lam h))).aestronglyMeasurable
  · have h0 := coefficientGammaSum_nonneg (h := h) H.lam_pos β y
    have h1 := coefficientGammaSum_le (h := h) H.lam_pos β y
    have hr : 0 ≤ ρ y ^ q := (Real.rpow_pos_of_pos (H.pos y) _).le
    rw [abs_of_nonneg (mul_nonneg (H.cutoff_nonneg y) (mul_nonneg hr h0))]
    calc ζ y * (ρ y ^ q * coefficientGammaSum lam h β y)
        ≤ 1 * (ρ y ^ q * coefficientGammaSum lam h β y) :=
          mul_le_mul_of_nonneg_right (H.cutoff_le_one y) (mul_nonneg hr h0)
      _ ≤ ρ y ^ q * (lam / 2 * (3 * h ^ 2 + 2) * coefficientGradNormSq β y) := by
          rw [one_mul]; exact mul_le_mul_of_nonneg_left h1 hr
      _ = _ := by ring

/-- Lower bound for the weighted contraction of the flux field with `Dρ`. -/
theorem sum_T_ge :
    1 / 4 * (∫ y, ζ y * (ρ y ^ (q - 2) * flowGamma lam h ρ ρ y)) -
        4 * d / lam ^ 2 * ∫ y, ζ y * (ρ y ^ q * coefficientGammaSum lam h β y) ≤
      ∑ c, ∫ y, ζ y * (ρ y ^ (q - 2) * coordPartial c ρ y * fluxField lam h ρ J c y) := by
  have hρ := H.smooth_rho
  have hint : ∀ c, Integrable fun y => ζ y * (ρ y ^ (q - 2) * coordPartial c ρ y *
      fluxField lam h ρ J c y) := fun c =>
    integrable_cutoff_mul H.smooth_cutoff.continuous H.abs_cutoff_le (H.flux_integrable c).2.1
  rw [← integral_finsetSum _ fun c _ => hint c]
  have hl : ∫ y, (1 / 4 * (ζ y * (ρ y ^ (q - 2) * flowGamma lam h ρ ρ y)) -
      4 * d / lam ^ 2 * (ζ y * (ρ y ^ q * coefficientGammaSum lam h β y))) =
      1 / 4 * (∫ y, ζ y * (ρ y ^ (q - 2) * flowGamma lam h ρ ρ y)) -
        4 * d / lam ^ 2 * ∫ y, ζ y * (ρ y ^ q * coefficientGammaSum lam h β y) := by
    rw [integral_sub (H.integrable_gamma.const_mul (1 / 4))
      (H.integrable_beta.const_mul (4 * d / lam ^ 2)), integral_const_mul, integral_const_mul]
  rw [← hl]
  refine integral_mono ((H.integrable_gamma.const_mul (1 / 4)).sub
    (H.integrable_beta.const_mul (4 * d / lam ^ 2)))
    (integrable_finsetSum _ fun c _ => hint c) fun y => ?_
  have hp := pointwise_energy (q := q) (h := h) H.lam_pos hρ H.smooth_beta H.flux_eq y (H.pos y)
    (H.loewner y)
  have hz := mul_le_mul_of_nonneg_left hp (H.cutoff_nonneg y)
  have e : ∑ c, ζ y * (ρ y ^ (q - 2) * coordPartial c ρ y * fluxField lam h ρ J c y) =
      ζ y * (ρ y ^ (q - 2) * ∑ c, coordPartial c ρ y * fluxField lam h ρ J c y) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [e]
  simp only []
  linarith

/-- The error from the derivatives of the cut-off. -/
theorem abs_sum_E_le :
    |∑ c, ∫ y, coordPartial c ζ y * (ρ y ^ (q - 1) * fluxField lam h ρ J c y)| ≤
      d * ε * (|lam * h / 2| * (∫ y, ρ y ^ (q - 1) * gradNorm ρ y) +
        d * ∫ y, ρ y ^ (q - 1) * coefficientGradNorm J y) := by
  rw [Fintype.sum_sum_type]
  have hz : ∀ i : Fin d, ∫ y, coordPartial (Sum.inr i) ζ y *
      (ρ y ^ (q - 1) * fluxField lam h ρ J (Sum.inr i) y) = 0 := fun i => by
    simp [H.cutoff_inr]
  simp only [hz, Finset.sum_const_zero, add_zero]
  have hb : ∀ i : Fin d, |∫ y, coordPartial (Sum.inl i) ζ y *
      (ρ y ^ (q - 1) * fluxField lam h ρ J (Sum.inl i) y)| ≤
      ε * (|lam * h / 2| * (∫ y, ρ y ^ (q - 1) * gradNorm ρ y) +
        d * ∫ y, ρ y ^ (q - 1) * coefficientGradNorm J y) := fun i => by
    have hg : Integrable fun y => ε * (|lam * h / 2| * (ρ y ^ (q - 1) * gradNorm ρ y) +
        d * (ρ y ^ (q - 1) * coefficientGradNorm J y)) :=
      (((H.integrable.grad.const_mul _).add (H.integrable.fluxGrad.const_mul _)).const_mul ε)
    have key : ∀ y, ‖coordPartial (Sum.inl i) ζ y *
        (ρ y ^ (q - 1) * fluxField lam h ρ J (Sum.inl i) y)‖ ≤
        ε * (|lam * h / 2| * (ρ y ^ (q - 1) * gradNorm ρ y) +
          d * (ρ y ^ (q - 1) * coefficientGradNorm J y)) := fun y => by
      rw [Real.norm_eq_abs, abs_mul]
      have h1 := abs_fluxV_le (lam := lam) (h := h) (ρ := ρ) (J := J) i y
      have h2 := H.cutoff_inl i y
      have h4 : |ρ y ^ (q - 1) * fluxV lam h ρ J i y| ≤ ρ y ^ (q - 1) *
          (|lam * h / 2| * gradNorm ρ y + d * coefficientGradNorm J y) :=
        abs_rpow_mul_le (s := q - 1) (H.pos y) h1
      calc |coordPartial (Sum.inl i) ζ y| * |ρ y ^ (q - 1) * fluxField lam h ρ J (Sum.inl i) y|
          ≤ ε * (ρ y ^ (q - 1) * (|lam * h / 2| * gradNorm ρ y +
              d * coefficientGradNorm J y)) :=
            mul_le_mul h2 h4 (abs_nonneg _) H.eps_nonneg
        _ = _ := by ring
    have := norm_integral_le_of_norm_le hg (Filter.Eventually.of_forall key)
    rw [Real.norm_eq_abs] at this
    refine this.trans (le_of_eq ?_)
    rw [integral_const_mul, integral_add (H.integrable.grad.const_mul _)
      (H.integrable.fluxGrad.const_mul _), integral_const_mul, integral_const_mul]
  calc |∑ i, ∫ y, coordPartial (Sum.inl i) ζ y * (ρ y ^ (q - 1) * fluxV lam h ρ J i y)|
      ≤ ∑ i : Fin d, ε * (|lam * h / 2| * (∫ y, ρ y ^ (q - 1) * gradNorm ρ y) +
          d * ∫ y, ρ y ^ (q - 1) * coefficientGradNorm J y) :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hb i)
    _ = _ := by simp; ring

/-- **The slice energy inequality**. -/
theorem slice_energy :
    (∫ y, ζ y * (q * ρ y ^ (q - 1) * dρ y)) +
        q * (q - 1) / 4 * (∫ y, ζ y * (ρ y ^ (q - 2) * flowGamma lam h ρ ρ y)) ≤
      4 * d * q * (q - 1) / lam ^ 2 * (∫ y, ζ y * (ρ y ^ q * coefficientGammaSum lam h β y)) +
        q * ε * d * (|lam * h / 2| * (∫ y, ρ y ^ (q - 1) * gradNorm ρ y) +
          d * ∫ y, ρ y ^ (q - 1) * coefficientGradNorm J y) := by
  have h1 := H.integral_flux_by_parts
  have h2 := H.sum_T_ge
  have h3 := H.abs_sum_E_le
  have hq := H.one_lt
  have hqq : 0 < q * (q - 1) := mul_pos (by linarith) (by linarith)
  have h4 := mul_le_mul_of_nonneg_left h2 hqq.le
  have h5 : -(∑ c, ∫ y, coordPartial c ζ y * (ρ y ^ (q - 1) * fluxField lam h ρ J c y)) ≤
      d * ε * (|lam * h / 2| * (∫ y, ρ y ^ (q - 1) * gradNorm ρ y) +
        d * ∫ y, ρ y ^ (q - 1) * coefficientGradNorm J y) :=
    (neg_le_abs _).trans h3
  have h6 := mul_le_mul_of_nonneg_left h5 (by linarith : 0 ≤ q)
  have e : 4 * d * q * (q - 1) / lam ^ 2 = q * (q - 1) * (4 * d / lam ^ 2) := by ring
  rw [h1, e]
  nlinarith [h4, h6]

end SliceHyp

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
