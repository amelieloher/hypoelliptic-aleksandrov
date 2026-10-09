module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.Fisher
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.Coefficient

/-!
# Fisher-type bound for the smoothed coefficient

The smoothing estimates, second half:
`r |Dβ|² ≤ C_d Λ² ∫ |DΦ_h|²/Φ_h (y - y') dm(y')`, from `r Dβ = D(Fm)_h - β Dr` and the weighted
Cauchy--Schwarz bound for the flux.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ} {lam Lam : ℝ} (Φ : SmoothingKernelFamily d lam) {h : ℝ}
  {F : EvolutionAmbientState d → PDE.Mat d} (m : Measure (EvolutionAmbientState d))

theorem coordPartial_mul {f g : EvolutionAmbientState d → ℝ} {y : EvolutionAmbientState d}
    (c : Fin d ⊕ Fin d) (hf : DifferentiableAt ℝ f y) (hg : DifferentiableAt ℝ g y) :
    coordPartial c (fun y => f y * g y) y =
      f y * coordPartial c g y + g y * coordPartial c f y := by
  unfold coordPartial
  have e : (fun y => f y * g y) = f * g := rfl
  rw [e, (hf.hasFDerivAt.mul hg.hasFDerivAt).fderiv]
  simp

/-- The squared gradient norm of the matrix field `B`, `|DB|² = ∑ᵢⱼ |D Bᵢⱼ|²`. -/
def coefficientGradNormSq (B : EvolutionAmbientState d → PDE.Mat d)
    (y : EvolutionAmbientState d) : ℝ :=
  ∑ i, ∑ j, gradNormSq (fun y => B y i j) y

variable [IsFiniteMeasure m]

theorem smoothFluxEntry_eq_mul (hh : 0 < h) (hm : m ≠ 0) (i j : Fin d)
    (y : EvolutionAmbientState d) :
    smoothFluxEntry Φ h F m i j y =
      smoothDensity Φ h m y * smoothCoefficient Φ h F m y i j := by
  rw [smoothCoefficient_of_ne_zero Φ m hm]
  simp only [Matrix.smul_apply, smoothFlux, Matrix.of_apply, smul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ (smoothDensity_pos Φ m hh hm y).ne', one_mul]

theorem contDiff_smoothDensity (hh : 0 < h) :
    ContDiff ℝ (⊤ : ℕ∞) (smoothDensity Φ h m) := by
  rw [smoothDensity_eq]
  exact contDiff_smoothWeighted (Cf := 1) hh measurable_const (fun _ => by simp)

theorem contDiff_smoothFluxEntry (hlam : 0 < lam) (hF : IsAdmissibleCoefficient lam Lam F)
    (hh : 0 < h) (i j : Fin d) : ContDiff ℝ (⊤ : ℕ∞) (smoothFluxEntry Φ h F m i j) := by
  rw [smoothFluxEntry_eq]
  exact contDiff_smoothWeighted hh (hF.measurable i j) (fun a => hF.abs_apply_le hlam a i j)

theorem contDiff_smoothCoefficient_entry (hlam : 0 < lam) (hF : IsAdmissibleCoefficient lam Lam F)
    (hh : 0 < h) (hm : m ≠ 0) (i j : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => smoothCoefficient Φ h F m y i j) := by
  have : (fun y => smoothCoefficient Φ h F m y i j) =
      fun y => (smoothDensity Φ h m y)⁻¹ * smoothFluxEntry Φ h F m i j y := by
    funext y
    rw [smoothFluxEntry_eq_mul Φ m hh hm, ← mul_assoc, inv_mul_cancel₀
      (smoothDensity_pos Φ m hh hm y).ne', one_mul]
  rw [this]
  exact ((contDiff_smoothDensity Φ m hh).inv fun y => (smoothDensity_pos Φ m hh hm y).ne').mul
    (contDiff_smoothFluxEntry Φ m hlam hF hh i j)

/-- `r ∂_c β = ∂_c J - β ∂_c r`. -/
theorem density_mul_coordPartial_coefficient (hlam : 0 < lam)
    (hF : IsAdmissibleCoefficient lam Lam F) (hh : 0 < h) (hm : m ≠ 0) (i j : Fin d)
    (c : Fin d ⊕ Fin d) (y : EvolutionAmbientState d) :
    smoothDensity Φ h m y * coordPartial c (fun y => smoothCoefficient Φ h F m y i j) y =
      coordPartial c (smoothFluxEntry Φ h F m i j) y -
        smoothCoefficient Φ h F m y i j * coordPartial c (smoothDensity Φ h m) y := by
  have hJ : smoothFluxEntry Φ h F m i j =
      fun y => smoothDensity Φ h m y * smoothCoefficient Φ h F m y i j :=
    funext fun y => smoothFluxEntry_eq_mul Φ m hh hm i j y
  have hr := ((contDiff_smoothDensity Φ m hh).differentiable (by simp)) y
  have hb := ((contDiff_smoothCoefficient_entry Φ m hlam hF hh hm i j).differentiable
    (by simp)) y
  rw [hJ, coordPartial_mul c hr hb]
  ring

theorem gradNormSq_coefficient_entry_le (hlam : 0 < lam)
    (hF : IsAdmissibleCoefficient lam Lam F) (hh : 0 < h) (hm : m ≠ 0) (i j : Fin d)
    (y : EvolutionAmbientState d) :
    smoothDensity Φ h m y ^ 2 * gradNormSq (fun y => smoothCoefficient Φ h F m y i j) y ≤
      4 * Lam ^ 2 * (smoothDensity Φ h m y * fisherSmooth Φ h m y) := by
  set r := smoothDensity Φ h m y with hr
  have hJ := gradNormSq_smoothWeighted_le (Φ := Φ) (h := h) m hh (hF.measurable i j)
    (fun a => hF.abs_apply_le hlam a i j) y
  have hD := gradNormSq_smoothWeighted_le (Φ := Φ) (h := h) m hh (f := fun _ => 1)
    measurable_const (Cf := 1) (fun _ => by simp) y
  rw [← smoothFluxEntry_eq] at hJ
  rw [← smoothDensity_eq] at hD
  have hβ : smoothCoefficient Φ h F m y i j ^ 2 ≤ Lam ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_smoothCoefficient_le Φ m hlam hF hh y i j) 2
  set b := smoothCoefficient Φ h F m y i j
  have hsum : r ^ 2 * gradNormSq (fun y => smoothCoefficient Φ h F m y i j) y ≤
      2 * gradNormSq (smoothFluxEntry Φ h F m i j) y + 2 * b ^ 2 * gradNormSq
        (smoothDensity Φ h m) y := by
    unfold gradNormSq
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun c _ => ?_
    have := density_mul_coordPartial_coefficient Φ m hlam hF hh hm i j c y
    have e : r ^ 2 * coordPartial c (fun y => smoothCoefficient Φ h F m y i j) y ^ 2 =
        (coordPartial c (smoothFluxEntry Φ h F m i j) y -
          b * coordPartial c (smoothDensity Φ h m) y) ^ 2 := by
      rw [← this]; ring
    rw [e]
    nlinarith [sq_nonneg (coordPartial c (smoothFluxEntry Φ h F m i j) y +
      b * coordPartial c (smoothDensity Φ h m) y)]
  have hrnn := smoothDensity_nonneg Φ m hh y
  have hFi := fisherSmooth_nonneg (Φ := Φ) (h := h) m hh y
  have hgJ : gradNormSq (smoothFluxEntry Φ h F m i j) y ≤ Lam ^ 2 * (r * fisherSmooth Φ h m y) := by
    calc _ ≤ Lam ^ 2 * r * fisherSmooth Φ h m y := hJ
      _ = _ := by ring
  have hgD : gradNormSq (smoothDensity Φ h m) y ≤ r * fisherSmooth Φ h m y := by
    calc _ ≤ 1 ^ 2 * r * fisherSmooth Φ h m y := hD
      _ = _ := by ring
  have hprod : 0 ≤ r * fisherSmooth Φ h m y := mul_nonneg hrnn hFi
  have hb2 : b ^ 2 * gradNormSq (smoothDensity Φ h m) y ≤ Lam ^ 2 * (r * fisherSmooth Φ h m y) :=
    mul_le_mul hβ hgD (Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg _)
  nlinarith

/-- The smoothing estimates: `|Dr|² / r ≤ ∫ |DΦ_h|²/Φ_h (y - y') dm` where `r > 0`. -/
theorem gradNormSq_smoothDensity_div_le (hh : 0 < h) (hm : m ≠ 0) (y : EvolutionAmbientState d) :
    gradNormSq (smoothDensity Φ h m) y / smoothDensity Φ h m y ≤ fisherSmooth Φ h m y := by
  have hr := smoothDensity_pos Φ m hh hm y
  have hD := gradNormSq_smoothWeighted_le (Φ := Φ) (h := h) m hh (f := fun _ => 1)
    measurable_const (Cf := 1) (fun _ => by simp) y
  rw [← smoothDensity_eq] at hD
  rw [div_le_iff₀ hr]
  nlinarith

/-- The smoothing estimates: `r |Dβ|² ≤ C_d Λ² ∫ |DΦ_h|²/Φ_h (y - y') dm` with `C_d = 4 d²`. -/
theorem density_mul_coefficientGradNormSq_le (hlam : 0 < lam)
    (hF : IsAdmissibleCoefficient lam Lam F) (hh : 0 < h) (hm : m ≠ 0)
    (y : EvolutionAmbientState d) :
    smoothDensity Φ h m y * coefficientGradNormSq (smoothCoefficient Φ h F m) y ≤
      4 * d ^ 2 * Lam ^ 2 * fisherSmooth Φ h m y := by
  have hr := smoothDensity_pos Φ m hh hm y
  unfold coefficientGradNormSq
  rw [Finset.mul_sum]
  have hij : ∀ i j : Fin d, smoothDensity Φ h m y *
      gradNormSq (fun y => smoothCoefficient Φ h F m y i j) y ≤
      4 * Lam ^ 2 * fisherSmooth Φ h m y := fun i j => by
    have := gradNormSq_coefficient_entry_le Φ m hlam hF hh hm i j y
    have h2 : smoothDensity Φ h m y * (smoothDensity Φ h m y *
        gradNormSq (fun y => smoothCoefficient Φ h F m y i j) y) ≤
        smoothDensity Φ h m y * (4 * Lam ^ 2 * fisherSmooth Φ h m y) := by nlinarith
    exact le_of_mul_le_mul_left h2 hr
  calc ∑ i, smoothDensity Φ h m y * ∑ j, gradNormSq (fun y => smoothCoefficient Φ h F m y i j) y
      ≤ ∑ _i : Fin d, ∑ _j : Fin d, 4 * Lam ^ 2 * fisherSmooth Φ h m y := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun j _ => hij i j
    _ = 4 * d ^ 2 * Lam ^ 2 * fisherSmooth Φ h m y := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
