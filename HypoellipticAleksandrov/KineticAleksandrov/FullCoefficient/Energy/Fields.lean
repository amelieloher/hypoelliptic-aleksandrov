module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Energy.Domination

/-!
# The flux field: smoothness and bounds

The energy inequality: the components `gradFluxZ` and `fluxV` of the flux
field are smooth, and they and their first partials are bounded by the gradient and Hessian norms of
`ρ` and `J`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ} {ρ : EvolutionAmbientState d → ℝ} {J : EvolutionAmbientState d → PDE.Mat d}
  {lam h : ℝ}

theorem gradFluxZ_eq_lin (i : Fin d) :
    gradFluxZ lam h ρ i = fun y => lam * h ^ 2 / 2 * positionPartial i ρ y +
      (-(lam * h / 2)) * velocityPartial i ρ y := funext fun y => by unfold gradFluxZ; ring

theorem contDiff_gradFluxZ (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (gradFluxZ lam h ρ i) := by
  rw [gradFluxZ_eq_lin]
  exact (contDiff_const.mul (contDiff_coordPartial hρ (Sum.inr i))).add
    (contDiff_const.mul (contDiff_coordPartial hρ (Sum.inl i)))

theorem contDiff_sum_velocityPartial (hJ : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) fun y => J y i j)
    (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) fun y => ∑ j, velocityPartial j (fun y => J y i j) y :=
  ContDiff.sum fun j _ => contDiff_coordPartial (hJ i j) (Sum.inl j)

theorem contDiff_fluxV (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (hJ : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) fun y => J y i j)
    (i : Fin d) : ContDiff ℝ (⊤ : ℕ∞) (fluxV lam h ρ J i) :=
  (contDiff_const.mul (contDiff_coordPartial hρ (Sum.inr i))).add
    (contDiff_sum_velocityPartial hJ i)

theorem contDiff_fluxField (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (hJ : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) fun y => J y i j) (c : Fin d ⊕ Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (fluxField lam h ρ J c) := by
  rcases c with i | i
  · exact contDiff_fluxV hρ hJ i
  · exact contDiff_gradFluxZ hρ i

theorem abs_gradFluxZ_le (i : Fin d) (y : EvolutionAmbientState d) :
    |gradFluxZ lam h ρ i y| ≤ (|lam * h ^ 2 / 2| + |lam * h / 2|) * gradNorm ρ y := by
  unfold gradFluxZ
  have h1 := energy_abs_coordPartial_le_gradNorm (Sum.inr i) ρ y
  have h2 := energy_abs_coordPartial_le_gradNorm (Sum.inl i) ρ y
  simp only [positionPartial_eq, velocityPartial_eq]
  calc |lam * h ^ 2 / 2 * coordPartial (Sum.inr i) ρ y - lam * h / 2 * coordPartial (Sum.inl i) ρ y|
      ≤ |lam * h ^ 2 / 2 * coordPartial (Sum.inr i) ρ y| +
          |lam * h / 2 * coordPartial (Sum.inl i) ρ y| := abs_sub _ _
    _ ≤ |lam * h ^ 2 / 2| * gradNorm ρ y + |lam * h / 2| * gradNorm ρ y := by
        rw [abs_mul, abs_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg _))
          (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))
    _ = _ := by ring

theorem abs_coordPartial_gradFluxZ_le (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (c : Fin d ⊕ Fin d) (i : Fin d)
    (y : EvolutionAmbientState d) :
    |coordPartial c (gradFluxZ lam h ρ i) y| ≤
      (|lam * h ^ 2 / 2| + |lam * h / 2|) * hessNorm ρ y := by
  have hdρ : ∀ c, Differentiable ℝ (coordPartial c ρ) := fun c => differentiable_coordPartial hρ c
  rw [gradFluxZ_eq_lin]
  simp only [positionPartial_eq, velocityPartial_eq]
  rw [coordPartial_lin₂ _ _ (hdρ (Sum.inr i) y) (hdρ (Sum.inl i) y) c]
  have h1 := energy_abs_coordPartial₂_le_hessNorm c (Sum.inr i) ρ y
  have h2 := energy_abs_coordPartial₂_le_hessNorm c (Sum.inl i) ρ y
  calc |lam * h ^ 2 / 2 * coordPartial c (coordPartial (Sum.inr i) ρ) y +
        -(lam * h / 2) * coordPartial c (coordPartial (Sum.inl i) ρ) y|
      ≤ |lam * h ^ 2 / 2 * coordPartial c (coordPartial (Sum.inr i) ρ) y| +
          |-(lam * h / 2) * coordPartial c (coordPartial (Sum.inl i) ρ) y| := abs_add_le _ _
    _ ≤ |lam * h ^ 2 / 2| * hessNorm ρ y + |lam * h / 2| * hessNorm ρ y := by
        rw [abs_mul, abs_mul, abs_neg]
        exact add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg _))
          (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))
    _ = _ := by ring

theorem abs_fluxV_le (i : Fin d) (y : EvolutionAmbientState d) :
    |fluxV lam h ρ J i y| ≤ |lam * h / 2| * gradNorm ρ y + d * coefficientGradNorm J y := by
  unfold fluxV
  have h1 := energy_abs_coordPartial_le_gradNorm (Sum.inr i) ρ y
  simp only [positionPartial_eq]
  have h2 : |∑ j, velocityPartial j (fun y => J y i j) y| ≤ d * coefficientGradNorm J y := by
    calc _ ≤ ∑ j, |velocityPartial j (fun y => J y i j) y| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin d, coefficientGradNorm J y :=
          Finset.sum_le_sum fun j _ => abs_coordPartial_coeff_le (Sum.inl j) J i j y
      _ = d * coefficientGradNorm J y := by simp
  calc |-(lam * h / 2) * coordPartial (Sum.inr i) ρ y + ∑ j, velocityPartial j (fun y => J y i j) y|
      ≤ |-(lam * h / 2) * coordPartial (Sum.inr i) ρ y| +
          |∑ j, velocityPartial j (fun y => J y i j) y| := abs_add_le _ _
    _ ≤ |lam * h / 2| * gradNorm ρ y + d * coefficientGradNorm J y := by
        rw [abs_mul, abs_neg]
        exact add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg _)) h2

theorem abs_coordPartial_fluxV_le (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (hJ : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) fun y => J y i j) (c : Fin d ⊕ Fin d) (i : Fin d)
    (y : EvolutionAmbientState d) :
    |coordPartial c (fluxV lam h ρ J i) y| ≤
      |lam * h / 2| * hessNorm ρ y + d * coefficientHessNorm J y := by
  have hdρ : ∀ c, Differentiable ℝ (coordPartial c ρ) := fun c => differentiable_coordPartial hρ c
  have hd2 : Differentiable ℝ fun y => ∑ j, velocityPartial j (fun y => J y i j) y :=
    (contDiff_sum_velocityPartial hJ i).differentiable (by simp)
  have e : fluxV lam h ρ J i = fun y => -(lam * h / 2) * positionPartial i ρ y +
      1 * ∑ j, velocityPartial j (fun y => J y i j) y := funext fun y => by
    unfold fluxV; ring
  have h1 := coordPartial_lin₂ (-(lam * h / 2)) 1 (hdρ (Sum.inr i) y) (hd2 y) c
  have h2 := coordPartial_finsetSum_at (y := y) Finset.univ
    (f := fun j y => coordPartial (Sum.inl j) (fun y => J y i j) y)
    (fun j _ => differentiable_coordPartial (hJ i j) (Sum.inl j) y) c
  rw [e]
  simp only [positionPartial_eq, velocityPartial_eq] at h1 ⊢
  rw [h1, one_mul, h2]
  have hA := energy_abs_coordPartial₂_le_hessNorm c (Sum.inr i) ρ y
  have hB : |∑ j, coordPartial c (coordPartial (Sum.inl j) (fun y => J y i j)) y| ≤
      d * coefficientHessNorm J y := by
    calc _ ≤ ∑ j, |coordPartial c (coordPartial (Sum.inl j) (fun y => J y i j)) y| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin d, coefficientHessNorm J y :=
          Finset.sum_le_sum fun j _ => abs_coordPartial₂_coeff_le c (Sum.inl j) J i j y
      _ = d * coefficientHessNorm J y := by simp
  calc |-(lam * h / 2) * coordPartial c (coordPartial (Sum.inr i) ρ) y +
        ∑ j, coordPartial c (coordPartial (Sum.inl j) (fun y => J y i j)) y|
      ≤ |-(lam * h / 2) * coordPartial c (coordPartial (Sum.inr i) ρ) y| +
          |∑ j, coordPartial c (coordPartial (Sum.inl j) (fun y => J y i j)) y| := abs_add_le _ _
    _ ≤ |lam * h / 2| * hessNorm ρ y + d * coefficientHessNorm J y := by
        rw [abs_mul, abs_neg]
        exact add_le_add (mul_le_mul_of_nonneg_left hA (abs_nonneg _)) hB

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
