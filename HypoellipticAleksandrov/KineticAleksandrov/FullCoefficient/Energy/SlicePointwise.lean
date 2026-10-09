module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Energy.Fields

/-!
# The pointwise inequality behind the energy inequality

The energy inequality: at a point of phase space,
`¼ ρ^{q-2} |Dρ|²_{M^h} - (4d/λ²) ρ^q |Dβ|²_{M^h} ≤ ρ^{q-2} ∑_c ∂_cρ F_c`, where `F` is the flux
field.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open Matrix
open scoped MatrixOrder

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ} {lam h : ℝ} {ρ : EvolutionAmbientState d → ℝ}
  {β J : EvolutionAmbientState d → PDE.Mat d}

theorem rpow_sub_two_mul_sq {r q : ℝ} (hr : 0 < r) : r ^ (q - 2) * r ^ 2 = r ^ q := by
  rw [← Real.rpow_natCast r 2, ← Real.rpow_add hr]
  norm_num

/-- `J = ρ β` gives `∑_j ∂_{v_j} J_ij = ∑_j β_ij ∂_{v_j} ρ + ρ (div_v β)_i`. -/
theorem fluxV_eq (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hβ : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) fun y => β y i j)
    (hJρ : ∀ i j y, J y i j = ρ y * β y i j) (i : Fin d) (y : EvolutionAmbientState d) :
    fluxV lam h ρ J i y =
      -(lam * h / 2) * positionPartial i ρ y + ∑ j, β y i j * velocityPartial j ρ y +
        ρ y * divCoefficient β y i := by
  unfold fluxV divCoefficient
  have hj : ∀ j, velocityPartial j (fun y => J y i j) y =
      β y i j * velocityPartial j ρ y + ρ y * velocityPartial j (fun y => β y i j) y := fun j => by
    have e : (fun y => J y i j) = fun y => ρ y * β y i j := funext fun y => hJρ i j y
    rw [e, velocityPartial_eq, coordPartial_mul _ (hρ.differentiable (by simp) y)
      ((hβ i j).differentiable (by simp) y)]
    simp only [velocityPartial_eq]
    ring
  simp_rw [hj]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- The contraction of the flux field with `Dρ`. -/
theorem sum_fluxField_mul (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (hβ : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) fun y => β y i j)
    (hJρ : ∀ i j y, J y i j = ρ y * β y i j) (y : EvolutionAmbientState d) :
    ∑ c, coordPartial c ρ y * fluxField lam h ρ J c y =
      Gform lam h (β y) (fun i => positionPartial i ρ y) (fun i => velocityPartial i ρ y) +
        ρ y * ∑ i, velocityPartial i ρ y * divCoefficient β y i := by
  rw [Fintype.sum_sum_type]
  simp only [fluxField]
  have key : ∀ i : Fin d, coordPartial (Sum.inl i) ρ y * fluxV lam h ρ J i y +
      coordPartial (Sum.inr i) ρ y * gradFluxZ lam h ρ i y =
      (lam * h ^ 2 / 2 * (positionPartial i ρ y * positionPartial i ρ y) -
        lam * h * (positionPartial i ρ y * velocityPartial i ρ y)) +
      velocityPartial i ρ y * (∑ j, β y i j * velocityPartial j ρ y) +
      ρ y * (velocityPartial i ρ y * divCoefficient β y i) := fun i => by
    rw [fluxV_eq hρ hβ hJρ]
    simp only [gradFluxZ, ← velocityPartial_eq, ← positionPartial_eq]
    ring
  rw [← Finset.sum_add_distrib]
  simp_rw [key]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  unfold Gform
  simp only [PDE.vecDot, Matrix.mulVec, dotProduct]

/-- The pointwise energy inequality, with `ρ > 0`, `β ≥ λ` and `J = ρ β`. -/
theorem pointwise_energy {q : ℝ} (hlam : 0 < lam) (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (hβ : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) fun y => β y i j)
    (hJρ : ∀ i j y, J y i j = ρ y * β y i j) (y : EvolutionAmbientState d) (hpos : 0 < ρ y)
    (hloew : lam • (1 : PDE.Mat d) ≤ β y) :
    1 / 4 * (ρ y ^ (q - 2) * flowGamma lam h ρ ρ y) -
        4 * d / lam ^ 2 * (ρ y ^ q * coefficientGammaSum lam h β y) ≤
      ρ y ^ (q - 2) * ∑ c, coordPartial c ρ y * fluxField lam h ρ J c y := by
  rw [sum_fluxField_mul hρ hβ hJρ]
  have hs : 0 ≤ ρ y ^ (q - 2) := (Real.rpow_pos_of_pos hpos _).le
  have h1 := energy_pointwise (h := h) (ρ := ρ y) (s := ρ y ^ (q - 2)) hlam hs hloew
    (fun i => positionPartial i ρ y) (fun i => velocityPartial i ρ y) (divCoefficient β y)
  have h2 := sum_sq_divCoefficient_le (h := h) hlam β y
  rw [← flowGamma_self] at h1
  have hV := coefficientGammaSum_nonneg (h := h) hlam β y
  have h3 : ρ y ^ (q - 2) * (ρ y ^ 2 / lam * ∑ i, divCoefficient β y i ^ 2) ≤
      4 * d / lam ^ 2 * (ρ y ^ q * coefficientGammaSum lam h β y) := by
    have e : 4 * d / lam ^ 2 * (ρ y ^ q * coefficientGammaSum lam h β y) =
        ρ y ^ (q - 2) * (ρ y ^ 2 / lam * (4 * d / lam * coefficientGammaSum lam h β y)) := by
      rw [← rpow_sub_two_mul_sq (q := q) hpos]
      ring
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ hs
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  nlinarith

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
