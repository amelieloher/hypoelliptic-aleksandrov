module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Energy.Domination
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Energy.Cutoff

/-!
# Integration by parts against the velocity cut-off

The energy inequality: for a smooth positive `ρ` and a smooth field `X`,
`∫ ζ ρ^{q-1} ∂_c X = - ∫ ∂_c ζ ρ^{q-1} X - (q-1) ∫ ζ ρ^{q-2} ∂_c ρ X`, and the transport term
`∫ ζ q ρ^{q-1} v·∇_z ρ` vanishes for a velocity-only cut-off `ζ`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ}

/-- Integration by parts of `ρ^{q-1} ∂_c X` against a cut-off. -/
theorem integral_cutoff_rpow_mul_coordPartial {ρ X ζ : EvolutionAmbientState d → ℝ} {q A B : ℝ}
    (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hpos : ∀ y, 0 < ρ y) (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hA : ∀ y, |ζ y| ≤ A) (c : Fin d ⊕ Fin d)
    (hB : ∀ y, |coordPartial c ζ y| ≤ B)
    (hg : Integrable fun y => ρ y ^ (q - 1) * X y)
    (h3 : Integrable fun y => ρ y ^ (q - 2) * coordPartial c ρ y * X y)
    (h4 : Integrable fun y => ρ y ^ (q - 1) * coordPartial c X y) :
    ∫ y, ζ y * (ρ y ^ (q - 1) * coordPartial c X y) =
      -(∫ y, coordPartial c ζ y * (ρ y ^ (q - 1) * X y)) -
        (q - 1) * ∫ y, ζ y * (ρ y ^ (q - 2) * coordPartial c ρ y * X y) := by
  have hgs := contDiff_rpow_mul hρ hX hpos (q - 1)
  have hderiv : coordPartial c (fun y => ρ y ^ (q - 1) * X y) = fun y =>
      (q - 1) * (ρ y ^ (q - 2) * coordPartial c ρ y * X y) +
        ρ y ^ (q - 1) * coordPartial c X y := by
    rw [coordPartial_rpow_mul hρ hX hpos (q - 1) c]
    funext y
    have : q - 1 - 1 = q - 2 := by ring
    rw [this]
    ring
  have hgd : Integrable (coordPartial c fun y => ρ y ^ (q - 1) * X y) := by
    rw [hderiv]
    exact (h3.const_mul (q - 1)).add h4
  have key := integral_cutoff_mul_coordPartial_eq_neg hζ hgs hA c hB hg hgd
  rw [hderiv] at key
  beta_reduce at key
  simp only [mul_add] at key
  have i1 : Integrable fun y => ζ y * ((q - 1) * (ρ y ^ (q - 2) * coordPartial c ρ y * X y)) :=
    integrable_cutoff_mul hζ.continuous hA (h3.const_mul (q - 1))
  have i2 : Integrable fun y => ζ y * (ρ y ^ (q - 1) * coordPartial c X y) :=
    integrable_cutoff_mul hζ.continuous hA h4
  rw [integral_add i1 i2] at key
  have e1 : ∫ y, ζ y * ((q - 1) * (ρ y ^ (q - 2) * coordPartial c ρ y * X y)) =
      (q - 1) * ∫ y, ζ y * (ρ y ^ (q - 2) * coordPartial c ρ y * X y) := by
    rw [← integral_const_mul]
    congr 1
    funext y
    ring
  rw [e1] at key
  linarith

theorem coordPartial_inr_fst_apply (i j : Fin d) (y : EvolutionAmbientState d) :
    coordPartial (Sum.inr j) (fun y : EvolutionAmbientState d => y.1 i) y = 0 := by
  have hd : HasFDerivAt (fun y : EvolutionAmbientState d => y.1 i)
      ((ContinuousLinearMap.proj i).comp
        (ContinuousLinearMap.fst ℝ (PDE.Vec d) (PDE.Vec d))) y :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i).hasFDerivAt).comp y
      hasFDerivAt_fst
  rw [coordPartial, hd.fderiv]
  simp [coordDir]

theorem contDiff_fst_apply (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) fun y : EvolutionAmbientState d => y.1 i :=
  (contDiff_apply ℝ ℝ i).comp contDiff_fst

/-- The pointwise form of the transport term as a sum of position partials of `ρ^q`. -/
theorem cutoff_transport_eq_sum {ρ ζ : EvolutionAmbientState d → ℝ} {q : ℝ}
    (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hpos : ∀ y, 0 < ρ y) (y : EvolutionAmbientState d) :
    ζ y * (q * ρ y ^ (q - 1) * transportDerivative ρ y) =
      ∑ i, (y.1 i * ζ y) * coordPartial (Sum.inr i) (fun y => ρ y ^ q) y := by
  unfold transportDerivative
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coordPartial_rpow (Sum.inr i) ((hρ.differentiable (by simp)) y) (hpos y) q]
  simp only [positionPartial_eq]
  ring

/-- The transport term vanishes for a cut-off independent of the position. -/
theorem integral_cutoff_transport_eq_zero {ρ ζ : EvolutionAmbientState d → ℝ} {q B : ℝ}
    (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hpos : ∀ y, 0 < ρ y) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζz : ∀ i y, coordPartial (Sum.inr i) ζ y = 0) (hB : ∀ i y, |y.1 i * ζ y| ≤ B)
    (hpow : Integrable fun y => ρ y ^ q)
    (hgrad : ∀ i, Integrable fun y => ρ y ^ (q - 1) * positionPartial i ρ y) :
    Integrable (fun y => ζ y * (q * ρ y ^ (q - 1) * transportDerivative ρ y)) ∧
      ∫ y, ζ y * (q * ρ y ^ (q - 1) * transportDerivative ρ y) = 0 := by
  have hgs : ContDiff ℝ (⊤ : ℕ∞) fun y => ρ y ^ q := contDiff_rpow_of_pos hρ hpos q
  have hgd : ∀ i, Integrable (coordPartial (Sum.inr i) fun y => ρ y ^ q) := fun i => by
    have : (coordPartial (Sum.inr i) fun y => ρ y ^ q) =
        fun y => q * (ρ y ^ (q - 1) * positionPartial i ρ y) := by
      funext y
      rw [coordPartial_rpow (Sum.inr i) ((hρ.differentiable (by simp)) y) (hpos y) q]
      simp only [positionPartial_eq]
      ring
    rw [this]
    exact (hgrad i).const_mul q
  have hζi : ∀ i, ContDiff ℝ (⊤ : ℕ∞) fun y => y.1 i * ζ y := fun i =>
    (contDiff_fst_apply i).mul hζ
  have hint : ∀ i, Integrable fun y => (y.1 i * ζ y) * coordPartial (Sum.inr i)
      (fun y => ρ y ^ q) y := fun i =>
    integrable_cutoff_mul (hζi i).continuous (fun y => hB i y) (hgd i)
  have hzero : ∀ i, ∫ y, (y.1 i * ζ y) * coordPartial (Sum.inr i) (fun y => ρ y ^ q) y = 0 :=
    fun i => by
    have hdz : ∀ y, coordPartial (Sum.inr i) (fun y => y.1 i * ζ y) y = 0 := fun y => by
      rw [coordPartial_mul (Sum.inr i) ((contDiff_fst_apply i).differentiable (by simp) y)
        ((hζ.differentiable (by simp)) y), coordPartial_inr_fst_apply, hζz]
      simp
    have := integral_cutoff_mul_coordPartial_eq_neg (hζi i) hgs (A := B) (fun y => hB i y)
      (Sum.inr i) (B := 0) (fun y => by rw [hdz]; simp) hpow (hgd i)
    simpa [hdz] using this
  simp_rw [cutoff_transport_eq_sum hρ hpos]
  exact ⟨integrable_finsetSum _ fun i _ => hint i, by
    rw [integral_finsetSum _ fun i _ => hint i]
    exact Finset.sum_eq_zero fun i _ => hzero i⟩

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
