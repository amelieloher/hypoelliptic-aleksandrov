module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Energy.Fields

/-!
# Integrability for the integrations by parts

The energy inequality and the smoothing estimates: the integrability of the slice
integrands, packaged as `SliceIntegrable`, gives the three integrability statements needed to
integrate `ρ^{q-1} ∂_c X` by parts, for every field `X` dominated by the gradient of `ρ` and `J`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ}

/-- The integrability of the slice integrands of the smoothing estimates used in the energy
inequality, for a
density `ρ`, a coefficient `β` and the flux `J = ρ β`. -/
structure SliceIntegrable (q : ℝ) (ρ : EvolutionAmbientState d → ℝ)
    (β J : EvolutionAmbientState d → PDE.Mat d) : Prop where
  pow : Integrable fun y => ρ y ^ q
  grad : Integrable fun y => ρ y ^ (q - 1) * gradNorm ρ y
  hess : Integrable fun y => ρ y ^ (q - 1) * hessNorm ρ y
  fisher : Integrable fun y => ρ y ^ (q - 2) * gradNormSq ρ y
  fluxGrad : Integrable fun y => ρ y ^ (q - 1) * coefficientGradNorm J y
  fluxHess : Integrable fun y => ρ y ^ (q - 1) * coefficientHessNorm J y
  fluxFisher : Integrable fun y => ρ y ^ (q - 2) * coefficientGradNormSq J y
  betaGradSq : Integrable fun y => ρ y ^ q * coefficientGradNormSq β y

variable {q : ℝ} {ρ : EvolutionAmbientState d → ℝ} {β J : EvolutionAmbientState d → PDE.Mat d}

theorem abs_rpow_mul_le {r s B X : ℝ} (hr : 0 < r) (hX : |X| ≤ B) :
    |r ^ s * X| ≤ r ^ s * B := by
  rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hr s)]
  exact mul_le_mul_of_nonneg_left hX (Real.rpow_pos_of_pos hr s).le

/-- The three integrability statements for the integration by parts of `ρ^{q-1} ∂_c X`. -/
theorem SliceIntegrable.triple (hS : SliceIntegrable q ρ β J) (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (hpos : ∀ y, 0 < ρ y) {X : EvolutionAmbientState d → ℝ} (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (c : Fin d ⊕ Fin d) {K1 K2 K3 K4 : ℝ} (h2 : 0 ≤ K2)
    (hXb : ∀ y, |X y| ≤ K1 * gradNorm ρ y + K2 * coefficientGradNorm J y)
    (hdXb : ∀ y, |coordPartial c X y| ≤ K3 * hessNorm ρ y + K4 * coefficientHessNorm J y) :
    Integrable (fun y => ρ y ^ (q - 1) * X y) ∧
      Integrable (fun y => ρ y ^ (q - 2) * coordPartial c ρ y * X y) ∧
      Integrable (fun y => ρ y ^ (q - 1) * coordPartial c X y) := by
  have hrc : ∀ s : ℝ, Continuous fun y => ρ y ^ s := fun s =>
    (contDiff_rpow_of_pos hρ hpos s).continuous
  refine ⟨?_, ?_, ?_⟩
  · refine integrable_of_abs_le (K := 1) ((hrc _).mul hX.continuous).aestronglyMeasurable
      ((hS.grad.const_mul K1).add (hS.fluxGrad.const_mul K2)) fun y => ?_
    refine (abs_rpow_mul_le (hpos y) (hXb y)).trans (le_of_eq ?_)
    simp only [Pi.add_apply]
    ring
  · refine integrable_of_abs_le (K := 1)
      (((hrc _).mul (continuous_coordPartial hρ c)).mul hX.continuous).aestronglyMeasurable
      (((hS.fisher.const_mul (K1 + K2 / 2))).add (hS.fluxFisher.const_mul (K2 / 2))) fun y => ?_
    have hP : 0 ≤ ρ y ^ (q - 2) := (Real.rpow_pos_of_pos (hpos y) _).le
    have hg := energy_abs_coordPartial_le_gradNorm c ρ y
    have hgn := gradNorm_nonneg ρ y
    have hcn := coefficientGradNorm_nonneg J y
    have e1 := sq_gradNorm ρ y
    have e2 := sq_coefficientGradNorm J y
    rw [abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos (hpos y) _)]
    have hb : |coordPartial c ρ y| * |X y| ≤ gradNorm ρ y *
        (K1 * gradNorm ρ y + K2 * coefficientGradNorm J y) :=
      mul_le_mul hg (hXb y) (abs_nonneg _) hgn
    have hc := mul_le_mul_of_nonneg_left hb hP
    rw [mul_assoc]
    refine hc.trans ?_
    simp only [Pi.add_apply]
    rw [← e1, ← e2]
    nlinarith [mul_nonneg (mul_nonneg hP h2) (sq_nonneg (gradNorm ρ y - coefficientGradNorm J y))]
  · refine integrable_of_abs_le (K := 1) ((hrc _).mul
      (continuous_coordPartial hX c)).aestronglyMeasurable
      ((hS.hess.const_mul K3).add (hS.fluxHess.const_mul K4)) fun y => ?_
    refine (abs_rpow_mul_le (hpos y) (hdXb y)).trans (le_of_eq ?_)
    simp only [Pi.add_apply]
    ring

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
