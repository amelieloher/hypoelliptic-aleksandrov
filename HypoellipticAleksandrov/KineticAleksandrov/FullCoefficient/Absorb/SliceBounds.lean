module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Absorb.TauDeriv

/-!
# Supremum bounds for the slice integrals `∫ r_h^q`

The absorption estimate: `I(h) = ∫ ρ_h(τ₁)^q ≤ ‖ρ_h‖_∞^{q-1} ‖ρ_h‖_1 ≤
c^{q-1} h^{-2d(q-1)}` for a slice of mass at most `1`, and `F ≤ d Λ² E`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ} {lam Lam : ℝ} (Φ : SmoothingKernelFamily d lam) {h q : ℝ}

theorem supConst_nonneg (hh : 0 < h) : 0 ≤ Φ.supConst := by
  have h1 := Φ.le_sup hh 0
  have h2 := Φ.pos hh 0
  have h3 : 0 < (h ^ (2 * d))⁻¹ := by positivity
  by_contra hc
  rw [not_le] at hc
  nlinarith [mul_neg_of_neg_of_pos hc h3]

theorem integral_smoothDensity_pow_le (m : Measure (EvolutionAmbientState d))
    [IsFiniteMeasure m] (hm : m.real Set.univ ≤ 1) (hh : 0 < h) (hq : 1 < q) :
    Integrable (fun y => smoothDensity Φ h m y ^ q) ∧
      ∫ y, smoothDensity Φ h m y ^ q ≤ (Φ.supConst * (h ^ (2 * d))⁻¹) ^ (q - 1) := by
  have hc := supConst_nonneg Φ hh
  set R : ℝ := Φ.supConst * (h ^ (2 * d))⁻¹ with hR
  have hR0 : 0 ≤ R := by positivity
  have hpt : ∀ y, smoothDensity Φ h m y ^ q ≤ R ^ (q - 1) * smoothDensity Φ h m y := by
    intro y
    have hr0 := smoothDensity_nonneg Φ m hh y
    have hrR : smoothDensity Φ h m y ≤ R := by
      refine (smoothDensity_le Φ m hh y).trans ?_
      calc _ ≤ Φ.supConst * (h ^ (2 * d))⁻¹ * 1 :=
            mul_le_mul_of_nonneg_left hm (by positivity)
        _ = R := mul_one _
    calc smoothDensity Φ h m y ^ q = smoothDensity Φ h m y ^ (q - 1) * smoothDensity Φ h m y := by
          rw [← Real.rpow_add_one' hr0 (by linarith : q - 1 + 1 ≠ 0)]; ring_nf
      _ ≤ R ^ (q - 1) * smoothDensity Φ h m y :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hr0 hrR (by linarith)) hr0
  have hint : Integrable (fun y => R ^ (q - 1) * smoothDensity Φ h m y) :=
    (integrable_smoothDensity Φ m hh).const_mul _
  have hcont : Continuous fun y => smoothDensity Φ h m y ^ q :=
    (continuous_smoothDensity Φ m hh).rpow_const fun _ => Or.inr (by linarith)
  have hnn : ∀ y, 0 ≤ smoothDensity Φ h m y ^ q := fun y =>
    Real.rpow_nonneg (smoothDensity_nonneg Φ m hh y) _
  refine ⟨hint.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_), ?_⟩
  · rw [Real.norm_eq_abs, abs_of_nonneg (hnn y)]; exact hpt y
  · calc _ ≤ ∫ y, R ^ (q - 1) * smoothDensity Φ h m y :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall hnn) hint
            (Filter.Eventually.of_forall hpt)
      _ = R ^ (q - 1) * m.real Set.univ := by
          rw [integral_const_mul, integral_smoothDensity Φ m hh]
      _ ≤ R ^ (q - 1) * 1 := mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg hR0 _)
      _ = _ := mul_one _

theorem supBound_eq (hh : 0 < h) (hc : 0 ≤ Φ.supConst) :
    (Φ.supConst * (h ^ (2 * d))⁻¹) ^ (q - 1) = Φ.supConst ^ (q - 1) * h ^ (-(2 * d * (q - 1))) := by
  rw [Real.mul_rpow hc (by positivity), Real.inv_rpow (by positivity)]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul hh.le, ← Real.rpow_neg (by positivity)]
  congr 2
  push_cast; ring

theorem integrandPowBeta_le (m : Measure (EvolutionAmbientState d)) [IsFiniteMeasure m]
    {F : EvolutionAmbientState d → PDE.Mat d} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hF : IsAdmissibleCoefficient lam Lam F) (hh : 0 < h) (y : EvolutionAmbientState d) :
    integrandPowBeta Φ h F m q y ≤ d * Lam ^ 2 * smoothDensity Φ h m y ^ q := by
  unfold integrandPowBeta
  have := frobeniusSq_smoothCoefficient_le Φ m hlam hLam hF hh y
  have h0 : 0 ≤ smoothDensity Φ h m y ^ q := Real.rpow_nonneg (smoothDensity_nonneg Φ m hh y) _
  nlinarith

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
