module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.Heat
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.FisherBeta

/-!
# The smoothing estimates: smoothness, differentiation under the integral, heat equation

The smoothing estimates: `r = m_h` and `(Fm)_h` are smooth, derivatives
may be taken under the integral sign in `y` and in `h`, with `∂_h r = M^h : D² r` and
`∂_h (Fm)_h = M^h : D² (Fm)_h`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ} {lam Lam : ℝ} (Φ : SmoothingKernelFamily d lam) {h : ℝ}
  {F : EvolutionAmbientState d → PDE.Mat d} (m : Measure (EvolutionAmbientState d))
  [IsFiniteMeasure m]

/-- First partial derivatives of `r` may be taken under the integral sign. -/
theorem coordPartial_smoothDensity (hh : 0 < h) (c : Fin d ⊕ Fin d)
    (y : EvolutionAmbientState d) :
    coordPartial c (smoothDensity Φ h m) y = ∫ a, coordPartial c (Φ.kernel h) (y - a) ∂m := by
  rw [smoothDensity_eq, coordPartial_smoothWeighted hh measurable_const (Cf := 1)
    (fun _ => by simp) c]
  simp [wconv]

/-- Second partial derivatives of `r` may be taken under the integral sign. -/
theorem coordPartial₂_smoothDensity (hh : 0 < h) (c c' : Fin d ⊕ Fin d)
    (y : EvolutionAmbientState d) :
    coordPartial c' (coordPartial c (smoothDensity Φ h m)) y =
      ∫ a, coordPartial c' (coordPartial c (Φ.kernel h)) (y - a) ∂m := by
  rw [smoothDensity_eq, coordPartial₂_smoothWeighted hh measurable_const (Cf := 1)
    (fun _ => by simp) c c']
  simp [wconv]

/-- First partial derivatives of the flux entries may be taken under the integral sign. -/
theorem coordPartial_smoothFluxEntry (hlam : 0 < lam) (hF : IsAdmissibleCoefficient lam Lam F)
    (hh : 0 < h) (i j : Fin d) (c : Fin d ⊕ Fin d) (y : EvolutionAmbientState d) :
    coordPartial c (smoothFluxEntry Φ h F m i j) y =
      ∫ a, coordPartial c (Φ.kernel h) (y - a) * F a i j ∂m := by
  rw [smoothFluxEntry_eq, coordPartial_smoothWeighted hh (hF.measurable i j)
    (fun a => hF.abs_apply_le hlam a i j) c]
  simp only [wconv, smul_eq_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun a => mul_comm _ _)

/-- Second partial derivatives of the flux entries may be taken under the integral sign. -/
theorem coordPartial₂_smoothFluxEntry (hlam : 0 < lam) (hF : IsAdmissibleCoefficient lam Lam F)
    (hh : 0 < h) (i j : Fin d) (c c' : Fin d ⊕ Fin d) (y : EvolutionAmbientState d) :
    coordPartial c' (coordPartial c (smoothFluxEntry Φ h F m i j)) y =
      ∫ a, coordPartial c' (coordPartial c (Φ.kernel h)) (y - a) * F a i j ∂m := by
  rw [smoothFluxEntry_eq, coordPartial₂_smoothWeighted hh (hF.measurable i j)
    (fun a => hF.abs_apply_le hlam a i j) c c']
  simp only [wconv, smul_eq_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun a => mul_comm _ _)

/-- Heat equation for `r`: `∂_h r = M^h : D² r`. -/
theorem hasDerivAt_smoothDensity (hh : 0 < h) (y : EvolutionAmbientState d) :
    HasDerivAt (fun s => smoothDensity Φ s m y)
      (heatOperator lam h (smoothDensity Φ h m) y) h := by
  simp only [smoothDensity_eq]
  exact hasDerivAt_smoothWeighted Φ hh measurable_const (Cf := 1) (fun _ => by simp) y

/-- The `h`-derivative of `r` is the integral of the `h`-derivative of the kernel. -/
theorem heatOperator_smoothDensity (hh : 0 < h) (y : EvolutionAmbientState d) :
    heatOperator lam h (smoothDensity Φ h m) y =
      ∫ a, heatOperator lam h (Φ.kernel h) (y - a) ∂m := by
  rw [smoothDensity_eq]
  change heatOperator lam h (wconv (Φ.kernel h) (fun _ => 1) m) y = _
  rw [heatOperator_wconv (Φ.isBoundedSmooth hh) measurable_const (Cf := 1) (fun _ => by simp)]
  simp [wconv]

/-- Heat equation for the flux entries: `∂_h (Fm)_h = M^h : D² (Fm)_h`. -/
theorem hasDerivAt_smoothFluxEntry (hlam : 0 < lam) (hF : IsAdmissibleCoefficient lam Lam F)
    (hh : 0 < h) (i j : Fin d) (y : EvolutionAmbientState d) :
    HasDerivAt (fun s => smoothFluxEntry Φ s F m i j y)
      (heatOperator lam h (smoothFluxEntry Φ h F m i j) y) h := by
  simp only [smoothFluxEntry_eq]
  exact hasDerivAt_smoothWeighted Φ hh (hF.measurable i j)
    (fun a => hF.abs_apply_le hlam a i j) y

/-- The `h`-derivative of the flux entries is the integral of the `h`-derivative of the kernel. -/
theorem heatOperator_smoothFluxEntry (hlam : 0 < lam) (hF : IsAdmissibleCoefficient lam Lam F)
    (hh : 0 < h) (i j : Fin d) (y : EvolutionAmbientState d) :
    heatOperator lam h (smoothFluxEntry Φ h F m i j) y =
      ∫ a, heatOperator lam h (Φ.kernel h) (y - a) * F a i j ∂m := by
  rw [smoothFluxEntry_eq]
  change heatOperator lam h (wconv (Φ.kernel h) (fun a => F a i j) m) y = _
  rw [heatOperator_wconv (Φ.isBoundedSmooth hh) (hF.measurable i j)
    (fun a => hF.abs_apply_le hlam a i j)]
  simp only [wconv, smul_eq_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun a => mul_comm _ _)

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
