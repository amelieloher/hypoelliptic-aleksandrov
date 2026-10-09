module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.FisherBeta
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Coordinate derivatives of `u^s * w`

For a smooth positive function `u` and a smooth function `w` on phase space, the first and second
coordinate partials of `u^s * w`. These are the chain-rule identities behind the `W^{2,1}`
membership of `r^q` and `r^q |β|²` in the integrability list of the smoothing estimates.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open Real

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ}

theorem coordPartial_add {f g : EvolutionAmbientState d → ℝ} {y : EvolutionAmbientState d}
    (c : Fin d ⊕ Fin d) (hf : DifferentiableAt ℝ f y) (hg : DifferentiableAt ℝ g y) :
    coordPartial c (fun y => f y + g y) y = coordPartial c f y + coordPartial c g y := by
  unfold coordPartial
  have e : (fun y => f y + g y) = f + g := rfl
  rw [e, (hf.hasFDerivAt.add hg.hasFDerivAt).fderiv]
  simp

theorem coordPartial_const_mul' {f : EvolutionAmbientState d → ℝ} {y : EvolutionAmbientState d}
    (c : Fin d ⊕ Fin d) (a : ℝ) (hf : DifferentiableAt ℝ f y) :
    coordPartial c (fun y => a * f y) y = a * coordPartial c f y := by
  unfold coordPartial
  rw [(hf.hasFDerivAt.const_mul a).fderiv]
  simp

theorem coordPartial_rpow {u : EvolutionAmbientState d → ℝ} {y : EvolutionAmbientState d}
    (c : Fin d ⊕ Fin d) (hu : DifferentiableAt ℝ u y) (h0 : 0 < u y) (s : ℝ) :
    coordPartial c (fun y => u y ^ s) y = s * u y ^ (s - 1) * coordPartial c u y := by
  unfold coordPartial
  rw [(hu.hasFDerivAt.rpow_const (p := s) (Or.inl h0.ne')).fderiv]
  simp

theorem coordPartial_sq {f : EvolutionAmbientState d → ℝ} {y : EvolutionAmbientState d}
    (c : Fin d ⊕ Fin d) (hf : DifferentiableAt ℝ f y) :
    coordPartial c (fun y => f y ^ 2) y = 2 * f y * coordPartial c f y := by
  unfold coordPartial
  rw [(hf.hasFDerivAt.pow 2).fderiv]
  simp

theorem contDiff_rpow_of_pos {u : EvolutionAmbientState d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hpos : ∀ y, 0 < u y) (s : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (fun y => u y ^ s) :=
  contDiff_iff_contDiffAt.2 fun y =>
    (contDiffAt_rpow_const_of_ne (p := s) (hpos y).ne').comp y hu.contDiffAt

section Smooth

variable {u w : EvolutionAmbientState d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
  (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hpos : ∀ y, 0 < u y)

include hu hw hpos in
theorem contDiff_rpow_mul (s : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (fun y => u y ^ s * w y) :=
  (contDiff_rpow_of_pos hu hpos _).mul hw

include hu hw hpos in
theorem coordPartial_rpow_mul (s : ℝ) (c : Fin d ⊕ Fin d) :
    coordPartial c (fun y => u y ^ s * w y) = fun y =>
      s * u y ^ (s - 1) * coordPartial c u y * w y + u y ^ s * coordPartial c w y := by
  funext y
  have hu' : DifferentiableAt ℝ u y := (hu.differentiable (by simp)) y
  have hw' : DifferentiableAt ℝ w y := (hw.differentiable (by simp)) y
  have hp : DifferentiableAt ℝ (fun y => u y ^ s) y :=
    ((contDiff_rpow_of_pos hu hpos _).differentiable (by simp)) y
  rw [coordPartial_mul c hp hw', coordPartial_rpow c hu' (hpos y)]
  ring

include hu hw hpos in
theorem coordPartial₂_rpow_mul (s : ℝ) (c c' : Fin d ⊕ Fin d) (y : EvolutionAmbientState d) :
    coordPartial c' (coordPartial c (fun y => u y ^ s * w y)) y =
      s * (s - 1) * u y ^ (s - 2) * coordPartial c' u y * coordPartial c u y * w y +
      s * u y ^ (s - 1) * coordPartial c' (coordPartial c u) y * w y +
      s * u y ^ (s - 1) * coordPartial c u y * coordPartial c' w y +
      s * u y ^ (s - 1) * coordPartial c' u y * coordPartial c w y +
      u y ^ s * coordPartial c' (coordPartial c w) y := by
  rw [coordPartial_rpow_mul hu hw hpos s c]
  have hu1 : ContDiff ℝ (⊤ : ℕ∞) (coordPartial c u) := contDiff_coordPartial hu c
  have hw1 : ContDiff ℝ (⊤ : ℕ∞) (coordPartial c w) := contDiff_coordPartial hw c
  have hd : ∀ {f : EvolutionAmbientState d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) f →
      DifferentiableAt ℝ f y := fun hf => (hf.differentiable (by simp)) y
  have hrp : ContDiff ℝ (⊤ : ℕ∞) (fun y => u y ^ (s - 1)) :=
    contDiff_rpow_of_pos hu hpos _
  have hrp' : ContDiff ℝ (⊤ : ℕ∞) (fun y => u y ^ s) := contDiff_rpow_of_pos hu hpos _
  have t1 : DifferentiableAt ℝ (fun y => s * u y ^ (s - 1) * coordPartial c u y * w y) y :=
    hd (((contDiff_const.mul hrp).mul hu1).mul hw)
  have t2 : DifferentiableAt ℝ (fun y => u y ^ s * coordPartial c w y) y := hd (hrp'.mul hw1)
  rw [coordPartial_add c' t1 t2]
  have a1 : coordPartial c' (fun y => s * u y ^ (s - 1) * coordPartial c u y * w y) y =
      (s * (s - 1) * u y ^ (s - 2) * coordPartial c' u y) * coordPartial c u y * w y +
      s * u y ^ (s - 1) * coordPartial c' (coordPartial c u) y * w y +
      s * u y ^ (s - 1) * coordPartial c u y * coordPartial c' w y := by
    have e1 : DifferentiableAt ℝ (fun y => s * u y ^ (s - 1) * coordPartial c u y) y :=
      hd ((contDiff_const.mul hrp).mul hu1)
    rw [coordPartial_mul c' e1 (hd hw)]
    have e2 : DifferentiableAt ℝ (fun y => s * u y ^ (s - 1)) y := hd (contDiff_const.mul hrp)
    rw [coordPartial_mul c' e2 (hd hu1), coordPartial_const_mul' c' s (hd hrp),
      coordPartial_rpow c' (hd hu) (hpos y) (s - 1)]
    have : s - 1 - 1 = s - 2 := by ring
    rw [this]
    ring
  have a2 : coordPartial c' (fun y => u y ^ s * coordPartial c w y) y =
      s * u y ^ (s - 1) * coordPartial c' u y * coordPartial c w y +
      u y ^ s * coordPartial c' (coordPartial c w) y := by
    rw [coordPartial_mul c' (hd hrp') (hd hw1), coordPartial_rpow c' (hd hu) (hpos y) s]
    ring
  rw [a1, a2]
  ring

end Smooth

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
