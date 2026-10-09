module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.Coordinates

/-!
# Coordinate partials of the reflected translate `y' ↦ F(y - y')`

Chain rule for the test function `y' ↦ Φ_h(y - y')` of the smoothed equation: each first partial
derivative changes sign and each second partial derivative does not, in terms of the partials
of `F` evaluated at `y - y'` (`Calculus.lean` partials, via the coordinate partials).
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ}

theorem coordPartial_sub_comp {F : EvolutionAmbientState d → ℝ} (hF : Differentiable ℝ F)
    (c : Fin d ⊕ Fin d) (y y' : EvolutionAmbientState d) :
    coordPartial c (fun z => F (y - z)) y' = -coordPartial c F (y - y') := by
  have h1 : HasFDerivAt (fun z => F (y - z)) (-(fderiv ℝ F (y - y'))) y' := by
    have := (hF (y - y')).hasFDerivAt.comp y' ((hasFDerivAt_id y').const_sub y)
    simpa [Function.comp_def] using this
  unfold coordPartial
  rw [h1.fderiv]
  simp

theorem coordPartial_sub_comp₂ {F : EvolutionAmbientState d → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (c c' : Fin d ⊕ Fin d) (y y' : EvolutionAmbientState d) :
    coordPartial c' (coordPartial c (fun z => F (y - z))) y' =
      coordPartial c' (coordPartial c F) (y - y') := by
  have h1 : coordPartial c (fun z => F (y - z)) =
      fun z => (fun w => -coordPartial c F w) (y - z) := by
    funext z
    rw [coordPartial_sub_comp (hF.differentiable (by simp))]
  rw [h1]
  have hd : Differentiable ℝ (fun w => -coordPartial c F w) :=
    (differentiable_coordPartial hF c).neg
  rw [coordPartial_sub_comp hd]
  have : coordPartial c' (fun w => -coordPartial c F w) =
      fun w => -coordPartial c' (coordPartial c F) w := by
    funext w
    unfold coordPartial
    rw [fderiv_fun_neg]
    simp
  rw [this]
  simp

theorem coordPartial_const_mul {G : EvolutionAmbientState d → ℝ} (hG : Differentiable ℝ G)
    (k : ℝ) (c : Fin d ⊕ Fin d) (y : EvolutionAmbientState d) :
    coordPartial c (fun z => k * G z) y = k * coordPartial c G y := by
  unfold coordPartial
  rw [fderiv_const_mul (hG y)]
  simp

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
