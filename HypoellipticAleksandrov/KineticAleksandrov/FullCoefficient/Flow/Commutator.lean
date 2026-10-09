module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Flow.SecondOrder

/-!
# The transport commutator identity for the Gaussian flow

The Gaussian flow estimates:
`(v · ∇_z) Φ_h = (λ h² / 2) Δ_z Φ_h - λ h ∇_z · ∇_v Φ_h`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ}

theorem flowKernel_funext {lam h : ℝ} (hl : 0 < lam) (hh : 0 < h) :
    (flowKernel lam h : EvolutionAmbientState d → ℝ) =
      fun y => flowConst lam h ^ d * gaussExp (flowA lam h) (flowB lam h) (flowC lam h) y :=
  funext fun y => flowKernel_eq hl hh y

theorem positionPartial_flowKernel {lam h : ℝ} (hl : 0 < lam) (hh : 0 < h) (i : Fin d)
    (y : EvolutionAmbientState d) :
    positionPartial i (flowKernel lam h) y = -flowConst lam h ^ d *
      (2 * flowA lam h * y.2 i + flowB lam h * y.1 i) *
      gaussExp (flowA lam h) (flowB lam h) (flowC lam h) y := by
  rw [positionPartial_eq_dirPartial, flowKernel_funext hl hh,
    dirPartial_const_mul_gaussExp]
  rfl

theorem positionPartial_positionPartial_flowKernel {lam h : ℝ} (hl : 0 < lam) (hh : 0 < h)
    (i : Fin d) (y : EvolutionAmbientState d) :
    positionPartial i (positionPartial i (flowKernel lam h)) y =
      flowConst lam h ^ d * ((2 * flowA lam h * y.2 i + flowB lam h * y.1 i) ^ 2
        - 2 * flowA lam h) * gaussExp (flowA lam h) (flowB lam h) (flowC lam h) y := by
  change dirPartial (Sum.inr i) (dirPartial (Sum.inr i) (flowKernel lam h)) y = _
  rw [flowKernel_funext hl hh, dirPartial_dirPartial_gaussExp]
  simp only [gen, genCoeff, ↓reduceIte]
  ring

theorem positionPartial_velocityPartial_flowKernel {lam h : ℝ} (hl : 0 < lam) (hh : 0 < h)
    (i : Fin d) (y : EvolutionAmbientState d) :
    positionPartial i (velocityPartial i (flowKernel lam h)) y =
      flowConst lam h ^ d * ((flowB lam h * y.2 i + 2 * flowC lam h * y.1 i) *
        (2 * flowA lam h * y.2 i + flowB lam h * y.1 i) - flowB lam h) *
        gaussExp (flowA lam h) (flowB lam h) (flowC lam h) y := by
  change dirPartial (Sum.inr i) (dirPartial (Sum.inl i) (flowKernel lam h)) y = _
  rw [flowKernel_funext hl hh, dirPartial_dirPartial_gaussExp]
  simp only [gen, genCoeff, ↓reduceIte]

/-- The Gaussian flow estimates, the transport commutator. -/
theorem transportDerivative_flowKernel {lam h : ℝ} (hl : 0 < lam) (hh : 0 < h)
    (y : EvolutionAmbientState d) :
    transportDerivative (flowKernel lam h) y =
      (lam * h ^ 2 / 2) * positionLaplacian (flowKernel lam h) y -
        lam * h * mixedDivergence (flowKernel lam h) y := by
  unfold transportDerivative positionLaplacian mixedDivergence
  simp_rw [positionPartial_positionPartial_flowKernel hl hh,
    positionPartial_velocityPartial_flowKernel hl hh, positionPartial_flowKernel hl hh]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold flowA flowB flowC
  field_simp
  ring

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
