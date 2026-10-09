module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Calculus
public import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Joint space-time partial derivatives

For a function `G : ℝ × (Vec d × Vec d) → ℝ` of elapsed time `τ` and phase-space point
`y = (v, z)`, this module defines the joint partial derivatives and identifies the slice
derivatives of `FullCoefficient/Calculus.lean` (those of `fun y ↦ G (τ, y)`) with them.  It is
the calculus bridge of the forward equation of the Green slices.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ}

/-- The joint time partial `∂_τ G` of a function of `(τ, y)`. -/
def jointTimePartial (G : ℝ × EvolutionAmbientState d → ℝ)
    (q : ℝ × EvolutionAmbientState d) : ℝ :=
  fderiv ℝ G q (1, 0)

/-- The joint velocity partial `∂_{v_i} G` of a function of `(τ, (v, z))`. -/
def jointVelocityPartial (i : Fin d) (G : ℝ × EvolutionAmbientState d → ℝ)
    (q : ℝ × EvolutionAmbientState d) : ℝ :=
  fderiv ℝ G q (0, (Pi.single i 1, 0))

/-- The joint position partial `∂_{z_i} G` of a function of `(τ, (v, z))`. -/
def jointPositionPartial (i : Fin d) (G : ℝ × EvolutionAmbientState d → ℝ)
    (q : ℝ × EvolutionAmbientState d) : ℝ :=
  fderiv ℝ G q (0, (0, Pi.single i 1))

/-- Fixed directional derivatives of a smooth function are smooth. -/
theorem contDiff_fderiv_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : E → ℝ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) (w : E) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q => fderiv ℝ G q w) :=
  (hG.fderiv_right (m := (⊤ : ℕ∞)) (by norm_cast)).clm_apply contDiff_const

theorem contDiff_jointTimePartial {G : ℝ × EvolutionAmbientState d → ℝ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) : ContDiff ℝ (⊤ : ℕ∞) (jointTimePartial G) :=
  contDiff_fderiv_apply hG _

theorem contDiff_jointVelocityPartial {G : ℝ × EvolutionAmbientState d → ℝ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (jointVelocityPartial i G) :=
  contDiff_fderiv_apply hG _

theorem contDiff_jointPositionPartial {G : ℝ × EvolutionAmbientState d → ℝ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (jointPositionPartial i G) :=
  contDiff_fderiv_apply hG _

/-- The time derivative of a slice is the joint time partial. -/
theorem deriv_slice_time (G : ℝ × EvolutionAmbientState d → ℝ) (τ : ℝ)
    (y : EvolutionAmbientState d) (hG : DifferentiableAt ℝ G (τ, y)) :
    deriv (fun τ => G (τ, y)) τ = jointTimePartial G (τ, y) := by
  have h2 : HasDerivAt (fun τ : ℝ => (τ, y)) ((1 : ℝ), (0 : EvolutionAmbientState d)) τ :=
    (hasDerivAt_id τ).prodMk (hasDerivAt_const τ y)
  exact (HasFDerivAt.comp_hasDerivAt (f := fun τ : ℝ => (τ, y)) τ hG.hasFDerivAt h2).deriv

/-- Directional derivatives of a slice are joint directional derivatives. -/
theorem fderiv_slice (G : ℝ × EvolutionAmbientState d → ℝ) (τ : ℝ)
    (y : EvolutionAmbientState d) (hG : DifferentiableAt ℝ G (τ, y))
    (w : EvolutionAmbientState d) :
    fderiv ℝ (fun y' => G (τ, y')) y w = fderiv ℝ G (τ, y) (0, w) := by
  have h : HasFDerivAt (fun y' => G (τ, y'))
      ((fderiv ℝ G (τ, y)).comp (ContinuousLinearMap.inr ℝ ℝ (EvolutionAmbientState d))) y :=
    hG.hasFDerivAt.comp y (hasFDerivAt_prodMk_right τ y)
  rw [h.fderiv]
  rfl


/-- Velocity-direction derivatives of a two-variable slice are joint directional derivatives. -/
theorem fderiv_slice_velocity (G : ℝ × EvolutionAmbientState d → ℝ) (τ : ℝ)
    (v z : PDE.Vec d) (hG : DifferentiableAt ℝ G (τ, (v, z))) (w : PDE.Vec d) :
    fderiv ℝ (fun v' : PDE.Vec d => G (τ, (v', z))) v w = fderiv ℝ G (τ, (v, z)) (0, (w, 0)) := by
  have hm : HasFDerivAt (fun v' : PDE.Vec d => ((τ, (v', z)) : ℝ × EvolutionAmbientState d))
      ((ContinuousLinearMap.inr ℝ ℝ (EvolutionAmbientState d)).comp
        (ContinuousLinearMap.inl ℝ (PDE.Vec d) (PDE.Vec d))) v :=
    (hasFDerivAt_prodMk_right τ (v, z)).comp v (hasFDerivAt_prodMk_left v z)
  have h : HasFDerivAt (fun v' : PDE.Vec d => G (τ, (v', z))) _ v := hG.hasFDerivAt.comp v hm
  rw [h.fderiv]
  rfl

/-- Position-direction derivatives of a two-variable slice are joint directional derivatives. -/
theorem fderiv_slice_position (G : ℝ × EvolutionAmbientState d → ℝ) (τ : ℝ)
    (v z : PDE.Vec d) (hG : DifferentiableAt ℝ G (τ, (v, z))) (w : PDE.Vec d) :
    fderiv ℝ (fun z' : PDE.Vec d => G (τ, (v, z'))) z w = fderiv ℝ G (τ, (v, z)) (0, (0, w)) := by
  have hm : HasFDerivAt (fun z' : PDE.Vec d => ((τ, (v, z')) : ℝ × EvolutionAmbientState d))
      ((ContinuousLinearMap.inr ℝ ℝ (EvolutionAmbientState d)).comp
        (ContinuousLinearMap.inr ℝ (PDE.Vec d) (PDE.Vec d))) z :=
    (hasFDerivAt_prodMk_right τ (v, z)).comp z (hasFDerivAt_prodMk_right v z)
  have h : HasFDerivAt (fun z' : PDE.Vec d => G (τ, (v, z'))) _ z := hG.hasFDerivAt.comp z hm
  rw [h.fderiv]
  rfl

/-- The velocity partial of a slice is the joint velocity partial. -/
theorem velocityPartial_slice (G : ℝ × EvolutionAmbientState d → ℝ) (τ : ℝ)
    (y : EvolutionAmbientState d) (hG : DifferentiableAt ℝ G (τ, y)) (i : Fin d) :
    velocityPartial i (fun y' => G (τ, y')) y = jointVelocityPartial i G (τ, y) :=
  fderiv_slice G τ y hG _

/-- The position partial of a slice is the joint position partial. -/
theorem positionPartial_slice (G : ℝ × EvolutionAmbientState d → ℝ) (τ : ℝ)
    (y : EvolutionAmbientState d) (hG : DifferentiableAt ℝ G (τ, y)) (i : Fin d) :
    positionPartial i (fun y' => G (τ, y')) y = jointPositionPartial i G (τ, y) :=
  fderiv_slice G τ y hG _

/-- The second velocity partials of a slice of a smooth function are joint second partials. -/
theorem velocityPartial_velocityPartial_slice {G : ℝ × EvolutionAmbientState d → ℝ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (τ : ℝ) (y : EvolutionAmbientState d) (i j : Fin d) :
    velocityPartial i (velocityPartial j (fun y' => G (τ, y'))) y =
      jointVelocityPartial i (jointVelocityPartial j G) (τ, y) := by
  have hdiff : Differentiable ℝ G := hG.differentiable (by simp)
  have hfun : velocityPartial j (fun y' => G (τ, y')) =
      fun y' => jointVelocityPartial j G (τ, y') := by
    funext y'
    exact velocityPartial_slice G τ y' (hdiff _) j
  rw [hfun]
  exact velocityPartial_slice (jointVelocityPartial j G) τ y
    (((contDiff_jointVelocityPartial hG j).differentiable (by simp)) _) i

/-- Smooth joint functions have smooth slices. -/
theorem contDiff_slice {G : ℝ × EvolutionAmbientState d → ℝ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (τ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => G (τ, y)) :=
  hG.comp (contDiff_const.prodMk contDiff_id)

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
