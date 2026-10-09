module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Forward.Lines
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Forward.Joint

/-!
# Derivatives of the mollification of an admissible test function

For an admissible `φ` and a smooth probability kernel `ρ`, the mollification
`moll ρ Φ`, `Φ(τ, y) = φ(τ, y)`, is smooth and its partial derivatives are the mollifications of
the partial derivatives of `φ`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

open MeasureTheory Set

variable {d : ℕ} {T : ℝ} {φ : ℝ → EvolutionAmbientState d → ℝ}

/-- A smooth compactly supported probability density supported in the closed ball of radius `r`. -/
structure IsMollifierKernel (ρ : ℝ × EvolutionAmbientState d → ℝ) (r : ℝ) : Prop where
  /-- Smoothness. -/
  smooth : ContDiff ℝ (⊤ : ℕ∞) ρ
  /-- Compact support. -/
  compact : HasCompactSupport ρ
  /-- Non-negativity. -/
  nonneg : ∀ x, 0 ≤ ρ x
  /-- Unit mass. -/
  integral_eq_one : ∫ x, ρ x = 1
  /-- Support in the ball of radius `r`. -/
  vanishes : ∀ x, r < ‖x‖ → ρ x = 0

theorem IsMollifierKernel.integrable {ρ : ℝ × EvolutionAmbientState d → ℝ} {r : ℝ}
    (h : IsMollifierKernel ρ r) : Integrable ρ :=
  h.smooth.continuous.integrable_of_hasCompactSupport h.compact

variable {ρ : ℝ × EvolutionAmbientState d → ℝ} {r : ℝ}

theorem contDiff_moll_test (hρ : IsMollifierKernel ρ r) (hφ : IsAdmissibleTest T φ) :
    ContDiff ℝ (⊤ : ℕ∞) (moll ρ (testValue φ)) :=
  contDiff_moll hρ.smooth hρ.compact hφ.value.1

/-- The time partial of the mollification is the mollification of `∂_τ φ`. -/
theorem jointTimePartial_moll (hρ : IsMollifierKernel ρ r) (hφ : IsAdmissibleTest T φ)
    (x : ℝ × EvolutionAmbientState d) :
    jointTimePartial (moll ρ (testValue φ)) x = moll ρ (testTime φ) x := by
  obtain ⟨Cf, hCf⟩ := hφ.value.2
  obtain ⟨Cg, hCg⟩ := hφ.timeDeriv.2
  have h1 := hasDerivAt_line (((contDiff_moll_test hρ hφ).differentiable (by simp)) x)
    ((1 : ℝ), (0 : EvolutionAmbientState d))
  have h2 := hasDerivAt_moll_line hρ.integrable hφ.value.1 hφ.timeDeriv.1 (fun y => hCf y)
    (fun y => hCg y) ((1 : ℝ), (0 : EvolutionAmbientState d)) (hasDerivAt_line_time hφ) x
  exact h1.unique h2

theorem jointVelocityPartial_moll (hρ : IsMollifierKernel ρ r) (hφ : IsAdmissibleTest T φ)
    (i : Fin d) (x : ℝ × EvolutionAmbientState d) :
    jointVelocityPartial i (moll ρ (testValue φ)) x = moll ρ (testVelocity φ i) x := by
  obtain ⟨Cf, hCf⟩ := hφ.value.2
  obtain ⟨Cg, hCg⟩ := (hφ.velocityGrad i).2
  have h1 := hasDerivAt_line (((contDiff_moll_test hρ hφ).differentiable (by simp)) x)
    ((0 : ℝ), ((Pi.single i 1 : PDE.Vec d), (0 : PDE.Vec d)))
  have h2 := hasDerivAt_moll_line hρ.integrable hφ.value.1 (hφ.velocityGrad i).1
    (fun y => hCf y) (fun y => hCg y)
    ((0 : ℝ), ((Pi.single i 1 : PDE.Vec d), (0 : PDE.Vec d))) (hasDerivAt_line_velocity hφ i) x
  exact h1.unique h2

theorem jointPositionPartial_moll (hρ : IsMollifierKernel ρ r) (hφ : IsAdmissibleTest T φ)
    (i : Fin d) (x : ℝ × EvolutionAmbientState d) :
    jointPositionPartial i (moll ρ (testValue φ)) x = moll ρ (testPosition φ i) x := by
  obtain ⟨Cf, hCf⟩ := hφ.value.2
  obtain ⟨Cg, hCg⟩ := (hφ.positionGrad i).2
  have h1 := hasDerivAt_line (((contDiff_moll_test hρ hφ).differentiable (by simp)) x)
    ((0 : ℝ), ((0 : PDE.Vec d), (Pi.single i 1 : PDE.Vec d)))
  have h2 := hasDerivAt_moll_line hρ.integrable hφ.value.1 (hφ.positionGrad i).1
    (fun y => hCf y) (fun y => hCg y)
    ((0 : ℝ), ((0 : PDE.Vec d), (Pi.single i 1 : PDE.Vec d))) (hasDerivAt_line_position hφ i) x
  exact h1.unique h2

theorem jointVelocityPartial_velocityPartial_moll (hρ : IsMollifierKernel ρ r)
    (hφ : IsAdmissibleTest T φ) (i j : Fin d) (x : ℝ × EvolutionAmbientState d) :
    jointVelocityPartial i (jointVelocityPartial j (moll ρ (testValue φ))) x =
      moll ρ (testHessian φ i j) x := by
  have hfun : jointVelocityPartial j (moll ρ (testValue φ)) = moll ρ (testVelocity φ j) :=
    funext fun y => jointVelocityPartial_moll hρ hφ j y
  rw [hfun]
  obtain ⟨Cf, hCf⟩ := (hφ.velocityGrad j).2
  obtain ⟨Cg, hCg⟩ := (hφ.velocityHess i j).2
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (moll ρ (testVelocity φ j)) :=
    contDiff_moll hρ.smooth hρ.compact (hφ.velocityGrad j).1
  have h1 := hasDerivAt_line ((hsm.differentiable (by simp)) x)
    ((0 : ℝ), ((Pi.single i 1 : PDE.Vec d), (0 : PDE.Vec d)))
  have h2 := hasDerivAt_moll_line hρ.integrable (hφ.velocityGrad j).1 (hφ.velocityHess i j).1
    (fun y => hCf y) (fun y => hCg y)
    ((0 : ℝ), ((Pi.single i 1 : PDE.Vec d), (0 : PDE.Vec d))) (hasDerivAt_line_hessian hφ i j) x
  exact h1.unique h2

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
