module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Flow.Derivs

/-!
# First and second derivatives of the Gaussian kernel

For `Φ = K * gaussExp a b c` the first and second coordinate derivatives are the explicit
polynomial multiples
`∂_δ Φ = -K * gen δ * G` and `∂_δ' ∂_δ Φ = K * (gen δ * gen δ' - genCoeff δ δ') * G`.
These give the Laplacians and the mixed divergence of the flow kernel.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ}

theorem dirPartial_const (δ : Fin d ⊕ Fin d) (K : ℝ) (y : EvolutionAmbientState d) :
    dirPartial δ (fun _ => K) y = 0 := by
  simp [dirPartial]

theorem dirPartial_const_mul_gaussExp (a b c K : ℝ) (δ : Fin d ⊕ Fin d)
    (y : EvolutionAmbientState d) :
    dirPartial δ (fun y => K * gaussExp a b c y) y = -K * gen a b c δ y * gaussExp a b c y := by
  have := dirPartial_mul_gaussExp a b c δ (p := fun _ => K) (y := y) (differentiableAt_const K)
  simp only [dirPartial_const] at this
  rw [this]
  ring

theorem dirPartial_gen_const_mul (a b c K : ℝ) (δ δ' : Fin d ⊕ Fin d)
    (y : EvolutionAmbientState d) :
    dirPartial δ' (fun y => K * gen a b c δ y) y = K * genCoeff a b c δ δ' := by
  obtain ⟨L, hL, hv⟩ := hasFDerivAt_gen a b c δ y
  unfold dirPartial
  rw [(hL.const_mul K).fderiv]
  simp [hv]

theorem dirPartial_dirPartial_gaussExp (a b c K : ℝ) (δ δ' : Fin d ⊕ Fin d)
    (y : EvolutionAmbientState d) :
    dirPartial δ' (dirPartial δ (fun y => K * gaussExp a b c y)) y =
      K * (gen a b c δ y * gen a b c δ' y - genCoeff a b c δ δ') * gaussExp a b c y := by
  have h1 : dirPartial δ (fun y => K * gaussExp a b c y) =
      fun y => (-K * gen a b c δ y) * gaussExp a b c y := by
    funext z
    rw [dirPartial_const_mul_gaussExp]
  rw [h1]
  have hd : DifferentiableAt ℝ (fun y => -K * gen a b c δ y) y :=
    ((differentiable_gen a b c δ).const_mul (-K)) y
  rw [dirPartial_mul_gaussExp a b c δ' hd, dirPartial_gen_const_mul]
  ring

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
