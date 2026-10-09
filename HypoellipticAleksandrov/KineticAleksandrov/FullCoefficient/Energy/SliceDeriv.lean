module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Energy.SliceBound

/-!
# Partial derivatives of a jointly smooth family of slices

For `g : ℝ × ℝ^{2d} → ℝ` smooth, the `y`-partials and the `τ`-derivative of the slices
`g τ = g (τ, ·)` are given by the Fréchet derivative of `g` and are jointly continuous.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ} {g : ℝ → EvolutionAmbientState d → ℝ}

theorem coordPartial_slice_of_differentiableAt {τ : ℝ} {y : EvolutionAmbientState d}
    (hg : DifferentiableAt ℝ (fun p : ℝ × EvolutionAmbientState d => g p.1 p.2) (τ, y))
    (c : Fin d ⊕ Fin d) :
    coordPartial c (g τ) y =
      fderiv ℝ (fun p : ℝ × EvolutionAmbientState d => g p.1 p.2) (τ, y) (0, coordDir c) := by
  have hd : HasFDerivAt (fun y : EvolutionAmbientState d => ((τ, y) : ℝ × EvolutionAmbientState d))
      ((0 : EvolutionAmbientState d →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ _)) y :=
    (hasFDerivAt_const τ y).prodMk (hasFDerivAt_id y)
  have hc : HasFDerivAt (g τ) ((fderiv ℝ (fun p : ℝ × EvolutionAmbientState d => g p.1 p.2)
      (τ, y)).comp ((0 : EvolutionAmbientState d →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ _))) y :=
    hg.hasFDerivAt.comp y hd
  rw [coordPartial, hc.fderiv]
  simp

theorem coordPartial_slice (hg : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × EvolutionAmbientState d =>
    g p.1 p.2)) (c : Fin d ⊕ Fin d) (τ : ℝ) (y : EvolutionAmbientState d) :
    coordPartial c (g τ) y =
      fderiv ℝ (fun p : ℝ × EvolutionAmbientState d => g p.1 p.2) (τ, y) (0, coordDir c) :=
  coordPartial_slice_of_differentiableAt (hg.differentiable (by simp) (τ, y)) c

theorem deriv_slice (hg : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × EvolutionAmbientState d =>
    g p.1 p.2)) (τ : ℝ) (y : EvolutionAmbientState d) :
    deriv (fun τ' => g τ' y) τ =
      fderiv ℝ (fun p : ℝ × EvolutionAmbientState d => g p.1 p.2) (τ, y) (1, 0) := by
  have hd : HasDerivAt (fun τ' : ℝ => ((τ', y) : ℝ × EvolutionAmbientState d)) ((1, 0) :
      ℝ × EvolutionAmbientState d) τ :=
    (hasDerivAt_id τ).prodMk (hasDerivAt_const τ y)
  have := ((hg.differentiable (by simp) (τ, y)).hasFDerivAt).comp_hasDerivAt τ hd
  exact this.deriv

theorem hasDerivAt_slice (hg : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × EvolutionAmbientState d =>
    g p.1 p.2)) (τ : ℝ) (y : EvolutionAmbientState d) :
    HasDerivAt (fun τ' => g τ' y) (deriv (fun τ' => g τ' y) τ) τ := by
  have hd : HasDerivAt (fun τ' : ℝ => ((τ', y) : ℝ × EvolutionAmbientState d)) ((1, 0) :
      ℝ × EvolutionAmbientState d) τ :=
    (hasDerivAt_id τ).prodMk (hasDerivAt_const τ y)
  exact (((hg.differentiable (by simp) (τ, y)).hasFDerivAt).comp_hasDerivAt τ hd).differentiableAt
    |>.hasDerivAt

theorem continuous_coordPartial_slice (hg : ContDiff ℝ (⊤ : ℕ∞)
    (fun p : ℝ × EvolutionAmbientState d => g p.1 p.2)) (c : Fin d ⊕ Fin d) :
    Continuous fun p : ℝ × EvolutionAmbientState d => coordPartial c (g p.1) p.2 := by
  have : (fun p : ℝ × EvolutionAmbientState d => coordPartial c (g p.1) p.2) = fun p =>
      fderiv ℝ (fun p : ℝ × EvolutionAmbientState d => g p.1 p.2) p (0, coordDir c) :=
    funext fun p => coordPartial_slice hg c p.1 p.2
  rw [this]
  exact (hg.continuous_fderiv (by simp)).clm_apply continuous_const

theorem continuous_deriv_slice (hg : ContDiff ℝ (⊤ : ℕ∞)
    (fun p : ℝ × EvolutionAmbientState d => g p.1 p.2)) :
    Continuous fun p : ℝ × EvolutionAmbientState d => deriv (fun τ' => g τ' p.2) p.1 := by
  have : (fun p : ℝ × EvolutionAmbientState d => deriv (fun τ' => g τ' p.2) p.1) = fun p =>
      fderiv ℝ (fun p : ℝ × EvolutionAmbientState d => g p.1 p.2) p (1, 0) :=
    funext fun p => deriv_slice hg p.1 p.2
  rw [this]
  exact (hg.continuous_fderiv (by simp)).clm_apply continuous_const

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
