module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Flow.Mass
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Coordinate derivatives of the Gaussian exponential

Directional derivatives of `gaussExp a b c = exp (-quadForm a b c)` along the coordinate
directions of phase space. A direction is `δ : Fin d ⊕ Fin d`: `inl i` is the velocity direction
`e_i` and `inr i` the position direction. The Leibniz rule
`∂_δ (p * G) = (∂_δ p - p * ∂_δ Q) * G` and the constancy of the second derivatives of `Q` are
the two inputs of the polynomial calculus used for the Gaussian flow estimates.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open Real

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ}

/-- The coordinate directions of phase space `y = (v, z)`. -/
def vecDir (δ : Fin d ⊕ Fin d) : EvolutionAmbientState d :=
  Sum.elim (fun i => ((Pi.single i 1 : PDE.Vec d), (0 : PDE.Vec d)))
    (fun i => ((0 : PDE.Vec d), (Pi.single i 1 : PDE.Vec d))) δ

/-- The partial derivative in a coordinate direction. -/
def dirPartial (δ : Fin d ⊕ Fin d) (F : EvolutionAmbientState d → ℝ)
    (y : EvolutionAmbientState d) : ℝ :=
  fderiv ℝ F y (vecDir δ)

theorem velocityPartial_eq_dirPartial (i : Fin d) (F : EvolutionAmbientState d → ℝ)
    (y : EvolutionAmbientState d) : velocityPartial i F y = dirPartial (Sum.inl i) F y := rfl

theorem positionPartial_eq_dirPartial (i : Fin d) (F : EvolutionAmbientState d → ℝ)
    (y : EvolutionAmbientState d) : positionPartial i F y = dirPartial (Sum.inr i) F y := rfl

/-- The `i`-th velocity coordinate as a continuous linear functional. -/
def coordV (i : Fin d) : EvolutionAmbientState d →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ (PDE.Vec d) (PDE.Vec d))

/-- The `i`-th position coordinate as a continuous linear functional. -/
def coordZ (i : Fin d) : EvolutionAmbientState d →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ (PDE.Vec d) (PDE.Vec d))

@[simp] theorem coordV_apply (i : Fin d) (y : EvolutionAmbientState d) : coordV i y = y.1 i := rfl
@[simp] theorem coordZ_apply (i : Fin d) (y : EvolutionAmbientState d) : coordZ i y = y.2 i := rfl

/-- The gradient of the quadratic form `Q` of the Gaussian exponential in the direction `δ`. -/
def gen (a b c : ℝ) : Fin d ⊕ Fin d → EvolutionAmbientState d → ℝ
  | Sum.inl i, y => b * y.2 i + 2 * c * y.1 i
  | Sum.inr i, y => 2 * a * y.2 i + b * y.1 i

/-- The (constant) second derivative of `Q`: `∂_δ' ∂_δ Q`. -/
def genCoeff (a b c : ℝ) : Fin d ⊕ Fin d → Fin d ⊕ Fin d → ℝ
  | Sum.inl i, Sum.inl j => if j = i then 2 * c else 0
  | Sum.inl i, Sum.inr j => if j = i then b else 0
  | Sum.inr i, Sum.inl j => if j = i then b else 0
  | Sum.inr i, Sum.inr j => if j = i then 2 * a else 0

theorem hasFDerivAt_quadForm (a b c : ℝ) (y : EvolutionAmbientState d) :
    HasFDerivAt (quadForm a b c)
      (∑ i, ((a * (2 * y.2 i)) • coordZ i + b • (y.1 i • coordZ i + y.2 i • coordV i)
        + (c * (2 * y.1 i)) • coordV i)) y := by
  unfold quadForm
  refine HasFDerivAt.fun_sum fun i _ => ?_
  have h1 := (coordV i).hasFDerivAt (x := y)
  have h2 := (coordZ i).hasFDerivAt (x := y)
  have := (((h2.pow 2).const_mul a).add ((h2.mul h1).const_mul b)).add ((h1.pow 2).const_mul c)
  convert this using 1
  · funext z
    simp [mul_assoc]
  · refine ContinuousLinearMap.ext fun z => ?_
    simp
    ring

theorem dirPartial_quadForm (a b c : ℝ) (δ : Fin d ⊕ Fin d) (y : EvolutionAmbientState d) :
    dirPartial δ (quadForm a b c) y = gen a b c δ y := by
  unfold dirPartial
  rw [(hasFDerivAt_quadForm a b c y).fderiv]
  rcases δ with i | i
  · simp [vecDir, gen, Pi.single_apply, Finset.sum_add_distrib]
    ring
  · simp [vecDir, gen, Pi.single_apply, Finset.sum_add_distrib]
    ring

theorem contDiff_quadForm (a b c : ℝ) (n : WithTop ℕ∞) :
    ContDiff ℝ n (quadForm a b c : EvolutionAmbientState d → ℝ) := by
  unfold quadForm
  refine ContDiff.sum fun i _ => ?_
  have h1 : ContDiff ℝ n (fun y : EvolutionAmbientState d => y.1 i) := (coordV i).contDiff
  have h2 : ContDiff ℝ n (fun y : EvolutionAmbientState d => y.2 i) := (coordZ i).contDiff
  fun_prop

theorem contDiff_gaussExp (a b c : ℝ) (n : WithTop ℕ∞) :
    ContDiff ℝ n (gaussExp a b c : EvolutionAmbientState d → ℝ) :=
  Real.contDiff_exp.comp (contDiff_quadForm a b c n).neg

theorem hasFDerivAt_gen (a b c : ℝ) (δ : Fin d ⊕ Fin d) (y : EvolutionAmbientState d) :
    ∃ L : EvolutionAmbientState d →L[ℝ] ℝ, HasFDerivAt (gen a b c δ) L y ∧
      ∀ δ', L (vecDir δ') = genCoeff a b c δ δ' := by
  rcases δ with i | i
  · refine ⟨b • coordZ i + (2 * c) • coordV i, ?_, ?_⟩
    · have := ((coordZ i).hasFDerivAt (x := y)).const_mul b |>.add
        (((coordV i).hasFDerivAt (x := y)).const_mul (2 * c))
      exact this
    · rintro (j | j) <;> simp [vecDir, genCoeff, Pi.single_apply, eq_comm]
  · refine ⟨(2 * a) • coordZ i + b • coordV i, ?_, ?_⟩
    · have := ((coordZ i).hasFDerivAt (x := y)).const_mul (2 * a) |>.add
        (((coordV i).hasFDerivAt (x := y)).const_mul b)
      exact this
    · rintro (j | j) <;> simp [vecDir, genCoeff, Pi.single_apply, eq_comm]

theorem dirPartial_gen (a b c : ℝ) (δ δ' : Fin d ⊕ Fin d) (y : EvolutionAmbientState d) :
    dirPartial δ' (gen a b c δ) y = genCoeff a b c δ δ' := by
  obtain ⟨L, hL, hv⟩ := hasFDerivAt_gen a b c δ y
  unfold dirPartial
  rw [hL.fderiv, hv]

theorem differentiable_gen (a b c : ℝ) (δ : Fin d ⊕ Fin d) :
    Differentiable ℝ (gen a b c δ : EvolutionAmbientState d → ℝ) := fun y =>
  (hasFDerivAt_gen a b c δ y).choose_spec.1.differentiableAt

theorem dirPartial_gaussExp (a b c : ℝ) (δ : Fin d ⊕ Fin d) (y : EvolutionAmbientState d) :
    dirPartial δ (gaussExp a b c) y = -gen a b c δ y * gaussExp a b c y := by
  unfold dirPartial gaussExp
  have h : HasFDerivAt (fun y => rexp (-quadForm a b c y))
      (rexp (-quadForm a b c y) • -fderiv ℝ (quadForm a b c) y) y :=
    ((contDiff_quadForm a b c 1).differentiable one_ne_zero y).hasFDerivAt.neg.exp
  rw [h.fderiv]
  have := dirPartial_quadForm a b c δ y
  unfold dirPartial at this
  simp [this]
  ring

/-- Leibniz rule against the Gaussian exponential: `∂_δ (p G) = (∂_δ p - p ∂_δ Q) G`. -/
theorem dirPartial_mul_gaussExp (a b c : ℝ) (δ : Fin d ⊕ Fin d)
    {p : EvolutionAmbientState d → ℝ} {y : EvolutionAmbientState d}
    (hp : DifferentiableAt ℝ p y) :
    dirPartial δ (fun y => p y * gaussExp a b c y) y =
      (dirPartial δ p y - p y * gen a b c δ y) * gaussExp a b c y := by
  have hG : DifferentiableAt ℝ (gaussExp a b c : EvolutionAmbientState d → ℝ) y :=
    ((contDiff_gaussExp a b c 1).differentiable one_ne_zero) y
  unfold dirPartial
  rw [fderiv_fun_mul hp hG]
  have := dirPartial_gaussExp a b c δ y
  unfold dirPartial at this
  simp [this]
  ring

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
