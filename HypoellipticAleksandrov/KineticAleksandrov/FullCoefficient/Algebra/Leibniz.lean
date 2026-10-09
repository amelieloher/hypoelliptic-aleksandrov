module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Calculus

/-!
# Directional second derivatives: product and chain rules

The flow identities (calculus input). For a direction
`a` and a direction `b`, `dirSecond F a b y = ∂_b (∂_a F) (y)`. The coordinate second
derivatives of `Calculus.lean` are instances of this with coordinate directions. Here the
Leibniz rule and the chain rule for these second derivatives are proved for `C²` functions.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ}

/-- The iterated directional derivative `∂_b (∂_a F)` at `y`. -/
def dirSecond (F : EvolutionAmbientState d → ℝ) (a b : EvolutionAmbientState d)
    (y : EvolutionAmbientState d) : ℝ :=
  fderiv ℝ (fun y' => fderiv ℝ F y' a) y b

/-- The directional derivative of a `C²` function is differentiable. -/
theorem hasFDerivAt_dir {F : EvolutionAmbientState d → ℝ} (hF : ContDiff ℝ 2 F)
    (a : EvolutionAmbientState d) (y : EvolutionAmbientState d) :
    HasFDerivAt (fun y' => fderiv ℝ F y' a) (fderiv ℝ (fun y' => fderiv ℝ F y' a) y) y := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  have h2 : ContDiff ℝ 1 (fun y' => fderiv ℝ F y' a) := h1.clm_apply contDiff_const
  exact (h2.differentiable (by norm_num) y).hasFDerivAt

/-- First-order Leibniz rule, as an equality of functions. -/
theorem fderiv_dir_mul {F G : EvolutionAmbientState d → ℝ} (hF : ContDiff ℝ 2 F)
    (hG : ContDiff ℝ 2 G) (a : EvolutionAmbientState d) :
    (fun y' => fderiv ℝ (fun y => F y * G y) y' a)
      = fun y' => F y' * fderiv ℝ G y' a + G y' * fderiv ℝ F y' a := by
  funext y'
  have hF' := (hF.differentiable (by norm_num) y').hasFDerivAt
  have hG' := (hG.differentiable (by norm_num) y').hasFDerivAt
  have e : fderiv ℝ (fun y => F y * G y) y' = _ := (hF'.mul hG').fderiv
  rw [e]
  simp

/-- Second-order Leibniz rule. -/
theorem dirSecond_mul {F G : EvolutionAmbientState d → ℝ} (hF : ContDiff ℝ 2 F)
    (hG : ContDiff ℝ 2 G) (a b y : EvolutionAmbientState d) :
    dirSecond (fun y => F y * G y) a b y
      = F y * dirSecond G a b y + G y * dirSecond F a b y
        + fderiv ℝ F y b * fderiv ℝ G y a + fderiv ℝ F y a * fderiv ℝ G y b := by
  unfold dirSecond
  rw [fderiv_dir_mul hF hG a]
  have hF' := (hF.differentiable (by norm_num) y).hasFDerivAt
  have hG' := (hG.differentiable (by norm_num) y).hasFDerivAt
  have hFa := hasFDerivAt_dir hF a y
  have hGa := hasFDerivAt_dir hG a y
  have e : fderiv ℝ (fun y' => F y' * fderiv ℝ G y' a + G y' * fderiv ℝ F y' a) y = _ :=
    ((hF'.mul hGa).add (hG'.mul hFa)).fderiv
  rw [e]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- First-order chain rule, as an equality of functions. -/
theorem fderiv_dir_comp {F : EvolutionAmbientState d → ℝ} (hF : ContDiff ℝ 2 F)
    {φ φ' : ℝ → ℝ} (hφ : ∀ y', HasDerivAt φ (φ' (F y')) (F y'))
    (a : EvolutionAmbientState d) :
    (fun y' => fderiv ℝ (fun y => φ (F y)) y' a)
      = fun y' => φ' (F y') * fderiv ℝ F y' a := by
  funext y'
  have hF' := (hF.differentiable (by norm_num) y').hasFDerivAt
  have e : fderiv ℝ (fun y => φ (F y)) y' = _ := ((hφ y').comp_hasFDerivAt y' hF').fderiv
  rw [e]
  simp

/-- Second-order chain rule. -/
theorem dirSecond_comp {F : EvolutionAmbientState d → ℝ} (hF : ContDiff ℝ 2 F)
    {φ φ' φ'' : ℝ → ℝ} (hφ : ∀ y', HasDerivAt φ (φ' (F y')) (F y'))
    (y : EvolutionAmbientState d) (hφ' : HasDerivAt φ' (φ'' (F y)) (F y))
    (a b : EvolutionAmbientState d) :
    dirSecond (fun y => φ (F y)) a b y
      = φ' (F y) * dirSecond F a b y + φ'' (F y) * (fderiv ℝ F y b * fderiv ℝ F y a) := by
  unfold dirSecond
  rw [fderiv_dir_comp hF hφ a]
  have hF' := (hF.differentiable (by norm_num) y).hasFDerivAt
  have hFa := hasFDerivAt_dir hF a y
  have hc := hφ'.comp_hasFDerivAt y hF'
  have e : fderiv ℝ (fun y' => φ' (F y') * fderiv ℝ F y' a) y = _ := (hc.mul hFa).fderiv
  rw [e]
  simp only [add_apply, smul_apply, smul_eq_mul]
  simp
  ring

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
