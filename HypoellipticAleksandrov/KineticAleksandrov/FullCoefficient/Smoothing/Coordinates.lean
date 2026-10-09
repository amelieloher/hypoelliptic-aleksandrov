module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Calculus
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Coordinate partial derivatives and their norms

All `2d` coordinate directions of phase space `(v, z)` are indexed by `Fin d ⊕ Fin d`
(velocity coordinates on the left, position coordinates on the right). This module records the
squared gradient and Hessian norms used in the smoothing estimates, their comparison with the
operator norms of the Fréchet derivatives,
and the commutation of coordinate partials with weighted convolutions.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ}

/-- The unit vector of phase space in the coordinate direction `c`. -/
def coordDir : Fin d ⊕ Fin d → EvolutionAmbientState d
  | Sum.inl i => (Pi.single i 1, 0)
  | Sum.inr i => (0, Pi.single i 1)

/-- The partial derivative in the coordinate direction `c`. -/
def coordPartial (c : Fin d ⊕ Fin d) (F : EvolutionAmbientState d → ℝ)
    (y : EvolutionAmbientState d) : ℝ :=
  fderiv ℝ F y (coordDir c)

theorem velocityPartial_eq (i : Fin d) (F : EvolutionAmbientState d → ℝ) :
    velocityPartial i F = coordPartial (Sum.inl i) F := rfl

theorem positionPartial_eq (i : Fin d) (F : EvolutionAmbientState d → ℝ) :
    positionPartial i F = coordPartial (Sum.inr i) F := rfl

/-- The squared Euclidean norm of the gradient, `|DF|²`. -/
def gradNormSq (F : EvolutionAmbientState d → ℝ) (y : EvolutionAmbientState d) : ℝ :=
  ∑ c, coordPartial c F y ^ 2

/-- The squared Euclidean norm of the Hessian, `|D²F|²`. -/
def hessNormSq (F : EvolutionAmbientState d → ℝ) (y : EvolutionAmbientState d) : ℝ :=
  ∑ c, ∑ c', coordPartial c (coordPartial c' F) y ^ 2

theorem norm_coordDir_le (c : Fin d ⊕ Fin d) : ‖coordDir c‖ ≤ 1 := by
  rcases c with i | i
  · simp only [coordDir, Prod.norm_def, norm_zero]
    refine max_le ?_ zero_le_one
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
    by_cases h : j = i
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  · simp only [coordDir, Prod.norm_def, norm_zero]
    refine max_le zero_le_one ?_
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
    by_cases h : j = i
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]

theorem abs_coordPartial_le (c : Fin d ⊕ Fin d) (F : EvolutionAmbientState d → ℝ)
    (y : EvolutionAmbientState d) : |coordPartial c F y| ≤ ‖fderiv ℝ F y‖ := by
  have := (fderiv ℝ F y).le_opNorm (coordDir c)
  rw [coordPartial, ← Real.norm_eq_abs]
  exact this.trans (mul_le_of_le_one_right (norm_nonneg _) (norm_coordDir_le c))

theorem abs_coordPartial_coordPartial_le {F : EvolutionAmbientState d → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (c c' : Fin d ⊕ Fin d) (y : EvolutionAmbientState d) :
    |coordPartial c (coordPartial c' F) y| ≤ ‖iteratedFDeriv ℝ 2 F y‖ := by
  have hd : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (m := 1) (by simp)
  have hfun : coordPartial c' F = fun x => fderiv ℝ F x (coordDir c') := rfl
  have hdiff : DifferentiableAt ℝ (fderiv ℝ F) y :=
    (hd.differentiable one_ne_zero) y
  have h2 : coordPartial c (coordPartial c' F) y =
      fderiv ℝ (fderiv ℝ F) y (coordDir c) (coordDir c') := by
    rw [coordPartial, hfun, fderiv_clm_apply hdiff (differentiableAt_const _)]
    simp
  rw [h2]
  have hn : ‖iteratedFDeriv ℝ 1 (fderiv ℝ F) y‖ = ‖iteratedFDeriv ℝ 2 F y‖ :=
    norm_iteratedFDeriv_fderiv (n := 1)
  rw [norm_iteratedFDeriv_one] at hn
  rw [← hn, ← Real.norm_eq_abs]
  calc ‖fderiv ℝ (fderiv ℝ F) y (coordDir c) (coordDir c')‖
      ≤ ‖fderiv ℝ (fderiv ℝ F) y (coordDir c)‖ * ‖coordDir c'‖ :=
        (fderiv ℝ (fderiv ℝ F) y (coordDir c)).le_opNorm _
    _ ≤ ‖fderiv ℝ (fderiv ℝ F) y‖ * ‖coordDir c‖ * ‖coordDir c'‖ := by
        gcongr; exact (fderiv ℝ (fderiv ℝ F) y).le_opNorm _
    _ ≤ ‖fderiv ℝ (fderiv ℝ F) y‖ := by
        have h1 := norm_coordDir_le c
        have h2 := norm_coordDir_le c'
        have hn0 := norm_nonneg (fderiv ℝ (fderiv ℝ F) y)
        calc _ ≤ ‖fderiv ℝ (fderiv ℝ F) y‖ * 1 * 1 := by gcongr
          _ = _ := by ring

theorem gradNormSq_le (F : EvolutionAmbientState d → ℝ) (y : EvolutionAmbientState d) :
    gradNormSq F y ≤ (2 * d) * ‖fderiv ℝ F y‖ ^ 2 := by
  unfold gradNormSq
  calc ∑ c, coordPartial c F y ^ 2 ≤ ∑ _c : Fin d ⊕ Fin d, ‖fderiv ℝ F y‖ ^ 2 := by
        refine Finset.sum_le_sum fun c _ => ?_
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (abs_coordPartial_le c F y) 2
    _ = (2 * d) * ‖fderiv ℝ F y‖ ^ 2 := by
        simp [Finset.sum_const, Fintype.card_sum, two_mul]

theorem hessNormSq_le {F : EvolutionAmbientState d → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (y : EvolutionAmbientState d) :
    hessNormSq F y ≤ (2 * d) ^ 2 * ‖iteratedFDeriv ℝ 2 F y‖ ^ 2 := by
  unfold hessNormSq
  calc ∑ c, ∑ c', coordPartial c (coordPartial c' F) y ^ 2
      ≤ ∑ _c : Fin d ⊕ Fin d, ∑ _c' : Fin d ⊕ Fin d, ‖iteratedFDeriv ℝ 2 F y‖ ^ 2 := by
        refine Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun c' _ => ?_
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (abs_coordPartial_coordPartial_le hF c c' y) 2
    _ = (2 * d) ^ 2 * ‖iteratedFDeriv ℝ 2 F y‖ ^ 2 := by
        simp [Finset.sum_const, Fintype.card_sum, two_mul]
        ring

theorem contDiff_coordPartial {F : EvolutionAmbientState d → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (c : Fin d ⊕ Fin d) : ContDiff ℝ (⊤ : ℕ∞) (coordPartial c F) :=
  (hF.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const

theorem continuous_coordPartial {F : EvolutionAmbientState d → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (c : Fin d ⊕ Fin d) : Continuous (coordPartial c F) :=
  (contDiff_coordPartial hF c).continuous

theorem differentiable_coordPartial {F : EvolutionAmbientState d → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (c : Fin d ⊕ Fin d) : Differentiable ℝ (coordPartial c F) :=
  (contDiff_coordPartial hF c).differentiable (by simp)

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
