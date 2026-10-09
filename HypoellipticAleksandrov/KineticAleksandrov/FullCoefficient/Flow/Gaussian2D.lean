module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Two-dimensional Gaussian integrals

Integrability and total mass of `exp (-(a u² + b u w + c w²))` on `ℝ × ℝ`, with the pair written
as `p = (w, u)` (velocity first), by completing the square in `u`. Used for the unit-mass identity
of the Gaussian flow kernel.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open Real MeasureTheory

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

/-- The quadratic form `a u² + b u w + c w²` at `p = (w, u)`. -/
def pairQ (a b c : ℝ) (p : ℝ × ℝ) : ℝ := a * p.2 ^ 2 + b * p.2 * p.1 + c * p.1 ^ 2

/-- The conditional variance coefficient `c - b² / (4a)`. -/
def pairRes (a b c : ℝ) : ℝ := c - b ^ 2 / (4 * a)

theorem pairQ_eq {a b c : ℝ} (ha : 0 < a) (p : ℝ × ℝ) :
    pairQ a b c p = a * (p.2 + b / (2 * a) * p.1) ^ 2 + pairRes a b c * p.1 ^ 2 := by
  unfold pairQ pairRes
  field_simp
  ring

theorem integral_exp_neg_pairQ_inner {a b c : ℝ} (ha : 0 < a) (w : ℝ) :
    ∫ u : ℝ, exp (-pairQ a b c (w, u)) = √(π / a) * exp (-(pairRes a b c * w ^ 2)) := by
  have h1 : ∀ u : ℝ, exp (-pairQ a b c (w, u)) =
      exp (-a * (u + b / (2 * a) * w) ^ 2) * exp (-(pairRes a b c * w ^ 2)) := by
    intro u
    rw [← Real.exp_add, pairQ_eq ha]
    congr 1
    simp only [neg_mul]
    ring
  simp_rw [h1]
  rw [integral_mul_const, integral_add_right_eq_self (fun u : ℝ => exp (-a * u ^ 2))
    (b / (2 * a) * w), integral_gaussian]

theorem integrable_exp_neg_pairQ_inner {a b c : ℝ} (ha : 0 < a) (w : ℝ) :
    Integrable (fun u : ℝ => exp (-pairQ a b c (w, u))) := by
  have h1 : ∀ u : ℝ, exp (-pairQ a b c (w, u)) =
      exp (-a * (u + b / (2 * a) * w) ^ 2) * exp (-(pairRes a b c * w ^ 2)) := by
    intro u
    rw [← Real.exp_add, pairQ_eq ha]
    congr 1
    simp only [neg_mul]
    ring
  simp_rw [h1]
  exact ((integrable_exp_neg_mul_sq ha).comp_add_right (b / (2 * a) * w)).mul_const _

theorem integrable_exp_neg_pairQ {a b c : ℝ} (ha : 0 < a) (hr : 0 < pairRes a b c) :
    Integrable (fun p : ℝ × ℝ => exp (-pairQ a b c p)) := by
  rw [Measure.volume_eq_prod, integrable_prod_iff]
  · refine ⟨Filter.Eventually.of_forall fun w => integrable_exp_neg_pairQ_inner ha w, ?_⟩
    have h2 : (fun w : ℝ => ∫ u : ℝ, ‖exp (-pairQ a b c (w, u))‖) =
        fun w => √(π / a) * exp (-(pairRes a b c * w ^ 2)) := by
      funext w
      simp_rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact integral_exp_neg_pairQ_inner ha w
    rw [h2]
    have := (integrable_exp_neg_mul_sq hr).const_mul (√(π / a))
    simpa [neg_mul] using this
  · exact (Continuous.aestronglyMeasurable (by unfold pairQ; fun_prop))

theorem integral_exp_neg_pairQ {a b c : ℝ} (ha : 0 < a) (hr : 0 < pairRes a b c) :
    ∫ p : ℝ × ℝ, exp (-pairQ a b c p) = √(π / a) * √(π / pairRes a b c) := by
  rw [Measure.volume_eq_prod, integral_prod _ (by
    rw [← Measure.volume_eq_prod]; exact integrable_exp_neg_pairQ ha hr)]
  simp_rw [integral_exp_neg_pairQ_inner ha]
  rw [integral_const_mul]
  congr 1
  have := integral_gaussian (pairRes a b c)
  simpa [neg_mul] using this

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
