module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.FisherBeta
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.DerivBounds

/-!
# Euclidean gradient and Hessian norms

The norms `|DF|`, `|D²F|` of a scalar function and `|DB|`, `|D²B|` of a matrix field on phase
space (square roots of the coordinatewise sums of squares), with elementary estimates from
coordinatewise bounds. These are the norms in the integrability list of the smoothing estimates.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ}

/-- The Euclidean gradient norm `|DF|`. -/
def gradNorm (F : EvolutionAmbientState d → ℝ) (y : EvolutionAmbientState d) : ℝ :=
  √(gradNormSq F y)

/-- The Euclidean Hessian norm `|D²F|`. -/
def hessNorm (F : EvolutionAmbientState d → ℝ) (y : EvolutionAmbientState d) : ℝ :=
  √(hessNormSq F y)

/-- The squared Hessian norm `|D²B|² = ∑ᵢⱼ |D² Bᵢⱼ|²` of a matrix field. -/
def coefficientHessNormSq (B : EvolutionAmbientState d → PDE.Mat d)
    (y : EvolutionAmbientState d) : ℝ :=
  ∑ i, ∑ j, hessNormSq (fun y => B y i j) y

/-- The gradient norm `|DB|` of a matrix field. -/
def coefficientGradNorm (B : EvolutionAmbientState d → PDE.Mat d)
    (y : EvolutionAmbientState d) : ℝ :=
  √(coefficientGradNormSq B y)

/-- The Hessian norm `|D²B|` of a matrix field. -/
def coefficientHessNorm (B : EvolutionAmbientState d → PDE.Mat d)
    (y : EvolutionAmbientState d) : ℝ :=
  √(coefficientHessNormSq B y)

theorem gradNormSq_nonneg (F : EvolutionAmbientState d → ℝ) (y : EvolutionAmbientState d) :
    0 ≤ gradNormSq F y :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem hessNormSq_nonneg (F : EvolutionAmbientState d → ℝ) (y : EvolutionAmbientState d) :
    0 ≤ hessNormSq F y :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem coefficientGradNormSq_nonneg (B : EvolutionAmbientState d → PDE.Mat d)
    (y : EvolutionAmbientState d) : 0 ≤ coefficientGradNormSq B y :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => gradNormSq_nonneg _ _

theorem coefficientHessNormSq_nonneg (B : EvolutionAmbientState d → PDE.Mat d)
    (y : EvolutionAmbientState d) : 0 ≤ coefficientHessNormSq B y :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hessNormSq_nonneg _ _

theorem sqrt_le_mul_succ {x n B : ℝ} (hn : 0 ≤ n) (hB : 0 ≤ B) (hx : x ≤ n * B ^ 2) :
    √x ≤ (n + 1) * B := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, hx.trans ?_⟩
  nlinarith [sq_nonneg B, mul_nonneg hn (sq_nonneg B)]

theorem gradNormSq_le_of_forall {F : EvolutionAmbientState d → ℝ} {B : ℝ}
    {y : EvolutionAmbientState d} (h : ∀ c, |coordPartial c F y| ≤ B) :
    gradNormSq F y ≤ (2 * d) * B ^ 2 := by
  unfold gradNormSq
  calc ∑ c, coordPartial c F y ^ 2 ≤ ∑ _c : Fin d ⊕ Fin d, B ^ 2 :=
        Finset.sum_le_sum fun c _ => by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h c) 2
    _ = (2 * d) * B ^ 2 := by simp [Finset.sum_const, Fintype.card_sum, two_mul]

theorem hessNormSq_le_of_forall {F : EvolutionAmbientState d → ℝ} {B : ℝ}
    {y : EvolutionAmbientState d} (h : ∀ c c', |coordPartial c' (coordPartial c F) y| ≤ B) :
    hessNormSq F y ≤ (2 * d) ^ 2 * B ^ 2 := by
  unfold hessNormSq
  calc ∑ c, ∑ c', coordPartial c (coordPartial c' F) y ^ 2
      ≤ ∑ _c : Fin d ⊕ Fin d, ∑ _c' : Fin d ⊕ Fin d, B ^ 2 :=
        Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun c' _ => by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h c' c) 2
    _ = (2 * d) ^ 2 * B ^ 2 := by simp [Finset.sum_const, Fintype.card_sum, two_mul]; ring

theorem continuous_gradNormSq {F : EvolutionAmbientState d → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    Continuous (gradNormSq F) :=
  continuous_finsetSum _ fun c _ => (continuous_coordPartial hF c).pow 2

theorem continuous_hessNormSq {F : EvolutionAmbientState d → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    Continuous (hessNormSq F) :=
  continuous_finsetSum _ fun c _ => continuous_finsetSum _ fun c' _ =>
    (continuous_coordPartial (contDiff_coordPartial hF c') c).pow 2

theorem continuous_gradNorm {F : EvolutionAmbientState d → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    Continuous (gradNorm F) :=
  (continuous_gradNormSq hF).sqrt

theorem continuous_hessNorm {F : EvolutionAmbientState d → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    Continuous (hessNorm F) :=
  (continuous_hessNormSq hF).sqrt

theorem continuous_coefficientGradNormSq {B : EvolutionAmbientState d → PDE.Mat d}
    (hB : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun y => B y i j)) :
    Continuous (coefficientGradNormSq B) :=
  continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => continuous_gradNormSq (hB i j)

theorem continuous_coefficientHessNormSq {B : EvolutionAmbientState d → PDE.Mat d}
    (hB : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun y => B y i j)) :
    Continuous (coefficientHessNormSq B) :=
  continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => continuous_hessNormSq (hB i j)

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
