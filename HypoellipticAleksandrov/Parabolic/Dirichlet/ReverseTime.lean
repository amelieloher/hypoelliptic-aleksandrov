module

public import HypoellipticAleksandrov.Parabolic.ScalarDirichletData
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Tactic.Ring

/-!
# Classical reverse-time divergence rewrite

This file records the pointwise reverse-time calculation for the scalar
parabolic Dirichlet equation, including its literal coordinate divergence
form.  It does not introduce a weak or variational divergence.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace HypoellipticAleksandrov.Parabolic

/-- `(τ, y) ↦ (r₁ - τ, y)`. -/
def reverseTimeMap {n : ℕ} (r₁ : ℝ) : TimeVelocity n → TimeVelocity n :=
  fun z => (r₁ - z.1, z.2)

/-- Pullback of a scalar field by `reverseTimeMap r₁`. -/
def reverseTimeScalar {n : ℕ} (r₁ : ℝ)
    (f : TimeVelocity n → ℝ) : TimeVelocity n → ℝ :=
  fun z => f (reverseTimeMap r₁ z)

/-- Pullback of a time--space matrix coefficient by reverse time. -/
def reverseTimeCoefficient {n : ℕ} (r₁ : ℝ)
    (a : CoefficientField n) : CoefficientField n :=
  fun τ y => a (r₁ - τ) y

/-- Pullback of a time--space vector coefficient by reverse time. -/
def reverseTimeVectorCoefficient {n : ℕ} (r₁ : ℝ)
    (b : ℝ → PDE.Vec n → PDE.Vec n) : ℝ → PDE.Vec n → PDE.Vec n :=
  fun τ y => b (r₁ - τ) y

/-- Pullback of a curried scalar coefficient or source by reverse time. -/
def reverseTimeScalarCoefficient {n : ℕ} (r₁ : ℝ)
    (q : ℝ → PDE.Vec n → ℝ) : ℝ → PDE.Vec n → ℝ :=
  fun τ y => q (r₁ - τ) y

/-- Evaluation of `reverseTimeMap`. -/
@[simp] theorem reverseTimeMap_apply {n : ℕ} (r₁ : ℝ) (z : TimeVelocity n) :
    reverseTimeMap r₁ z = (r₁ - z.1, z.2) :=
  rfl

/-- Evaluation of the reverse-time scalar pullback. -/
@[simp] theorem reverseTimeScalar_apply {n : ℕ} (r₁ : ℝ)
    (f : TimeVelocity n → ℝ) (z : TimeVelocity n) :
    reverseTimeScalar r₁ f z = f (reverseTimeMap r₁ z) :=
  rfl

/-- Evaluation of the reverse-time matrix-coefficient pullback. -/
@[simp] theorem reverseTimeCoefficient_apply {n : ℕ} (r₁ : ℝ)
    (a : CoefficientField n) (τ : ℝ) (y : PDE.Vec n) :
    reverseTimeCoefficient r₁ a τ y = a (r₁ - τ) y :=
  rfl

/-- Evaluation of the reverse-time vector-coefficient pullback. -/
@[simp] theorem reverseTimeVectorCoefficient_apply {n : ℕ} (r₁ : ℝ)
    (b : ℝ → PDE.Vec n → PDE.Vec n) (τ : ℝ) (y : PDE.Vec n) :
    reverseTimeVectorCoefficient r₁ b τ y = b (r₁ - τ) y :=
  rfl

/-- Evaluation of the reverse-time scalar-coefficient pullback. -/
@[simp] theorem reverseTimeScalarCoefficient_apply {n : ℕ} (r₁ : ℝ)
    (q : ℝ → PDE.Vec n → ℝ) (τ : ℝ) (y : PDE.Vec n) :
    reverseTimeScalarCoefficient r₁ q τ y = q (r₁ - τ) y :=
  rfl

/-- The vector with `j` component `∑ i, ∂ᵢ aᵢⱼ`, at a fixed time. -/
def scalarSpatialCoefficientDivergence {n : ℕ}
    (a : CoefficientField n) (z : TimeVelocity n) : PDE.Vec n :=
  fun j => ∑ i : Fin n,
    (fderiv ℝ (fun y : PDE.Vec n => a z.1 y i j) z.2) (PDE.basisVec i)

/-- The classical spatial divergence `∑ᵢ ∂ᵢ(∑ⱼ aᵢⱼ ∂ⱼu)`. -/
def scalarSpatialFluxDivergence {n : ℕ}
    (a : CoefficientField n) (u : TimeVelocity n → ℝ)
    (z : TimeVelocity n) : ℝ :=
  ∑ i : Fin n,
    (fderiv ℝ (fun y : PDE.Vec n =>
      ∑ j : Fin n, a z.1 y i j * scalarSpatialGradient u (z.1, y) j)
      z.2) (PDE.basisVec i)

/-- `dᴿ_j = ∑ᵢ ∂ᵢaᴿ_ij - bᴿ_j`, with the manuscript's row--column order. -/
def reverseTimeDivergenceDrift {n : ℕ} (r₁ : ℝ)
    (a : CoefficientField n) (b : ℝ → PDE.Vec n → PDE.Vec n) :
    ℝ → PDE.Vec n → PDE.Vec n :=
  fun τ y => scalarSpatialCoefficientDivergence
      (reverseTimeCoefficient r₁ a) (τ, y) -
    reverseTimeVectorCoefficient r₁ b τ y

/-- Forward-time nondivergence expression after reversing the backward PDE. -/
def scalarForwardNondivergenceOperator {n : ℕ}
    (a : CoefficientField n) (b : ℝ → PDE.Vec n → PDE.Vec n)
    (c : ℝ → PDE.Vec n → ℝ) (u : TimeVelocity n → ℝ)
    (z : TimeVelocity n) : ℝ :=
  scalarTimeDerivative u z -
    matrixContraction (a z.1 z.2) (scalarSpatialHessian u z) -
    PDE.vecDot (b z.1 z.2) (scalarSpatialGradient u z) - c z.1 z.2 * u z

/-- Literal pointwise classical divergence-form expression. -/
def scalarForwardDivergenceFormOperator {n : ℕ}
    (a : CoefficientField n) (d : ℝ → PDE.Vec n → PDE.Vec n)
    (c : ℝ → PDE.Vec n → ℝ) (u : TimeVelocity n → ℝ)
    (z : TimeVelocity n) : ℝ :=
  scalarTimeDerivative u z - scalarSpatialFluxDivergence a u z +
    PDE.vecDot (d z.1 z.2) (scalarSpatialGradient u z) - c z.1 z.2 * u z

/-- Reverse time negates the derivative of a fixed-spatial scalar time slice. -/
theorem scalarTimeDerivative_reverseTimeScalar {n : ℕ} {r₁ : ℝ}
    {u : TimeVelocity n → ℝ} {z : TimeVelocity n}
    (hu : HasDerivAt (fun r : ℝ => u (r, z.2))
      (scalarTimeDerivative u (reverseTimeMap r₁ z))
      (reverseTimeMap r₁ z).1) :
    scalarTimeDerivative (reverseTimeScalar r₁ u) z =
      -scalarTimeDerivative u (reverseTimeMap r₁ z) := by
  exact (hu.comp_const_sub r₁ z.1).deriv

/-- Reverse time leaves the fixed-time spatial gradient unchanged. -/
theorem scalarSpatialGradient_reverseTimeScalar {n : ℕ} (r₁ : ℝ)
    (u : TimeVelocity n → ℝ) (z : TimeVelocity n) :
    scalarSpatialGradient (reverseTimeScalar r₁ u) z =
      scalarSpatialGradient u (reverseTimeMap r₁ z) :=
  rfl

/-- Reverse time leaves the fixed-time spatial Hessian unchanged. -/
theorem scalarSpatialHessian_reverseTimeScalar {n : ℕ} (r₁ : ℝ)
    (u : TimeVelocity n → ℝ) (z : TimeVelocity n) :
    scalarSpatialHessian (reverseTimeScalar r₁ u) z =
      scalarSpatialHessian u (reverseTimeMap r₁ z) :=
  rfl

/-- Reverse time commutes with the fixed-time coefficient divergence. -/
theorem scalarSpatialCoefficientDivergence_reverseTimeCoefficient
    {n : ℕ} (r₁ : ℝ) (a : CoefficientField n) (z : TimeVelocity n) :
    scalarSpatialCoefficientDivergence (reverseTimeCoefficient r₁ a) z =
      scalarSpatialCoefficientDivergence a (reverseTimeMap r₁ z) :=
  rfl

private theorem differentiableAt_scalarSpatialGradient {n : ℕ}
    {f : PDE.Vec n → ℝ} {x : PDE.Vec n}
    (hf : ContDiffAt ℝ 2 f x) :
    DifferentiableAt ℝ (fun y => PDE.classicalGradient f y) x := by
  apply differentiableAt_pi.2
  intro j
  have hderiv : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  exact hderiv.clm_apply (differentiableAt_const (c := PDE.basisVec j))

private theorem fderiv_scalarSpatialGradient_apply {n : ℕ}
    {f : PDE.Vec n → ℝ} {x : PDE.Vec n} (i j : Fin n)
    (hf : ContDiffAt ℝ 2 f x) :
    (fderiv ℝ (fun y => PDE.classicalGradient f y j) x) (PDE.basisVec i) =
      (fderiv ℝ (fun y => PDE.classicalGradient f y) x (PDE.basisVec i)) j := by
  have hgrad := differentiableAt_scalarSpatialGradient hf
  rw [fderiv_pi (fun k => (differentiableAt_pi.mp hgrad) k)]
  rfl

/-- Pointwise coordinate product rule for the classical spatial flux. -/
theorem scalarSpatialFluxDivergence_eq_matrixContraction_add
    {n : ℕ} {a : CoefficientField n} {u : TimeVelocity n → ℝ}
    {z : TimeVelocity n}
    (ha : ∀ i j : Fin n,
      DifferentiableAt ℝ (fun y : PDE.Vec n => a z.1 y i j) z.2)
    (hu : ContDiffAt ℝ 2 (fun y : PDE.Vec n => u (z.1, y)) z.2) :
    scalarSpatialFluxDivergence a u z =
      matrixContraction (a z.1 z.2) (scalarSpatialHessian u z) +
        PDE.vecDot (scalarSpatialCoefficientDivergence a z)
          (scalarSpatialGradient u z) := by
  unfold scalarSpatialFluxDivergence matrixContraction PDE.vecDot
    scalarSpatialCoefficientDivergence scalarSpatialHessian scalarSpatialGradient
  have hsum (i : Fin n) :
      (fderiv ℝ (fun y : PDE.Vec n =>
        ∑ j : Fin n, a z.1 y i j * PDE.classicalGradient
          (fun w : PDE.Vec n => u (z.1, w)) y j) z.2) (PDE.basisVec i) =
        ∑ j : Fin n, (fderiv ℝ (fun y : PDE.Vec n =>
          a z.1 y i j * PDE.classicalGradient
            (fun w : PDE.Vec n => u (z.1, w)) y j) z.2) (PDE.basisVec i) := by
    rw [fderiv_fun_sum]
    · simp only [ContinuousLinearMap.sum_apply]
    · intro j _hj
      exact (ha i j).mul (differentiableAt_pi.mp
        (differentiableAt_scalarSpatialGradient hu) j)
  have hprod (i j : Fin n) :
      (fderiv ℝ (fun y : PDE.Vec n =>
        a z.1 y i j * PDE.classicalGradient
          (fun w : PDE.Vec n => u (z.1, w)) y j) z.2) (PDE.basisVec i) =
        a z.1 z.2 i j *
          (fderiv ℝ (fun y : PDE.Vec n => PDE.classicalGradient
            (fun w : PDE.Vec n => u (z.1, w)) y) z.2 (PDE.basisVec i)) j +
        (fderiv ℝ (fun y : PDE.Vec n => a z.1 y i j) z.2)
          (PDE.basisVec i) * PDE.classicalGradient
            (fun w : PDE.Vec n => u (z.1, w)) z.2 j := by
    rw [fderiv_fun_mul (ha i j) ((differentiableAt_pi.mp
      (differentiableAt_scalarSpatialGradient hu)) j)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
    rw [fderiv_scalarSpatialGradient_apply i j hu]
    ring
  calc
    ∑ i : Fin n, (fderiv ℝ (fun y : PDE.Vec n =>
      ∑ j : Fin n, a z.1 y i j * PDE.classicalGradient
        (fun w : PDE.Vec n => u (z.1, w)) y j) z.2) (PDE.basisVec i) =
      ∑ i : Fin n, ∑ j : Fin n, (fderiv ℝ (fun y : PDE.Vec n =>
        a z.1 y i j * PDE.classicalGradient
          (fun w : PDE.Vec n => u (z.1, w)) y j) z.2) (PDE.basisVec i) := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact hsum i
    _ = ∑ i : Fin n, ∑ j : Fin n,
        (a z.1 z.2 i j *
          (fderiv ℝ (fun y : PDE.Vec n => PDE.classicalGradient
            (fun w : PDE.Vec n => u (z.1, w)) y) z.2 (PDE.basisVec i)) j +
        (fderiv ℝ (fun y : PDE.Vec n => a z.1 y i j) z.2)
          (PDE.basisVec i) * PDE.classicalGradient
            (fun w : PDE.Vec n => u (z.1, w)) z.2 j) := by
        simp_rw [hprod]
    _ = ∑ i : Fin n, ∑ j : Fin n,
        a z.1 z.2 i j *
          (fderiv ℝ (fun y : PDE.Vec n => PDE.classicalGradient
            (fun w : PDE.Vec n => u (z.1, w)) y) z.2 (PDE.basisVec i)) j +
      ∑ j : Fin n, (∑ i : Fin n,
        (fderiv ℝ (fun y : PDE.Vec n => a z.1 y i j) z.2)
          (PDE.basisVec i)) * PDE.classicalGradient
            (fun w : PDE.Vec n => u (z.1, w)) z.2 j := by
        simp_rw [Finset.sum_add_distrib]
        congr 1
        rw [Finset.sum_comm]
        simp only [Finset.sum_mul]

/-- Reversing time negates the full backward nondivergence expression. -/
theorem reverseTime_nondivergenceOperator_eq_neg
    {n : ℕ} {r₁ : ℝ} (a : CoefficientField n)
    (b : ℝ → PDE.Vec n → PDE.Vec n) (c : ℝ → PDE.Vec n → ℝ)
    {u : TimeVelocity n → ℝ} {z : TimeVelocity n}
    (huTime : HasDerivAt (fun r : ℝ => u (r, z.2))
      (scalarTimeDerivative u (reverseTimeMap r₁ z))
      (reverseTimeMap r₁ z).1) :
    scalarForwardNondivergenceOperator
      (reverseTimeCoefficient r₁ a) (reverseTimeVectorCoefficient r₁ b)
      (reverseTimeScalarCoefficient r₁ c) (reverseTimeScalar r₁ u) z =
      -scalarParabolicZeroOrderOperator a b c u (reverseTimeMap r₁ z) := by
  unfold scalarForwardNondivergenceOperator scalarParabolicZeroOrderOperator
  rw [scalarTimeDerivative_reverseTimeScalar huTime]
  change -scalarTimeDerivative u (reverseTimeMap r₁ z) -
      matrixContraction (a (reverseTimeMap r₁ z).1 (reverseTimeMap r₁ z).2)
        (scalarSpatialHessian u (reverseTimeMap r₁ z)) -
      PDE.vecDot (b (reverseTimeMap r₁ z).1 (reverseTimeMap r₁ z).2)
        (scalarSpatialGradient u (reverseTimeMap r₁ z)) -
      c (reverseTimeMap r₁ z).1 (reverseTimeMap r₁ z).2 *
        u (reverseTimeMap r₁ z) =
      -(scalarTimeDerivative u (reverseTimeMap r₁ z) +
        matrixContraction (a (reverseTimeMap r₁ z).1 (reverseTimeMap r₁ z).2)
          (scalarSpatialHessian u (reverseTimeMap r₁ z)) +
        PDE.vecDot (b (reverseTimeMap r₁ z).1 (reverseTimeMap r₁ z).2)
          (scalarSpatialGradient u (reverseTimeMap r₁ z)) +
        c (reverseTimeMap r₁ z).1 (reverseTimeMap r₁ z).2 *
          u (reverseTimeMap r₁ z))
  ring

/-- Reversing time converts the classical divergence expression to the negated PDE. -/
theorem reverseTime_divergenceFormOperator_eq_neg
    {n : ℕ} {r₁ : ℝ} (a : CoefficientField n)
    (b : ℝ → PDE.Vec n → PDE.Vec n) (c : ℝ → PDE.Vec n → ℝ)
    {u : TimeVelocity n → ℝ} {z : TimeVelocity n}
    (ha : ∀ i j : Fin n,
      DifferentiableAt ℝ
        (fun y : PDE.Vec n => a (reverseTimeMap r₁ z).1 y i j) z.2)
    (huTime : HasDerivAt (fun r : ℝ => u (r, z.2))
      (scalarTimeDerivative u (reverseTimeMap r₁ z))
      (reverseTimeMap r₁ z).1)
    (huSpace : ContDiffAt ℝ 2
      (fun y : PDE.Vec n => u ((reverseTimeMap r₁ z).1, y)) z.2) :
    scalarForwardDivergenceFormOperator
      (reverseTimeCoefficient r₁ a) (reverseTimeDivergenceDrift r₁ a b)
      (reverseTimeScalarCoefficient r₁ c) (reverseTimeScalar r₁ u) z =
      -scalarParabolicZeroOrderOperator a b c u (reverseTimeMap r₁ z) := by
  have haReverse : ∀ i j : Fin n,
      DifferentiableAt ℝ (fun y : PDE.Vec n =>
        reverseTimeCoefficient r₁ a z.1 y i j) z.2 := by
    intro i j
    simpa using ha i j
  have huReverse : ContDiffAt ℝ 2 (fun y : PDE.Vec n =>
      reverseTimeScalar r₁ u (z.1, y)) z.2 := by
    simpa [reverseTimeScalar, reverseTimeMap] using huSpace
  have hflux := scalarSpatialFluxDivergence_eq_matrixContraction_add
    (a := reverseTimeCoefficient r₁ a) (u := reverseTimeScalar r₁ u)
    (z := z) haReverse huReverse
  have vecDot_sub (p q g : PDE.Vec n) :
      PDE.vecDot (p - q) g = PDE.vecDot p g - PDE.vecDot q g := by
    unfold PDE.vecDot
    simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  calc
    scalarForwardDivergenceFormOperator
        (reverseTimeCoefficient r₁ a) (reverseTimeDivergenceDrift r₁ a b)
        (reverseTimeScalarCoefficient r₁ c) (reverseTimeScalar r₁ u) z =
      scalarForwardNondivergenceOperator
        (reverseTimeCoefficient r₁ a) (reverseTimeVectorCoefficient r₁ b)
        (reverseTimeScalarCoefficient r₁ c) (reverseTimeScalar r₁ u) z := by
          unfold scalarForwardDivergenceFormOperator
            scalarForwardNondivergenceOperator reverseTimeDivergenceDrift
          rw [hflux]
          rw [vecDot_sub]
          rw [Prod.eta]
          ring
    _ = -scalarParabolicZeroOrderOperator a b c u (reverseTimeMap r₁ z) :=
      reverseTime_nondivergenceOperator_eq_neg a b c huTime

/-- The source's exact pointwise reversed divergence-form equation. -/
theorem reverseTime_divergenceForm_identity
    {n : ℕ} {r₁ : ℝ} (a : CoefficientField n)
    (b : ℝ → PDE.Vec n → PDE.Vec n) (c F : ℝ → PDE.Vec n → ℝ)
    {u : TimeVelocity n → ℝ} {z : TimeVelocity n}
    (ha : ∀ i j : Fin n,
      DifferentiableAt ℝ
        (fun y : PDE.Vec n => a (reverseTimeMap r₁ z).1 y i j) z.2)
    (huTime : HasDerivAt (fun r : ℝ => u (r, z.2))
      (scalarTimeDerivative u (reverseTimeMap r₁ z))
      (reverseTimeMap r₁ z).1)
    (huSpace : ContDiffAt ℝ 2
      (fun y : PDE.Vec n => u ((reverseTimeMap r₁ z).1, y)) z.2)
    (hPDE : scalarParabolicZeroOrderOperator a b c u
      (reverseTimeMap r₁ z) = F (reverseTimeMap r₁ z).1 z.2) :
    scalarForwardDivergenceFormOperator
      (reverseTimeCoefficient r₁ a) (reverseTimeDivergenceDrift r₁ a b)
      (reverseTimeScalarCoefficient r₁ c) (reverseTimeScalar r₁ u) z =
      -reverseTimeScalar r₁ (fun q => F q.1 q.2) z := by
  rw [reverseTime_divergenceFormOperator_eq_neg a b c ha huTime huSpace, hPDE]
  rfl

end HypoellipticAleksandrov.Parabolic
