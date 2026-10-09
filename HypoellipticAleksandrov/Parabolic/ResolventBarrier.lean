module

public import HypoellipticAleksandrov.Parabolic.HarnackGeometry
public import HypoellipticAleksandrov.Parabolic.Operator
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# The parabolic resolvent barrier

This module implements the hyperbolic-cosine barrier in Krylov--Safonov,
Lemma 3.1, specialized to the second-order operator without lower-order terms.
It proves the time derivative, velocity Hessian, matrix contraction, and exact
forward-operator formula before establishing the coefficient-uniform strict
sign under pointwise two-sided Loewner ellipticity.

The coefficient field is used only at the evaluation point. In particular,
the result requires no coefficient regularity or off-point ellipticity.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Matrix
open scoped BigOperators MatrixOrder

/-- The scalar phase of the Krylov--Safonov resolvent barrier. -/
def resolventPhase {d : ℕ} (a rho : ℝ) (z : TimeVelocity d) : ℝ :=
  a * Real.sqrt rho * (PDE.vecNormSq z.2 - z.1)

/-- The hyperbolic-cosine resolvent barrier. -/
def resolventBarrier {d : ℕ} (a rho : ℝ) : TimeVelocity d → ℝ :=
  fun z => Real.cosh (resolventPhase a rho z)

private theorem fderiv_timeCoordinate_apply {d : ℕ}
    (z w : TimeVelocity d) :
    fderiv ℝ (fun y : TimeVelocity d => y.1) z w = w.1 := by
  rw [(hasFDerivAt_fst (𝕜 := ℝ) (p := z)).fderiv]
  rfl

private theorem fderiv_velocityCoordinate_apply {d : ℕ} (i : Fin d)
    (z w : TimeVelocity d) :
    fderiv ℝ (fun y : TimeVelocity d => y.2 i) z w = w.2 i := by
  have h :=
    (hasFDerivAt_apply (𝕜 := ℝ) i z.2).comp z
      (hasFDerivAt_snd (𝕜 := ℝ) (p := z))
  change (fderiv ℝ ((fun f : PDE.Vec d => f i) ∘ Prod.snd) z) w = w.2 i
  rw [h.fderiv]
  rfl

private theorem fderiv_vecDot_snd_apply {d : ℕ} (q : PDE.Vec d)
    (z w : TimeVelocity d) :
    fderiv ℝ (fun y : TimeVelocity d => PDE.vecDot y.2 q) z w =
      PDE.vecDot w.2 q := by
  classical
  unfold PDE.vecDot
  have hsum :
      fderiv ℝ (fun y : TimeVelocity d => ∑ i, y.2 i * q i) z =
        ∑ i, fderiv ℝ (fun y : TimeVelocity d => y.2 i * q i) z :=
    fderiv_fun_sum fun i _ => by fun_prop
  rw [hsum]
  simp only [ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [fderiv_mul_const (by fun_prop) (q i)]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [fderiv_velocityCoordinate_apply]
  ring

private theorem fderiv_vecNormSq_snd_apply {d : ℕ}
    (z w : TimeVelocity d) :
    fderiv ℝ (fun y : TimeVelocity d => PDE.vecNormSq y.2) z w =
      2 * PDE.vecDot z.2 w.2 := by
  classical
  unfold PDE.vecNormSq PDE.vecDot
  have hsum :
      fderiv ℝ (fun y : TimeVelocity d => ∑ i, y.2 i * y.2 i) z =
        ∑ i, fderiv ℝ (fun y : TimeVelocity d => y.2 i * y.2 i) z :=
    fderiv_fun_sum fun i _ => by fun_prop
  rw [hsum]
  simp only [ContinuousLinearMap.sum_apply]
  conv_rhs => rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [fderiv_fun_mul (by fun_prop) (by fun_prop)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  rw [fderiv_velocityCoordinate_apply]
  ring

private theorem contDiff_resolventPhase {d : ℕ} (a rho : ℝ) :
    ContDiff ℝ 2 (resolventPhase (d := d) a rho) := by
  unfold resolventPhase PDE.vecNormSq PDE.vecDot
  fun_prop

/-- The resolvent barrier is globally twice continuously differentiable. -/
theorem contDiff_resolventBarrier {d : ℕ} (a rho : ℝ) :
    ContDiff ℝ 2 (resolventBarrier (d := d) a rho) := by
  unfold resolventBarrier
  exact (contDiff_resolventPhase a rho).cosh

private theorem fderiv_resolventPhase_apply {d : ℕ} (a rho : ℝ)
    (z w : TimeVelocity d) :
    fderiv ℝ (resolventPhase a rho) z w =
      a * Real.sqrt rho * (2 * PDE.vecDot z.2 w.2 - w.1) := by
  unfold resolventPhase
  rw [fderiv_const_mul (by
    unfold PDE.vecNormSq PDE.vecDot
    fun_prop) (a * Real.sqrt rho)]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [fderiv_fun_sub (by
    unfold PDE.vecNormSq PDE.vecDot
    fun_prop) (by fun_prop)]
  simp only [ContinuousLinearMap.sub_apply]
  rw [fderiv_vecNormSq_snd_apply, fderiv_timeCoordinate_apply]

private theorem fderiv_resolventPhaseDirection_apply {d : ℕ}
    (a rho : ℝ) (w₂ z w₁ : TimeVelocity d) :
    fderiv ℝ
        (fun y : TimeVelocity d =>
          a * Real.sqrt rho *
            (2 * PDE.vecDot y.2 w₂.2 - w₂.1)) z w₁ =
      2 * (a * Real.sqrt rho) * PDE.vecDot w₁.2 w₂.2 := by
  have hdot : DifferentiableAt ℝ
      (fun y : TimeVelocity d => PDE.vecDot y.2 w₂.2) z := by
    unfold PDE.vecDot
    fun_prop
  rw [fderiv_const_mul ((hdot.const_mul 2).sub_const w₂.1)
    (a * Real.sqrt rho)]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [fderiv_fun_sub (hdot.const_mul 2) (differentiableAt_const w₂.1)]
  simp only [fderiv_const_apply, sub_zero]
  rw [fderiv_const_mul hdot 2]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [fderiv_vecDot_snd_apply]
  ring

private theorem fderiv_resolventPhase_eval_apply {d : ℕ}
    (a rho : ℝ) (w₂ z w₁ : TimeVelocity d) :
    fderiv ℝ (fun y => fderiv ℝ (resolventPhase a rho) y w₂) z w₁ =
      2 * (a * Real.sqrt rho) * PDE.vecDot w₁.2 w₂.2 := by
  have hfun :
      (fun y : TimeVelocity d =>
          fderiv ℝ (resolventPhase a rho) y w₂) =
        fun y =>
          a * Real.sqrt rho *
            (2 * PDE.vecDot y.2 w₂.2 - w₂.1) := by
    funext y
    exact fderiv_resolventPhase_apply a rho y w₂
  rw [hfun]
  exact fderiv_resolventPhaseDirection_apply a rho w₂ z w₁

private theorem fderiv_fderiv_resolventPhase_apply {d : ℕ}
    (a rho : ℝ) (z w₁ w₂ : TimeVelocity d) :
    fderiv ℝ (fderiv ℝ (resolventPhase a rho)) z w₁ w₂ =
      2 * (a * Real.sqrt rho) * PDE.vecDot w₁.2 w₂.2 := by
  let p : TimeVelocity d → ℝ := resolventPhase a rho
  have hp : ContDiff ℝ 2 p := contDiff_resolventPhase a rho
  have hDp : Differentiable ℝ (fderiv ℝ p) :=
    (hp.fderiv_right (m := 1) (by norm_num)).differentiable_one
  have hEval :
      fderiv ℝ (fun y => fderiv ℝ p y w₂) z =
        (fderiv ℝ (fderiv ℝ p) z).flip w₂ := by
    simpa only [ContinuousLinearMap.comp_zero, zero_add] using
      ((hDp z).hasFDerivAt.clm_apply
        (hasFDerivAt_const w₂ z)).fderiv
  have hEvalAt := congrArg
    (fun L : TimeVelocity d →L[ℝ] ℝ => L w₁) hEval
  simp only [ContinuousLinearMap.flip_apply] at hEvalAt
  calc
    fderiv ℝ (fderiv ℝ (resolventPhase a rho)) z w₁ w₂ =
        fderiv ℝ
          (fun y => fderiv ℝ (resolventPhase a rho) y w₂) z w₁ := by
      simpa only [p] using hEvalAt.symm
    _ = 2 * (a * Real.sqrt rho) * PDE.vecDot w₁.2 w₂.2 :=
      fderiv_resolventPhase_eval_apply a rho w₂ z w₁

private theorem fderiv_resolventBarrier_apply {d : ℕ} (a rho : ℝ)
    (z w : TimeVelocity d) :
    fderiv ℝ (resolventBarrier a rho) z w =
      Real.sinh (resolventPhase a rho z) *
        (a * Real.sqrt rho * (2 * PDE.vecDot z.2 w.2 - w.1)) := by
  unfold resolventBarrier
  rw [fderiv_cosh
    ((contDiff_resolventPhase a rho).differentiable (by norm_num) z)]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [fderiv_resolventPhase_apply]

/-- The resolvent barrier has the exact negative time derivative. -/
theorem timeDerivative_resolventBarrier {d : ℕ} (a rho : ℝ)
    (z : TimeVelocity d) :
    timeDerivative (resolventBarrier a rho) z =
      -(a * Real.sqrt rho) * Real.sinh (resolventPhase a rho z) := by
  unfold timeDerivative
  rw [fderiv_resolventBarrier_apply]
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, PDE.vecDot]
  ring

private theorem fderiv_fderiv_resolventBarrier_apply {d : ℕ}
    (a rho : ℝ) (z w₁ w₂ : TimeVelocity d) :
    fderiv ℝ (fderiv ℝ (resolventBarrier a rho)) z w₁ w₂ =
      Real.cosh (resolventPhase a rho z) *
          (a * Real.sqrt rho *
            (2 * PDE.vecDot z.2 w₁.2 - w₁.1)) *
          (a * Real.sqrt rho *
            (2 * PDE.vecDot z.2 w₂.2 - w₂.1)) +
        Real.sinh (resolventPhase a rho z) *
          (2 * (a * Real.sqrt rho) * PDE.vecDot w₁.2 w₂.2) := by
  let p : TimeVelocity d → ℝ := resolventPhase a rho
  let phi : TimeVelocity d → ℝ := resolventBarrier a rho
  have hp : ContDiff ℝ 2 p := contDiff_resolventPhase a rho
  have hphi : ContDiff ℝ 2 phi := contDiff_resolventBarrier a rho
  have hDphi : Differentiable ℝ (fderiv ℝ phi) :=
    (hphi.fderiv_right (m := 1) (by norm_num)).differentiable_one
  have hEval :
      fderiv ℝ (fun y => fderiv ℝ phi y w₂) z =
        (fderiv ℝ (fderiv ℝ phi) z).flip w₂ := by
    simpa only [ContinuousLinearMap.comp_zero, zero_add] using
      ((hDphi z).hasFDerivAt.clm_apply
        (hasFDerivAt_const w₂ z)).fderiv
  have hEvalAt := congrArg
    (fun L : TimeVelocity d →L[ℝ] ℝ => L w₁) hEval
  simp only [ContinuousLinearMap.flip_apply] at hEvalAt
  have hfun :
      (fun y : TimeVelocity d => fderiv ℝ phi y w₂) =
        fun y =>
          Real.sinh (p y) *
            (a * Real.sqrt rho *
              (2 * PDE.vecDot y.2 w₂.2 - w₂.1)) := by
    funext y
    simpa only [p, phi] using fderiv_resolventBarrier_apply a rho y w₂
  have hphaseDiff : DifferentiableAt ℝ p z :=
    hp.differentiable (by norm_num) z
  have hleft : DifferentiableAt ℝ (fun y => Real.sinh (p y)) z :=
    hphaseDiff.sinh
  have hright : DifferentiableAt ℝ
      (fun y : TimeVelocity d =>
        a * Real.sqrt rho *
          (2 * PDE.vecDot y.2 w₂.2 - w₂.1)) z := by
    unfold PDE.vecDot
    fun_prop
  calc
    fderiv ℝ (fderiv ℝ (resolventBarrier a rho)) z w₁ w₂ =
        fderiv ℝ (fun y => fderiv ℝ phi y w₂) z w₁ := by
      simpa only [phi] using hEvalAt.symm
    _ = fderiv ℝ
        (fun y =>
          Real.sinh (p y) *
            (a * Real.sqrt rho *
              (2 * PDE.vecDot y.2 w₂.2 - w₂.1))) z w₁ := by
      rw [hfun]
    _ = Real.cosh (resolventPhase a rho z) *
          (a * Real.sqrt rho *
            (2 * PDE.vecDot z.2 w₁.2 - w₁.1)) *
          (a * Real.sqrt rho *
            (2 * PDE.vecDot z.2 w₂.2 - w₂.1)) +
        Real.sinh (resolventPhase a rho z) *
          (2 * (a * Real.sqrt rho) * PDE.vecDot w₁.2 w₂.2) := by
      rw [fderiv_fun_mul hleft hright]
      simp only [ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [fderiv_resolventPhaseDirection_apply]
      rw [fderiv_sinh hphaseDiff]
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [fderiv_resolventPhase_apply]
      simp only [p]
      ring

/-- The exact velocity Hessian of the resolvent barrier. -/
theorem velocityHessian_resolventBarrier {d : ℕ} (a rho : ℝ)
    (z : TimeVelocity d) :
    velocityHessian (resolventBarrier a rho) z =
      (2 * (a * Real.sqrt rho) *
          Real.sinh (resolventPhase a rho z)) • (1 : PDE.Mat d) +
        (4 * (a * Real.sqrt rho) ^ 2 *
          Real.cosh (resolventPhase a rho z)) •
            Matrix.vecMulVec z.2 z.2 := by
  classical
  ext i j
  unfold velocityHessian
  rw [fderiv_fderiv_resolventBarrier_apply]
  simp only [Matrix.add_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst j
    simp [PDE.vecDot, Pi.single_apply]
    ring
  · have hji : j ≠ i := Ne.symm hij
    simp [PDE.vecDot, Pi.single_apply, hij, hji]
    ring

/-- Contraction with the identity matrix is the matrix trace. -/
theorem matrixContraction_one_eq_trace {d : ℕ} (A : PDE.Mat d) :
    matrixContraction A 1 = A.trace := by
  classical
  simp [matrixContraction, Matrix.trace, Matrix.diag, Matrix.one_apply]

/-- Contraction with `v vᵀ` is the quadratic form of the left matrix. -/
theorem matrixContraction_vecMulVec_eq_vecDot_mulVec {d : ℕ}
    (A : PDE.Mat d) (v : PDE.Vec d) :
    matrixContraction A (Matrix.vecMulVec v v) =
      PDE.vecDot v (A *ᵥ v) := by
  classical
  unfold matrixContraction PDE.vecDot Matrix.mulVec dotProduct
  simp only [Matrix.vecMulVec_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  ring

/-- The exact contraction of a coefficient matrix with the barrier Hessian. -/
theorem matrixContraction_velocityHessian_resolventBarrier {d : ℕ}
    (A : PDE.Mat d) (a rho : ℝ) (z : TimeVelocity d) :
    matrixContraction A (velocityHessian (resolventBarrier a rho) z) =
      2 * (a * Real.sqrt rho) *
          Real.sinh (resolventPhase a rho z) * A.trace +
        4 * (a * Real.sqrt rho) ^ 2 *
          Real.cosh (resolventPhase a rho z) *
            PDE.vecDot z.2 (A *ᵥ z.2) := by
  rw [velocityHessian_resolventBarrier,
    matrixContraction_add_right, matrixContraction_smul_right,
    matrixContraction_smul_right, matrixContraction_one_eq_trace,
    matrixContraction_vecMulVec_eq_vecDot_mulVec]

/-- The exact project-sign resolvent expression for the barrier. -/
theorem parabolicOperator_add_resolvent_resolventBarrier {d : ℕ}
    (A : CoefficientField d) (a rho : ℝ) (z : TimeVelocity d) :
    parabolicOperator A (resolventBarrier a rho) z +
        rho * resolventBarrier a rho z =
      rho * Real.cosh (resolventPhase a rho z) -
        (a * Real.sqrt rho) * Real.sinh (resolventPhase a rho z) *
          (1 + 2 * (coefficientAt A z).trace) -
        4 * (a * Real.sqrt rho) ^ 2 *
          Real.cosh (resolventPhase a rho z) *
            PDE.vecDot z.2 ((coefficientAt A z) *ᵥ z.2) := by
  rw [parabolicOperator_apply, timeDerivative_resolventBarrier,
    matrixContraction_velocityHessian_resolventBarrier]
  simp only [resolventBarrier]
  ring

/-- A positive lower Loewner bound makes every quadratic form nonnegative. -/
theorem vecDot_mulVec_nonneg_of_loewner_lower {d : ℕ}
    {lam : ℝ} {A : PDE.Mat d} (hlam : 0 < lam)
    (hlower : lam • (1 : PDE.Mat d) ≤ A) (v : PDE.Vec d) :
    0 ≤ PDE.vecDot v (A *ᵥ v) := by
  have hA : A.PosDef := HypoellipticAleksandrov.posDef_of_loewner_lower hlam hlower
  simpa only [star_trivial, PDE.vecDot, dotProduct] using hA.posSemidef.dotProduct_mulVec_nonneg v

/-- An upper Loewner bound gives the corresponding quadratic-form bound. -/
theorem vecDot_mulVec_le_of_loewner_upper {d : ℕ}
    {Lam : ℝ} {A : PDE.Mat d}
    (hupper : A ≤ Lam • (1 : PDE.Mat d)) (v : PDE.Vec d) :
    PDE.vecDot v (A *ᵥ v) ≤ Lam * PDE.vecNormSq v := by
  have hgap : (Lam • (1 : PDE.Mat d) - A).PosSemidef :=
    Matrix.le_iff.mp hupper
  have hquad := hgap.dotProduct_mulVec_nonneg v
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_sub, dotProduct_smul,
    smul_eq_mul] at hquad
  simpa only [PDE.vecNormSq, PDE.vecDot, dotProduct, mul_comm] using
    sub_nonneg.mp hquad

/-- A positive lower Loewner bound makes the matrix trace nonnegative. -/
theorem trace_nonneg_of_loewner_lower {d : ℕ}
    {lam : ℝ} {A : PDE.Mat d} (hlam : 0 < lam)
    (hlower : lam • (1 : PDE.Mat d) ≤ A) :
    0 ≤ A.trace := by
  exact (HypoellipticAleksandrov.posDef_of_loewner_lower hlam hlower).posSemidef.trace_nonneg

/-- An upper Loewner bound controls the matrix trace by dimension times its bound. -/
theorem trace_le_natCast_mul_of_loewner_upper {d : ℕ}
    {Lam : ℝ} {A : PDE.Mat d}
    (hupper : A ≤ Lam • (1 : PDE.Mat d)) :
    A.trace ≤ (d : ℝ) * Lam := by
  have hgap : (Lam • (1 : PDE.Mat d) - A).PosSemidef :=
    Matrix.le_iff.mp hupper
  have htrace := hgap.trace_nonneg
  simp only [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one,
    Fintype.card_fin, smul_eq_mul] at htrace
  nlinarith

/-- The squared Euclidean norm in the open unit coordinate cube is at most the dimension. -/
theorem vecNormSq_le_natCast_of_mem_unit_velocityCube {d : ℕ}
    {v : PDE.Vec d} (hv : v ∈ velocityCube (0 : PDE.Vec d) 1) :
    PDE.vecNormSq v ≤ (d : ℝ) := by
  rw [PDE.vecNormSq_eq_sum_sq]
  calc
    ∑ i, v i ^ 2 ≤ ∑ _i : Fin d, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _hi
      have habs : |v i| < 1 := by
        simpa only [Pi.zero_apply, sub_zero] using hv i
      have hsquare :=
        (sq_le_sq₀ (abs_nonneg (v i)) zero_le_one).mpr habs.le
      simpa only [sq_abs, one_pow] using hsquare
    _ = (d : ℝ) := by simp only [Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]

private theorem resolvent_witness_pos {D Lam : ℝ}
    (hD : 0 ≤ D) (hLam : 0 ≤ Lam) :
    let C := 1 + 2 * D * Lam
    let a := 1 / (8 * C)
    0 < a ∧ 0 < 1 - a * C - 4 * a ^ 2 * (D * Lam) := by
  dsimp only
  let C := 1 + 2 * D * Lam
  let a := 1 / (8 * C)
  change 0 < a ∧ 0 < 1 - a * C - 4 * a ^ 2 * (D * Lam)
  have hX : 0 ≤ D * Lam := mul_nonneg hD hLam
  have hC : 0 < C := by
    dsimp only [C]
    nlinarith
  have hCne : C ≠ 0 := ne_of_gt hC
  have ha : 0 < a := by
    dsimp only [a]
    positivity
  have haC : a * C = 1 / 8 := by
    dsimp only [a]
    field_simp [hCne]
  have hXC2 : D * Lam ≤ C ^ 2 := by
    dsimp only [C]
    nlinarith [sq_nonneg (D * Lam)]
  have hscaled : a ^ 2 * (D * Lam) ≤ a ^ 2 * C ^ 2 :=
    mul_le_mul_of_nonneg_left hXC2 (sq_nonneg a)
  have ha2C2 : a ^ 2 * C ^ 2 = 1 / 64 := by
    calc
      a ^ 2 * C ^ 2 = (a * C) ^ 2 := by ring
      _ = (1 / 8 : ℝ) ^ 2 := by rw [haC]
      _ = 1 / 64 := by norm_num
  have hsmall : 4 * a ^ 2 * (D * Lam) ≤ 1 / 16 := by
    nlinarith
  constructor
  · exact ha
  · rw [haC]
    nlinarith

private theorem resolvent_scalar_expression_pos
    {a rho C X tr q s : ℝ}
    (ha : 0 < a) (hC : 0 < C) (hrho : 1 < rho)
    (htr : 0 ≤ tr) (htrC : 1 + 2 * tr ≤ C) (hqX : q ≤ X)
    (hcoef : 0 < 1 - a * C - 4 * a ^ 2 * X) :
    0 < rho * Real.cosh s -
        (a * Real.sqrt rho) * Real.sinh s * (1 + 2 * tr) -
      4 * (a * Real.sqrt rho) ^ 2 * Real.cosh s * q := by
  have hrhoPos : 0 < rho := lt_trans zero_lt_one hrho
  have hsqrtPos : 0 < Real.sqrt rho := Real.sqrt_pos.2 hrhoPos
  have hkPos : 0 < a * Real.sqrt rho := mul_pos ha hsqrtPos
  have hphi : 0 < Real.cosh s := Real.cosh_pos s
  have hT : 0 < 1 + 2 * tr := by nlinarith
  have hsinhTrace :
      Real.sinh s * (1 + 2 * tr) < Real.cosh s * C := by
    calc
      Real.sinh s * (1 + 2 * tr) <
          Real.cosh s * (1 + 2 * tr) :=
        mul_lt_mul_of_pos_right (Real.sinh_lt_cosh s) hT
      _ ≤ Real.cosh s * C :=
        mul_le_mul_of_nonneg_left htrC hphi.le
  have hsinhTerm :
      (a * Real.sqrt rho) * Real.sinh s * (1 + 2 * tr) <
        (a * Real.sqrt rho) * Real.cosh s * C := by
    simpa only [mul_assoc] using
      mul_lt_mul_of_pos_left hsinhTrace hkPos
  have hquadFactor :
      0 ≤ 4 * (a * Real.sqrt rho) ^ 2 * Real.cosh s := by
    positivity
  have hquadTerm :
      4 * (a * Real.sqrt rho) ^ 2 * Real.cosh s * q ≤
        4 * (a * Real.sqrt rho) ^ 2 * Real.cosh s * X :=
    mul_le_mul_of_nonneg_left hqX hquadFactor
  have hsqrtLt : Real.sqrt rho < rho := by
    rw [Real.sqrt_lt' hrhoPos]
    nlinarith
  have hkLe : a * Real.sqrt rho ≤ a * rho :=
    mul_le_mul_of_nonneg_left hsqrtLt.le ha.le
  have hphiC : 0 ≤ Real.cosh s * C := mul_nonneg hphi.le hC.le
  have hkTerm :
      (a * Real.sqrt rho) * Real.cosh s * C ≤
        a * rho * Real.cosh s * C := by
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right hkLe hphiC
  have hkSq : (a * Real.sqrt rho) ^ 2 = a ^ 2 * rho := by
    rw [mul_pow, Real.sq_sqrt hrhoPos.le]
  have hlower :
      rho * Real.cosh s -
          (a * Real.sqrt rho) * Real.cosh s * C -
        4 * (a * Real.sqrt rho) ^ 2 * Real.cosh s * X <
      rho * Real.cosh s -
          (a * Real.sqrt rho) * Real.sinh s * (1 + 2 * tr) -
        4 * (a * Real.sqrt rho) ^ 2 * Real.cosh s * q := by
    nlinarith
  have hlower' :
      rho * Real.cosh s - a * rho * Real.cosh s * C -
          4 * a ^ 2 * rho * Real.cosh s * X ≤
        rho * Real.cosh s -
            (a * Real.sqrt rho) * Real.cosh s * C -
          4 * (a * Real.sqrt rho) ^ 2 * Real.cosh s * X := by
    rw [hkSq]
    nlinarith
  have hpositive :
      0 < rho * Real.cosh s * (1 - a * C - 4 * a ^ 2 * X) :=
    mul_pos (mul_pos hrhoPos hphi) hcoef
  calc
    0 < rho * Real.cosh s * (1 - a * C - 4 * a ^ 2 * X) := hpositive
    _ = rho * Real.cosh s - a * rho * Real.cosh s * C -
        4 * a ^ 2 * rho * Real.cosh s * X := by ring
    _ ≤ rho * Real.cosh s -
          (a * Real.sqrt rho) * Real.cosh s * C -
        4 * (a * Real.sqrt rho) ^ 2 * Real.cosh s * X := hlower'
    _ < rho * Real.cosh s -
          (a * Real.sqrt rho) * Real.sinh s * (1 + 2 * tr) -
        4 * (a * Real.sqrt rho) ^ 2 * Real.cosh s * q := hlower

/-- There is a positive resolvent-barrier parameter, chosen only from the
dimension and ellipticity constants, for which the project-sign resolvent
expression is strictly positive at every point in the unit velocity cube
obeying the two pointwise Loewner bounds. -/
theorem exists_resolventBarrier_strict_sign_of_mem_velocityCube {d : ℕ} (lam Lam : ℝ)
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam) :
    ∃ a > 0, ∀ rho > 1, ∀ A : CoefficientField d, ∀ z,
      z.2 ∈ velocityCube 0 1 →
      lam • (1 : PDE.Mat d) ≤ coefficientAt A z →
      coefficientAt A z ≤ Lam • (1 : PDE.Mat d) →
      0 < parabolicOperator A (resolventBarrier a rho) z +
        rho * resolventBarrier a rho z := by
  let D : ℝ := d
  let C : ℝ := 1 + 2 * D * Lam
  let a : ℝ := 1 / (8 * C)
  have hD : 0 ≤ D := by positivity
  have hLam : 0 < Lam := lt_of_lt_of_le hlam hlamLam
  have hwitness := resolvent_witness_pos hD hLam.le
  change 0 < a ∧ 0 < 1 - a * C - 4 * a ^ 2 * (D * Lam) at hwitness
  obtain ⟨ha, hcoef⟩ := hwitness
  refine ⟨a, ha, ?_⟩
  intro rho hrho A z hzVelocity hlower hupper
  let M : PDE.Mat d := coefficientAt A z
  have htraceNonneg : 0 ≤ M.trace := by
    exact trace_nonneg_of_loewner_lower hlam hlower
  have htraceUpper : M.trace ≤ D * Lam := by
    simpa only [D] using trace_le_natCast_mul_of_loewner_upper hupper
  have hnorm : PDE.vecNormSq z.2 ≤ D := by
    simpa only [D] using vecNormSq_le_natCast_of_mem_unit_velocityCube hzVelocity
  have hquadUpper :
      PDE.vecDot z.2 (M *ᵥ z.2) ≤ D * Lam := by
    calc
      PDE.vecDot z.2 (M *ᵥ z.2) ≤ Lam * PDE.vecNormSq z.2 :=
        vecDot_mulVec_le_of_loewner_upper hupper z.2
      _ ≤ Lam * D := mul_le_mul_of_nonneg_left hnorm hLam.le
      _ = D * Lam := mul_comm _ _
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  have htraceC : 1 + 2 * M.trace ≤ C := by
    dsimp only [C]
    nlinarith
  rw [parabolicOperator_add_resolvent_resolventBarrier]
  exact resolvent_scalar_expression_pos ha hC hrho htraceNonneg
    htraceC hquadUpper hcoef

/-- There is a positive resolvent-barrier parameter, chosen only from the
dimension and ellipticity constants, for which the project-sign resolvent
expression is strictly positive at every point obeying the two pointwise
Loewner bounds. -/
theorem exists_resolventBarrier_strict_sign {d : ℕ} (lam Lam : ℝ)
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam) :
    ∃ a > 0, ∀ rho > 1, ∀ A : CoefficientField d, ∀ z,
      z ∈ parabolicBox 1 1 0 0 →
      lam • (1 : PDE.Mat d) ≤ coefficientAt A z →
      coefficientAt A z ≤ Lam • (1 : PDE.Mat d) →
      0 < parabolicOperator A (resolventBarrier a rho) z +
        rho * resolventBarrier a rho z := by
  obtain ⟨a, ha, hsign⟩ :=
    exists_resolventBarrier_strict_sign_of_mem_velocityCube lam Lam hlam hlamLam
  refine ⟨a, ha, ?_⟩
  intro rho hrho A z hz hlower hupper
  exact hsign rho hrho A z (mem_parabolicBox_iff.mp hz).2.2 hlower hupper

end HypoellipticAleksandrov.Parabolic
