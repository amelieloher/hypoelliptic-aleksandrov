module

public import HypoellipticAleksandrov.Parabolic.MovingLensGeometry
public import HypoellipticAleksandrov.Parabolic.Operator
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Ring

/-!
# Exact moving-lens barrier calculus

This module contains only the local classical calculus for the rational
moving-lens barrier.  It uses the project convention
`P_A = ∂t - A : Dv²`.  The subsequent coefficient-uniform sign argument is
deliberately kept in a separate module.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

open Matrix
open Filter Topology
open scoped BigOperators

/-- The rank-one velocity matrix formed from the moving-lens displacement. -/
def movingLensDisplacementOuter {d : ℕ} (y : PDE.Vec d) (z : TimeVelocity d) : PDE.Mat d :=
  fun i j => movingLensDisplacement y z i * movingLensDisplacement y z j

/-- The source rational barrier on a moving lens. -/
def movingLensBarrier {d : ℕ} (xi eps : ℝ) (n : ℕ) (y : PDE.Vec d) :
    TimeVelocity d → ℝ :=
  fun z =>
    (1 - movingLensRadiusSq xi eps y z) ^ 2 /
      (movingLensDenominator xi eps z.1) ^ n

/-- The displacement outer product is the usual vector outer product. -/
theorem movingLensDisplacementOuter_eq_vecMulVec {d : ℕ} (y : PDE.Vec d)
    (z : TimeVelocity d) :
    movingLensDisplacementOuter y z =
      Matrix.vecMulVec (movingLensDisplacement y z) (movingLensDisplacement y z) :=
  rfl

/-- Pointwise `C²` regularity of the moving radius under a nonzero denominator. -/
theorem contDiffAt_movingLensRadiusSq {d : ℕ} {xi eps : ℝ} {y : PDE.Vec d}
    {z : TimeVelocity d} (hden : movingLensDenominator xi eps z.1 ≠ 0) :
    ContDiffAt ℝ 2 (movingLensRadiusSq xi eps y) z := by
  unfold movingLensRadiusSq
  apply ContDiffAt.div
  · unfold PDE.vecNormSq PDE.vecDot
    apply ContDiffAt.sum
    intro i _
    unfold movingLensDisplacement
    fun_prop
  · unfold movingLensDenominator
    fun_prop
  · exact hden

/-- Pointwise `C²` regularity of the moving barrier under a nonzero denominator. -/
theorem contDiffAt_movingLensBarrier {d : ℕ} {xi eps : ℝ} {n : ℕ} {y : PDE.Vec d}
    {z : TimeVelocity d} (hden : movingLensDenominator xi eps z.1 ≠ 0) :
    ContDiffAt ℝ 2 (movingLensBarrier xi eps n y) z := by
  unfold movingLensBarrier
  apply ContDiffAt.div
  · exact (contDiffAt_const.sub (contDiffAt_movingLensRadiusSq hden)).pow 2
  · unfold movingLensDenominator
    fun_prop
  · exact pow_ne_zero n hden

/-- On an active moving lens, the barrier is locally `C²` under the source-side
positive denominator data. -/
theorem contDiffOn_movingLensBarrier_active {d : ℕ} {xi eps tau : ℝ} {n : ℕ}
    {y : PDE.Vec d} (hxi : 0 ≤ xi) (heps : 0 < eps) :
    ContDiffOn ℝ 2 (movingLensBarrier xi eps n y) (movingLensActive xi eps tau y) := by
  intro z hz
  exact (contDiffAt_movingLensBarrier
    (movingLensDenominator_pos hxi heps hz.1.le).ne').contDiffWithinAt

private theorem fderiv_timeCoordinate_apply {d : ℕ}
    (z w : TimeVelocity d) :
    fderiv ℝ (fun q : TimeVelocity d => q.1) z w = w.1 := by
  rw [(hasFDerivAt_fst (𝕜 := ℝ) (p := z)).fderiv]
  rfl

private theorem fderiv_velocityCoordinate_apply {d : ℕ} (i : Fin d)
    (z w : TimeVelocity d) :
    fderiv ℝ (fun q : TimeVelocity d => q.2 i) z w = w.2 i := by
  have h :=
    (hasFDerivAt_apply (𝕜 := ℝ) i z.2).comp z
      (hasFDerivAt_snd (𝕜 := ℝ) (p := z))
  change (fderiv ℝ ((fun f : PDE.Vec d => f i) ∘ Prod.snd) z) w = w.2 i
  rw [h.fderiv]
  rfl

private theorem fderiv_movingLensDenominator_apply {d : ℕ} (xi eps : ℝ)
    (z w : TimeVelocity d) :
    fderiv ℝ (fun q : TimeVelocity d => movingLensDenominator xi eps q.1) z w =
      xi * w.1 := by
  unfold movingLensDenominator
  rw [fderiv_fun_add (by fun_prop) (by fun_prop),
    fderiv_const_mul (by fun_prop) xi]
  simp only [ContinuousLinearMap.smul_apply,
    smul_eq_mul, fderiv_timeCoordinate_apply, fderiv_const_apply, add_zero]

private theorem fderiv_movingLensDisplacement_apply {d : ℕ} (y : PDE.Vec d)
    (i : Fin d) (z w : TimeVelocity d) :
    fderiv ℝ (fun q : TimeVelocity d => movingLensDisplacement y q i) z w =
      w.2 i - w.1 * y i := by
  unfold movingLensDisplacement
  change fderiv ℝ (fun q : TimeVelocity d => q.2 i - q.1 * y i) z w = _
  have htime : DifferentiableAt ℝ (fun q : TimeVelocity d => q.1) z :=
    (hasFDerivAt_fst (𝕜 := ℝ) (p := z)).differentiableAt
  have hvelocity : DifferentiableAt ℝ (fun q : TimeVelocity d => q.2 i) z := by
    exact ((hasFDerivAt_apply (𝕜 := ℝ) i z.2).comp z
      (hasFDerivAt_snd (𝕜 := ℝ) (p := z))).differentiableAt
  rw [fderiv_fun_sub hvelocity (htime.mul_const (y i)),
    fderiv_fun_mul htime (differentiableAt_const (y i))]
  simp [fderiv_velocityCoordinate_apply, fderiv_timeCoordinate_apply]
  ring

private theorem fderiv_movingLensDisplacementNormSq_apply {d : ℕ} (y : PDE.Vec d)
    (z w : TimeVelocity d) :
    fderiv ℝ (fun q : TimeVelocity d => PDE.vecNormSq (movingLensDisplacement y q)) z w =
      2 * (PDE.vecDot (movingLensDisplacement y z) w.2 -
        w.1 * PDE.vecDot (movingLensDisplacement y z) y) := by
  classical
  unfold PDE.vecNormSq PDE.vecDot
  have hdispDiff (i : Fin d) : DifferentiableAt ℝ
      (fun q : TimeVelocity d => movingLensDisplacement y q i) z := by
    unfold movingLensDisplacement
    fun_prop
  have hsum :
      fderiv ℝ (fun q : TimeVelocity d =>
        ∑ i, movingLensDisplacement y q i * movingLensDisplacement y q i) z =
        ∑ i, fderiv ℝ (fun q : TimeVelocity d =>
          movingLensDisplacement y q i * movingLensDisplacement y q i) z :=
    fderiv_fun_sum fun i _ => (hdispDiff i).mul (hdispDiff i)
  rw [hsum]
  simp only [ContinuousLinearMap.sum_apply]
  calc
    ∑ i, (fderiv ℝ
        (fun q => movingLensDisplacement y q i * movingLensDisplacement y q i) z) w =
        ∑ i, 2 * movingLensDisplacement y z i * (w.2 i - w.1 * y i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [fderiv_fun_mul (hdispDiff i) (hdispDiff i)]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [fderiv_movingLensDisplacement_apply]
      ring
    _ = 2 * (∑ i, movingLensDisplacement y z i * w.2 i -
        w.1 * ∑ i, movingLensDisplacement y z i * y i) := by
      calc
        ∑ i, 2 * movingLensDisplacement y z i * (w.2 i - w.1 * y i) =
            ∑ i, (2 * movingLensDisplacement y z i * w.2 i -
              2 * w.1 * (movingLensDisplacement y z i * y i)) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = 2 * ∑ i, movingLensDisplacement y z i * w.2 i -
            2 * w.1 * ∑ i, movingLensDisplacement y z i * y i := by
          rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
          apply congrArg₂ (· - ·)
          · apply Finset.sum_congr rfl
            intro i _
            ring
          · rfl
        _ = _ := by ring

private theorem differentiableAt_movingLensDenominator {d : ℕ} (xi eps : ℝ)
    (z : TimeVelocity d) :
    DifferentiableAt ℝ (fun q : TimeVelocity d => movingLensDenominator xi eps q.1) z := by
  unfold movingLensDenominator
  fun_prop

private theorem fderiv_movingLensDenominatorInv_apply {d : ℕ} (xi eps : ℝ)
    (z w : TimeVelocity d) (hden : movingLensDenominator xi eps z.1 ≠ 0) :
    fderiv ℝ (fun q : TimeVelocity d => (movingLensDenominator xi eps q.1)⁻¹) z w =
      -(xi * w.1) / (movingLensDenominator xi eps z.1) ^ 2 := by
  let q : TimeVelocity d → ℝ := fun a => movingLensDenominator xi eps a.1
  have hq : HasFDerivAt q (fderiv ℝ q z) z :=
    (differentiableAt_movingLensDenominator xi eps z).hasFDerivAt
  have hinv := (hasFDerivAt_inv hden).comp z hq
  change fderiv ℝ ((fun x : ℝ => x⁻¹) ∘ q) z w = _
  rw [hinv.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.one_apply, smul_eq_mul]
  rw [fderiv_movingLensDenominator_apply]
  simp only [div_eq_mul_inv]
  ring

private theorem fderiv_movingLensDenominatorInvPow_apply {d : ℕ} (xi eps : ℝ)
    (n : ℕ) (z w : TimeVelocity d) (hden : movingLensDenominator xi eps z.1 ≠ 0) :
    fderiv ℝ (fun q : TimeVelocity d =>
      (movingLensDenominator xi eps q.1)⁻¹ ^ n) z w =
      (n : ℝ) * (movingLensDenominator xi eps z.1)⁻¹ ^ (n - 1) *
        (-(xi * w.1) / (movingLensDenominator xi eps z.1) ^ 2) := by
  rw [fderiv_fun_pow n]
  · simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [fderiv_movingLensDenominatorInv_apply xi eps z w hden]
    ring
  · exact (differentiableAt_movingLensDenominator xi eps z).inv hden

private theorem fderiv_movingLensRadiusSq_apply {d : ℕ} (xi eps : ℝ)
    (y : PDE.Vec d) (z w : TimeVelocity d)
    (hden : movingLensDenominator xi eps z.1 ≠ 0) :
    fderiv ℝ (movingLensRadiusSq xi eps y) z w =
      (2 * (PDE.vecDot (movingLensDisplacement y z) w.2 -
          w.1 * PDE.vecDot (movingLensDisplacement y z) y)) /
          movingLensDenominator xi eps z.1 -
        movingLensRadiusSq xi eps y z * (xi * w.1) /
          movingLensDenominator xi eps z.1 := by
  have hnum : DifferentiableAt ℝ
      (fun q : TimeVelocity d => PDE.vecNormSq (movingLensDisplacement y q)) z := by
    unfold PDE.vecNormSq PDE.vecDot movingLensDisplacement
    fun_prop
  have hinv : DifferentiableAt ℝ
      (fun q : TimeVelocity d => (movingLensDenominator xi eps q.1)⁻¹) z := by
    exact (differentiableAt_movingLensDenominator xi eps z).inv hden
  unfold movingLensRadiusSq
  change fderiv ℝ (fun q : TimeVelocity d =>
    PDE.vecNormSq (movingLensDisplacement y q) *
      (movingLensDenominator xi eps q.1)⁻¹) z w = _
  rw [fderiv_fun_mul hnum hinv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  rw [fderiv_movingLensDisplacementNormSq_apply,
    fderiv_movingLensDenominatorInv_apply xi eps z w hden]
  field_simp [hden]
  ring

private theorem fderiv_movingLensBarrier_apply {d : ℕ} (xi eps : ℝ) (n : ℕ)
    (y : PDE.Vec d) (z w : TimeVelocity d)
    (hden : movingLensDenominator xi eps z.1 ≠ 0) :
    fderiv ℝ (movingLensBarrier xi eps n y) z w =
      2 * (movingLensRadiusSq xi eps y z - 1) *
          fderiv ℝ (movingLensRadiusSq xi eps y) z w *
          (movingLensDenominator xi eps z.1)⁻¹ ^ n +
        (1 - movingLensRadiusSq xi eps y z) ^ 2 *
          fderiv ℝ (fun q : TimeVelocity d =>
            (movingLensDenominator xi eps q.1)⁻¹ ^ n) z w := by
  have hr : DifferentiableAt ℝ (movingLensRadiusSq xi eps y) z :=
    (contDiffAt_movingLensRadiusSq hden).differentiableAt (by norm_num)
  have hq : DifferentiableAt ℝ
      (fun q : TimeVelocity d => (movingLensDenominator xi eps q.1)⁻¹ ^ n) z :=
    ((differentiableAt_movingLensDenominator xi eps z).inv hden).pow n
  unfold movingLensBarrier
  have hrewrite :
      (fun q : TimeVelocity d =>
        (1 - movingLensRadiusSq xi eps y q) ^ 2 /
          (movingLensDenominator xi eps q.1) ^ n) =
        fun q => (1 - movingLensRadiusSq xi eps y q) ^ 2 *
          (movingLensDenominator xi eps q.1)⁻¹ ^ n := by
    funext q
    rw [div_eq_mul_inv, inv_pow]
  rw [hrewrite]
  have hbase : DifferentiableAt ℝ
      (fun q : TimeVelocity d => 1 - movingLensRadiusSq xi eps y q) z :=
    (differentiableAt_const (1 : ℝ)).sub hr
  have hnum : DifferentiableAt ℝ
      (fun q : TimeVelocity d => (1 - movingLensRadiusSq xi eps y q) ^ 2) z :=
    hbase.pow 2
  have hmul := congrArg (fun L : TimeVelocity d →L[ℝ] ℝ => L w)
    (fderiv_fun_mul hnum hq)
  change fderiv ℝ (fun q : TimeVelocity d =>
    (1 - movingLensRadiusSq xi eps y q) ^ 2 *
      (movingLensDenominator xi eps q.1)⁻¹ ^ n) z w = _
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul] at hmul
  rw [hmul]
  rw [fderiv_fun_pow 2 hbase]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [fderiv_fun_sub (differentiableAt_const (1 : ℝ)) hr]
  simp only [ContinuousLinearMap.neg_apply, fderiv_const_apply, zero_sub]
  ring

/-- The exact time derivative of the moving squared radius. -/
theorem timeDerivative_movingLensRadiusSq {d : ℕ} {xi eps : ℝ} {y : PDE.Vec d}
    {z : TimeVelocity d} (hden : movingLensDenominator xi eps z.1 ≠ 0) :
    timeDerivative (movingLensRadiusSq xi eps y) z =
      -(2 * PDE.vecDot (movingLensDisplacement y z) y +
        xi * movingLensRadiusSq xi eps y z) / movingLensDenominator xi eps z.1 := by
  unfold timeDerivative
  rw [fderiv_movingLensRadiusSq_apply xi eps y z (1, 0) hden]
  simp only [Pi.zero_apply, mul_zero, PDE.vecDot, Finset.sum_const_zero]
  unfold movingLensRadiusSq
  field_simp [hden]
  ring

/-- The exact time derivative of the moving-lens barrier.  The displayed
normal form uses the source convention `r - 1 = -(1 - r)`. -/
theorem timeDerivative_movingLensBarrier {d : ℕ} {xi eps : ℝ} {n : ℕ}
    {y : PDE.Vec d} {z : TimeVelocity d}
    (hden : movingLensDenominator xi eps z.1 ≠ 0) :
    timeDerivative (movingLensBarrier xi eps n y) z =
      (-2 * (movingLensRadiusSq xi eps y z - 1) *
          (2 * PDE.vecDot (movingLensDisplacement y z) y +
            xi * movingLensRadiusSq xi eps y z) -
        (n : ℝ) * xi * (1 - movingLensRadiusSq xi eps y z) ^ 2) /
          (movingLensDenominator xi eps z.1) ^ (n + 1) := by
  unfold timeDerivative
  rw [fderiv_movingLensBarrier_apply xi eps n y z (1, 0) hden,
    fderiv_movingLensRadiusSq_apply xi eps y z (1, 0) hden,
    fderiv_movingLensDenominatorInvPow_apply xi eps n z (1, 0) hden]
  simp only [Pi.zero_apply, mul_zero, PDE.vecDot, Finset.sum_const_zero]
  unfold movingLensRadiusSq
  cases n with
  | zero =>
    norm_num
    field_simp [hden]
    ring
  | succ n =>
    simp only [Nat.cast_succ, Nat.succ_sub_one, inv_pow]
    field_simp [hden]
    ring

private theorem fderiv_fderiv_apply_eq_fderiv_eval {d : ℕ}
    {w : TimeVelocity d → ℝ} {z direction₁ direction₂ : TimeVelocity d}
    (hw : ContDiffAt ℝ 2 w z) :
    fderiv ℝ (fderiv ℝ w) z direction₁ direction₂ =
      fderiv ℝ (fun a => fderiv ℝ w a direction₂) z direction₁ := by
  have hDw : DifferentiableAt ℝ (fderiv ℝ w) z :=
    (hw.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hEval :
      fderiv ℝ (fun a => fderiv ℝ w a direction₂) z =
        (fderiv ℝ (fderiv ℝ w) z).flip direction₂ := by
    simpa only [ContinuousLinearMap.comp_zero, zero_add] using
      ((hDw.hasFDerivAt.clm_apply (hasFDerivAt_const direction₂ z)).fderiv)
  have hEvalAt := congrArg
    (fun L : TimeVelocity d →L[ℝ] ℝ => L direction₁) hEval
  simpa only [ContinuousLinearMap.flip_apply] using hEvalAt.symm

private theorem fderiv_fderiv_movingLensRadiusSq_velocity_apply {d : ℕ}
    (xi eps : ℝ) (y : PDE.Vec d) (z : TimeVelocity d)
    (i j : Fin d) (hden : movingLensDenominator xi eps z.1 ≠ 0) :
    fderiv ℝ (fderiv ℝ (movingLensRadiusSq xi eps y)) z
      (0, Pi.single i 1) (0, Pi.single j 1) =
      (2 / movingLensDenominator xi eps z.1) * if i = j then 1 else 0 := by
  let r : TimeVelocity d → ℝ := movingLensRadiusSq xi eps y
  let direction₁ : TimeVelocity d := (0, Pi.single i 1)
  let direction₂ : TimeVelocity d := (0, Pi.single j 1)
  have hdenCont : ContinuousAt
      (fun a : TimeVelocity d => movingLensDenominator xi eps a.1) z := by
    unfold movingLensDenominator
    fun_prop
  have hnear : ∀ᶠ a in 𝓝 z, movingLensDenominator xi eps a.1 ≠ 0 :=
    hdenCont.eventually_ne hden
  have hfirst :
      (fun a => fderiv ℝ r a direction₂) =ᶠ[𝓝 z]
        fun a => 2 * movingLensDisplacement y a j /
          movingLensDenominator xi eps a.1 := by
    filter_upwards [hnear] with a ha
    dsimp only [r, direction₂]
    rw [fderiv_movingLensRadiusSq_apply xi eps y a (0, Pi.single j 1) ha]
    simp [PDE.vecDot, Pi.single_apply]
  have hdispDiff : DifferentiableAt ℝ
      (fun a : TimeVelocity d => movingLensDisplacement y a j) z := by
    unfold movingLensDisplacement
    fun_prop
  have hinvDiff : DifferentiableAt ℝ
      (fun a : TimeVelocity d => (movingLensDenominator xi eps a.1)⁻¹) z :=
    (differentiableAt_movingLensDenominator xi eps z).inv hden
  calc
    fderiv ℝ (fderiv ℝ r) z direction₁ direction₂ =
        fderiv ℝ (fun a => fderiv ℝ r a direction₂) z direction₁ :=
      fderiv_fderiv_apply_eq_fderiv_eval (contDiffAt_movingLensRadiusSq hden)
    _ = fderiv ℝ (fun a => 2 * movingLensDisplacement y a j /
        movingLensDenominator xi eps a.1) z direction₁ := by
      exact congrArg (fun L : TimeVelocity d →L[ℝ] ℝ => L direction₁) hfirst.fderiv_eq
    _ = (2 / movingLensDenominator xi eps z.1) * if i = j then 1 else 0 := by
      change fderiv ℝ (fun a : TimeVelocity d =>
        (2 * movingLensDisplacement y a j) *
          (movingLensDenominator xi eps a.1)⁻¹) z direction₁ = _
      rw [fderiv_fun_mul (hdispDiff.const_mul 2) hinvDiff]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        smul_eq_mul]
      rw [fderiv_movingLensDenominatorInv_apply xi eps z direction₁ hden,
        fderiv_const_mul hdispDiff 2]
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [fderiv_movingLensDisplacement_apply]
      dsimp only [direction₁]
      simp [Pi.single_apply]
      field_simp [hden]
      by_cases hij : i = j
      · simp [hij]
      · have hji : j ≠ i := Ne.symm hij
        simp [hij, hji]

/-- The exact velocity Hessian of the moving squared radius. -/
theorem velocityHessian_movingLensRadiusSq {d : ℕ} {xi eps : ℝ} {y : PDE.Vec d}
    {z : TimeVelocity d} (hden : movingLensDenominator xi eps z.1 ≠ 0) :
    velocityHessian (movingLensRadiusSq xi eps y) z =
      (2 / movingLensDenominator xi eps z.1) • (1 : PDE.Mat d) := by
  ext i j
  unfold velocityHessian
  rw [fderiv_fderiv_movingLensRadiusSq_velocity_apply xi eps y z i j hden]
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]

private theorem inv_pow_div_eq_inv_pow_succ (q : ℝ) (n : ℕ) :
    (q ^ n)⁻¹ / q = 1 / q ^ (n + 1) := by
  rw [div_eq_mul_inv, ← mul_inv, ← pow_succ, one_div]

private theorem fderiv_movingLensBarrier_velocity_apply {d : ℕ}
    (xi eps : ℝ) (n : ℕ) (y : PDE.Vec d) (z : TimeVelocity d)
    (j : Fin d) (hden : movingLensDenominator xi eps z.1 ≠ 0) :
    fderiv ℝ (movingLensBarrier xi eps n y) z (0, Pi.single j 1) =
      4 * (movingLensRadiusSq xi eps y z - 1) *
        movingLensDisplacement y z j /
          (movingLensDenominator xi eps z.1) ^ (n + 1) := by
  rw [fderiv_movingLensBarrier_apply xi eps n y z (0, Pi.single j 1) hden,
    fderiv_movingLensRadiusSq_apply xi eps y z (0, Pi.single j 1) hden,
    fderiv_movingLensDenominatorInvPow_apply xi eps n z (0, Pi.single j 1) hden]
  simp [PDE.vecDot, Pi.single_apply]
  cases n with
  | zero =>
    norm_num
    field_simp [hden]
    ring
  | succ n =>
    field_simp [hden]
    ring

private theorem fderiv_fderiv_movingLensBarrier_velocity_apply {d : ℕ}
    (xi eps : ℝ) (n : ℕ) (y : PDE.Vec d) (z : TimeVelocity d)
    (i j : Fin d) (hden : movingLensDenominator xi eps z.1 ≠ 0) :
    fderiv ℝ (fderiv ℝ (movingLensBarrier xi eps n y)) z
      (0, Pi.single i 1) (0, Pi.single j 1) =
      8 * movingLensDisplacement y z i * movingLensDisplacement y z j /
          (movingLensDenominator xi eps z.1) ^ (n + 2) +
        4 * (movingLensRadiusSq xi eps y z - 1) /
          (movingLensDenominator xi eps z.1) ^ (n + 1) * if i = j then 1 else 0 := by
  let b : TimeVelocity d → ℝ := movingLensBarrier xi eps n y
  let direction₁ : TimeVelocity d := (0, Pi.single i 1)
  let direction₂ : TimeVelocity d := (0, Pi.single j 1)
  have hdenCont : ContinuousAt
      (fun a : TimeVelocity d => movingLensDenominator xi eps a.1) z := by
    unfold movingLensDenominator
    fun_prop
  have hnear : ∀ᶠ a in 𝓝 z, movingLensDenominator xi eps a.1 ≠ 0 :=
    hdenCont.eventually_ne hden
  have hfirst :
      (fun a => fderiv ℝ b a direction₂) =ᶠ[𝓝 z]
        fun a => 4 * (movingLensRadiusSq xi eps y a - 1) *
          movingLensDisplacement y a j /
            (movingLensDenominator xi eps a.1) ^ (n + 1) := by
    filter_upwards [hnear] with a ha
    dsimp only [b, direction₂]
    exact fderiv_movingLensBarrier_velocity_apply xi eps n y a j ha
  have hr : DifferentiableAt ℝ (movingLensRadiusSq xi eps y) z :=
    (contDiffAt_movingLensRadiusSq hden).differentiableAt (by norm_num)
  have hdisp : DifferentiableAt ℝ
      (fun a : TimeVelocity d => movingLensDisplacement y a j) z := by
    unfold movingLensDisplacement
    fun_prop
  have hq : DifferentiableAt ℝ
      (fun a : TimeVelocity d =>
        (movingLensDenominator xi eps a.1)⁻¹ ^ (n + 1)) z :=
    ((differentiableAt_movingLensDenominator xi eps z).inv hden).pow (n + 1)
  calc
    fderiv ℝ (fderiv ℝ b) z direction₁ direction₂ =
        fderiv ℝ (fun a => fderiv ℝ b a direction₂) z direction₁ :=
      fderiv_fderiv_apply_eq_fderiv_eval (contDiffAt_movingLensBarrier hden)
    _ = fderiv ℝ (fun a => 4 * (movingLensRadiusSq xi eps y a - 1) *
        movingLensDisplacement y a j /
          (movingLensDenominator xi eps a.1) ^ (n + 1)) z direction₁ := by
      exact congrArg (fun L : TimeVelocity d →L[ℝ] ℝ => L direction₁) hfirst.fderiv_eq
    _ = 8 * movingLensDisplacement y z i * movingLensDisplacement y z j /
          (movingLensDenominator xi eps z.1) ^ (n + 2) +
        4 * (movingLensRadiusSq xi eps y z - 1) /
          (movingLensDenominator xi eps z.1) ^ (n + 1) * if i = j then 1 else 0 := by
      have hrewrite :
          (fun a : TimeVelocity d => 4 * (movingLensRadiusSq xi eps y a - 1) *
            movingLensDisplacement y a j /
              (movingLensDenominator xi eps a.1) ^ (n + 1)) =
            fun a => (4 * (movingLensRadiusSq xi eps y a - 1) *
              movingLensDisplacement y a j) *
                (movingLensDenominator xi eps a.1)⁻¹ ^ (n + 1) := by
        funext a
        rw [div_eq_mul_inv, inv_pow]
      rw [hrewrite]
      have hprod : DifferentiableAt ℝ (fun a : TimeVelocity d =>
          4 * (movingLensRadiusSq xi eps y a - 1) *
            movingLensDisplacement y a j) z :=
        ((differentiableAt_const (4 : ℝ)).mul (hr.sub_const 1)).mul hdisp
      rw [fderiv_fun_mul hprod hq]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        smul_eq_mul]
      have hscalar : DifferentiableAt ℝ (fun a : TimeVelocity d =>
          4 * (movingLensRadiusSq xi eps y a - 1)) z :=
        (differentiableAt_const (4 : ℝ)).mul (hr.sub_const 1)
      rw [fderiv_fun_mul hscalar hdisp]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        smul_eq_mul]
      rw [fderiv_fun_mul (differentiableAt_const (4 : ℝ)) (hr.sub_const 1)]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        smul_eq_mul, fderiv_const_apply]
      rw [fderiv_fun_sub hr (differentiableAt_const (1 : ℝ))]
      simp only [fderiv_const_apply, sub_zero]
      rw [fderiv_movingLensRadiusSq_apply xi eps y z direction₁ hden,
        fderiv_movingLensDisplacement_apply,
        fderiv_movingLensDenominatorInvPow_apply xi eps (n + 1) z direction₁ hden]
      dsimp only [direction₁]
      simp [PDE.vecDot, Pi.single_apply]
      by_cases hij : i = j
      · subst j
        simp
        ring
      · have hji : j ≠ i := Ne.symm hij
        simp [hij, hji]
        ring

/-- The exact velocity Hessian of the moving-lens barrier. -/
theorem velocityHessian_movingLensBarrier {d : ℕ} {xi eps : ℝ} {n : ℕ}
    {y : PDE.Vec d} {z : TimeVelocity d}
    (hden : movingLensDenominator xi eps z.1 ≠ 0) :
    velocityHessian (movingLensBarrier xi eps n y) z =
      (8 / (movingLensDenominator xi eps z.1) ^ (n + 2)) •
          movingLensDisplacementOuter y z +
        (4 * (movingLensRadiusSq xi eps y z - 1) /
          (movingLensDenominator xi eps z.1) ^ (n + 1)) • (1 : PDE.Mat d) := by
  ext i j
  unfold velocityHessian
  rw [fderiv_fderiv_movingLensBarrier_velocity_apply xi eps n y z i j hden]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
    movingLensDisplacementOuter, smul_eq_mul]
  ring

/-- Contraction with the identity is the matrix trace. -/
theorem movingLens_matrixContraction_one_eq_trace {d : ℕ} (A : PDE.Mat d) :
    matrixContraction A 1 = A.trace := by
  classical
  simp [matrixContraction, Matrix.trace, Matrix.diag, Matrix.one_apply]

/-- Contraction with the moving displacement outer product is its quadratic form. -/
theorem matrixContraction_movingLensDisplacementOuter {d : ℕ} (A : PDE.Mat d)
    (y : PDE.Vec d) (z : TimeVelocity d) :
    matrixContraction A (movingLensDisplacementOuter y z) =
      PDE.vecDot (movingLensDisplacement y z)
        (A *ᵥ movingLensDisplacement y z) := by
  classical
  unfold movingLensDisplacementOuter matrixContraction PDE.vecDot Matrix.mulVec dotProduct
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The exact contraction of the moving-lens barrier Hessian with an arbitrary
matrix.  No symmetry or ellipticity assumption on the matrix is used. -/
theorem matrixContraction_velocityHessian_movingLensBarrier {d : ℕ}
    (A : PDE.Mat d) {xi eps : ℝ} {n : ℕ} {y : PDE.Vec d}
    {z : TimeVelocity d} (hden : movingLensDenominator xi eps z.1 ≠ 0) :
    matrixContraction A (velocityHessian (movingLensBarrier xi eps n y) z) =
      8 * PDE.vecDot (movingLensDisplacement y z)
          (A *ᵥ movingLensDisplacement y z) /
          (movingLensDenominator xi eps z.1) ^ (n + 2) +
        4 * (movingLensRadiusSq xi eps y z - 1) * A.trace /
          (movingLensDenominator xi eps z.1) ^ (n + 1) := by
  rw [velocityHessian_movingLensBarrier hden,
    HypoellipticAleksandrov.matrixContraction_add_right,
    HypoellipticAleksandrov.matrixContraction_smul_right,
    HypoellipticAleksandrov.matrixContraction_smul_right,
    matrixContraction_movingLensDisplacementOuter,
    movingLens_matrixContraction_one_eq_trace]
  ring

/-- The project-sign moving-lens barrier identity.  Since
`P_A = ∂t - A : Dv²`, this is the source identity for `-P_A`. -/
theorem movingLensBarrier_neg_parabolicOperator_identity {d : ℕ}
    (A : CoefficientField d) {xi eps : ℝ} {n : ℕ} {y : PDE.Vec d}
    {z : TimeVelocity d} (hden : movingLensDenominator xi eps z.1 ≠ 0) :
    (movingLensDenominator xi eps z.1) ^ (n + 1) *
        (-parabolicOperator A (movingLensBarrier xi eps n y) z) =
      (n : ℝ) * xi * (1 - movingLensRadiusSq xi eps y z) ^ 2 +
        8 * (PDE.vecDot (movingLensDisplacement y z)
          (coefficientAt A z *ᵥ movingLensDisplacement y z) /
          movingLensDenominator xi eps z.1) +
        2 * (movingLensRadiusSq xi eps y z - 1) *
          (xi * movingLensRadiusSq xi eps y z +
            2 * PDE.vecDot (movingLensDisplacement y z) y +
            2 * (coefficientAt A z).trace) := by
  rw [parabolicOperator_apply,
    timeDerivative_movingLensBarrier hden,
    matrixContraction_velocityHessian_movingLensBarrier (coefficientAt A z) hden]
  field_simp [hden]
  ring

end

end HypoellipticAleksandrov.Parabolic
