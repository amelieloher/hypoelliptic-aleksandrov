module

public import PDEFoundation.Sobolev.H1.Basic
public import PDEFoundation.Sobolev.W1p.Composition

@[expose] public section

open scoped ENNReal

/-!
# Bounded-derivative composition in `H¹`

This file is the exact `p = 2` facade for the generic `W^{1,p}` composition
theorem.  It preserves the concrete value and gradient representatives used
by the application repositories; no analytic argument is repeated here.
-/

namespace PDE

open MeasureTheory

namespace H1Function

variable {d : ℕ} {U : Set (Vec d)}

/-- The `p = 2` weak chain rule, stated directly on the representative-level
`H¹` carrier.  This is an exact transport of the generic finite-exponent
theorem. -/
theorem hasWeakGradient_comp_contDiff_of_deriv_bounded
    (hU : IsOpenBoundedConvexDomain U)
    (u : H1Function U)
    {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G)
    {M : ℝ} (hM : 0 ≤ M)
    (hderiv : ∀ t, |deriv G t| ≤ M) :
    HasWeakGradientOn U
      (fun x => G (u.toFun x))
      (fun x i => deriv G (u.toFun x) * u.grad x i) := by
  simpa only [toW1pFunction_toFun, toW1pFunction_grad] using
    W1pFunction.hasWeakGradient_comp_contDiff_of_deriv_bounded
      hU (by norm_num) (by norm_num) u.toW1pFunction hG hM hderiv

/-- Compose an `H¹` representative with a `C¹` real function whose derivative
is bounded by `M`. -/
noncomputable def compContDiffOfDerivBounded
    (hU : IsOpenBoundedConvexDomain U)
    (u : H1Function U)
    {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G)
    {M : ℝ} (hM : 0 ≤ M)
    (hderiv : ∀ t, |deriv G t| ≤ M) :
    H1Function U :=
  (u.toW1pFunction.compContDiffOfDerivBounded
    hU (by norm_num) (by norm_num)
    hG hM hderiv).toH1Function

@[simp]
theorem compContDiffOfDerivBounded_toFun
    (hU : IsOpenBoundedConvexDomain U)
    (u : H1Function U)
    {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G)
    {M : ℝ} (hM : 0 ≤ M)
    (hderiv : ∀ t, |deriv G t| ≤ M) :
    (u.compContDiffOfDerivBounded
      hU hG hM hderiv).toFun =
        fun x => G (u.toFun x) :=
  rfl

@[simp]
theorem compContDiffOfDerivBounded_grad
    (hU : IsOpenBoundedConvexDomain U)
    (u : H1Function U)
    {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G)
    {M : ℝ} (hM : 0 ≤ M)
    (hderiv : ∀ t, |deriv G t| ≤ M) :
    (u.compContDiffOfDerivBounded
      hU hG hM hderiv).grad =
        fun x i =>
          deriv G (u.toFun x) * u.grad x i :=
  rfl

/-- The sharp raw `L²` value estimate after subtracting the unavoidable
constant `G 0`. -/
theorem eLpNormOn_compContDiffOfDerivBounded_sub_apply_zero_le
    (hU : IsOpenBoundedConvexDomain U)
    (u : H1Function U)
    {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G)
    {M : ℝ} (hM : 0 ≤ M)
    (hderiv : ∀ t, |deriv G t| ≤ M) :
    eLpNormOn U 2
        (fun x =>
          (u.compContDiffOfDerivBounded
            hU hG hM hderiv).toFun x - G 0) ≤
      ENNReal.ofReal M * eLpNormOn U 2 u.toFun := by
  simpa only [compContDiffOfDerivBounded,
    W1pFunction.toH1Function_toFun,
    H1Function.toW1pFunction_toFun] using
    W1pFunction.eLpNormOn_compContDiffOfDerivBounded_sub_apply_zero_le
      hU (by norm_num) (by norm_num) u.toW1pFunction hG hM hderiv

/-- The sharp normalized `L²` value estimate after subtracting `G 0`. -/
theorem eLpMeanNormOn_compContDiffOfDerivBounded_sub_apply_zero_le
    (hU : IsOpenBoundedConvexDomain U)
    (hUPos : 0 < volume U) (hUTop : volume U < ∞)
    (u : H1Function U)
    {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G)
    {M : ℝ} (hM : 0 ≤ M)
    (hderiv : ∀ t, |deriv G t| ≤ M) :
    eLpMeanNormOn U 2
        (fun x =>
          (u.compContDiffOfDerivBounded
            hU hG hM hderiv).toFun x - G 0) ≤
      ENNReal.ofReal M * eLpMeanNormOn U 2 u.toFun := by
  simpa only [compContDiffOfDerivBounded,
    W1pFunction.toH1Function_toFun,
    H1Function.toW1pFunction_toFun] using
    W1pFunction.eLpMeanNormOn_compContDiffOfDerivBounded_sub_apply_zero_le
      hU hUPos hUTop (by norm_num) (by norm_num)
      u.toW1pFunction hG hM hderiv

/-- Each native gradient coordinate has the exact multiplier cost `M`. -/
theorem eLpNormOn_compContDiffOfDerivBounded_grad_coord_le
    (hU : IsOpenBoundedConvexDomain U)
    (u : H1Function U)
    {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G)
    {M : ℝ} (hM : 0 ≤ M)
    (hderiv : ∀ t, |deriv G t| ≤ M)
    (i : Fin d) :
    eLpNormOn U 2
        (fun x =>
          (u.compContDiffOfDerivBounded
            hU hG hM hderiv).grad x i) ≤
      ENNReal.ofReal M * eLpNormOn U 2 (fun x => u.grad x i) := by
  simpa only [compContDiffOfDerivBounded,
    W1pFunction.toH1Function_grad,
    H1Function.toW1pFunction_grad] using
    W1pFunction.eLpNormOn_compContDiffOfDerivBounded_grad_coord_le
      hU (by norm_num) (by norm_num) u.toW1pFunction hG hM hderiv i

/-- The full Euclidean gradient has the exact, dimension-free raw `L²`
multiplier cost `M`. -/
theorem euclideanFieldELpNormOn_compContDiffOfDerivBounded_grad_le
    (hU : IsOpenBoundedConvexDomain U)
    (u : H1Function U)
    {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G)
    {M : ℝ} (hM : 0 ≤ M)
    (hderiv : ∀ t, |deriv G t| ≤ M) :
    euclideanFieldELpNormOn U 2
        (u.compContDiffOfDerivBounded hU hG hM hderiv).grad ≤
      ENNReal.ofReal M * euclideanFieldELpNormOn U 2 u.grad := by
  simpa only [compContDiffOfDerivBounded,
    W1pFunction.toH1Function_grad,
    H1Function.toW1pFunction_grad] using
    W1pFunction.euclideanFieldELpNormOn_compContDiffOfDerivBounded_grad_le
      hU (by norm_num) (by norm_num) u.toW1pFunction hG hM hderiv

/-- The full Euclidean gradient has the exact, dimension-free normalized
`L²` multiplier cost `M`. -/
theorem euclideanFieldELpMeanNormOn_compContDiffOfDerivBounded_grad_le
    (hU : IsOpenBoundedConvexDomain U)
    (hUPos : 0 < volume U) (hUTop : volume U < ∞)
    (u : H1Function U)
    {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G)
    {M : ℝ} (hM : 0 ≤ M)
    (hderiv : ∀ t, |deriv G t| ≤ M) :
    euclideanFieldELpMeanNormOn U 2
        (u.compContDiffOfDerivBounded hU hG hM hderiv).grad ≤
      ENNReal.ofReal M * euclideanFieldELpMeanNormOn U 2 u.grad := by
  simpa only [compContDiffOfDerivBounded,
    W1pFunction.toH1Function_grad,
    H1Function.toW1pFunction_grad] using
    W1pFunction.euclideanFieldELpMeanNormOn_compContDiffOfDerivBounded_grad_le
      hU hUPos hUTop (by norm_num) (by norm_num)
      u.toW1pFunction hG hM hderiv

end H1Function

end PDE
