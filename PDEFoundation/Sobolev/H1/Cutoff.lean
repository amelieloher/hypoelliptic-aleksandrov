module

public import PDEFoundation.Sobolev.H1.Basic
public import PDEFoundation.Sobolev.W1p.Cutoff

/-!
# Quantitative smooth cutoffs in `H¹`

This file is the exact `p = 2` facade over the generic cutoff multiplier API.
It keeps the chosen value and gradient representatives literal, including the
formula for multiplication by a squared cutoff.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

namespace H1Function

variable {d : ℕ}
variable {U inner outer : Set (Vec d)}
variable {K : ℝ}

/-- Multiply an `H¹` representative by a quantitative smooth cutoff. -/
noncomputable def mulCutoff
    (u : H1Function U)
    (η : QuantitativeSmoothCutoff inner outer K) :
    H1Function U :=
  (u.toW1pFunction.mulCutoff η (by norm_num)).toH1Function

@[simp]
theorem mulCutoff_toFun
    (u : H1Function U)
    (η : QuantitativeSmoothCutoff inner outer K) :
    (u.mulCutoff η).toFun = fun x => η.toFun x * u x := by
  simpa only [mulCutoff,
    W1pFunction.toH1Function_toFun,
    H1Function.toW1pFunction_apply] using
    u.toW1pFunction.mulCutoff_toFun η (by norm_num)

@[simp]
theorem mulCutoff_grad
    (u : H1Function U)
    (η : QuantitativeSmoothCutoff inner outer K) :
    (u.mulCutoff η).grad =
      fun x =>
        η.toFun x • u.grad x +
          u x • classicalGradient η.toFun x := by
  simpa only [mulCutoff,
    W1pFunction.toH1Function_grad,
    H1Function.toW1pFunction_grad,
    H1Function.toW1pFunction_apply] using
    u.toW1pFunction.mulCutoff_grad η (by norm_num)

/-- Exact value representative for multiplication by a squared cutoff. -/
@[simp]
theorem mulCutoff_sq_toFun
    (u : H1Function U)
    (η : QuantitativeSmoothCutoff inner outer K) :
    (u.mulCutoff η.sq).toFun = fun x => η x ^ 2 * u x := by
  simpa only [mulCutoff, W1pFunction.toH1Function_toFun,
    H1Function.toW1pFunction_apply] using
    u.toW1pFunction.mulCutoff_sq_toFun η (by norm_num)

/-- Exact gradient representative for multiplication by a squared cutoff. -/
theorem mulCutoff_sq_grad
    (u : H1Function U)
    (η : QuantitativeSmoothCutoff inner outer K) :
    (u.mulCutoff η.sq).grad =
      fun x =>
        η x ^ 2 • u.grad x +
          (2 * η x * u x) • classicalGradient η.toFun x := by
  simpa only [mulCutoff, W1pFunction.toH1Function_grad,
    H1Function.toW1pFunction_grad,
    H1Function.toW1pFunction_apply] using
    u.toW1pFunction.mulCutoff_sq_grad η (by norm_num)

/-- A cutoff has coefficient-one cost on the raw `L²` value seminorm. -/
theorem eLpNormOn_mulCutoff_toFun_le
    (u : H1Function U)
    (η : QuantitativeSmoothCutoff inner outer K) :
    eLpNormOn U 2 (u.mulCutoff η).toFun ≤
      (1 : ℝ≥0∞) * eLpNormOn U 2 u.toFun := by
  simpa only [mulCutoff, W1pFunction.toH1Function_toFun,
    H1Function.toW1pFunction_toFun] using
    u.toW1pFunction.eLpNormOn_mulCutoff_toFun_le η (by norm_num)

/-- The raw `L²` coordinate-gradient cutoff estimate retains coefficient one
on the old gradient and the explicit coefficient `K` on the value term. -/
theorem eLpNormOn_mulCutoff_grad_coord_le
    (u : H1Function U)
    (η : QuantitativeSmoothCutoff inner outer K) (i : Fin d) :
    eLpNormOn U 2 (fun x => (u.mulCutoff η).grad x i) ≤
      (1 : ℝ≥0∞) * eLpNormOn U 2 (fun x => u.grad x i) +
        ENNReal.ofReal K * eLpNormOn U 2 u.toFun := by
  simpa only [mulCutoff, W1pFunction.toH1Function_grad,
    H1Function.toW1pFunction_grad,
    H1Function.toW1pFunction_toFun] using
    u.toW1pFunction.eLpNormOn_mulCutoff_grad_coord_le η (by norm_num) i

end H1Function

end PDE
