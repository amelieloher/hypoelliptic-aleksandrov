module

public import PDEFoundation.Sobolev.H1.Basic
public import PDEFoundation.Sobolev.W1p.Truncation

/-!
# Positive-part truncation in `H¹`

This file is the exact `p = 2` facade for the generic `W^{1,p}` positive-part
construction. It preserves the concrete value and gradient representatives
used by the application repositories; no analytic argument is repeated here.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

open MeasureTheory

namespace H1Function

variable {d : ℕ} {U : Set (Vec d)}

/-- Positive-part truncation of an `H¹` representative at a constant level. -/
noncomputable def positivePartSubConst
    (hU : IsOpenBoundedConvexDomain U)
    (u : H1Function U) (c : ℝ) :
    H1Function U :=
  (u.toW1pFunction.positivePartSubConst
    hU (by norm_num) (by norm_num) c).toH1Function

@[simp]
theorem positivePartSubConst_toFun
    (hU : IsOpenBoundedConvexDomain U)
    (u : H1Function U) (c : ℝ) :
    (u.positivePartSubConst hU c).toFun =
      fun x => max (u.toFun x - c) 0 :=
  rfl

@[simp]
theorem positivePartSubConst_grad
    (hU : IsOpenBoundedConvexDomain U)
    (u : H1Function U) (c : ℝ) :
    (u.positivePartSubConst hU c).grad =
      fun x =>
        {y | c < u.toFun y}.indicator u.grad x :=
  rfl

/-- Positive-part truncation contracts the raw value `L²` seminorm relative
to the shifted representative, with sharp constant one. -/
theorem eLpNormOn_positivePartSubConst_toFun_le
    (hU : IsOpenBoundedConvexDomain U)
    (u : H1Function U) (c : ℝ) :
    eLpNormOn U 2 (u.positivePartSubConst hU c).toFun ≤
      eLpNormOn U 2 (fun x => u.toFun x - c) := by
  simpa only [positivePartSubConst,
    W1pFunction.toH1Function_toFun,
    H1Function.toW1pFunction_toFun] using
    W1pFunction.eLpNormOn_positivePartSubConst_toFun_le
      hU (by norm_num) (by norm_num) u.toW1pFunction c

/-- Positive-part truncation contracts each native gradient-coordinate `L²`
seminorm with sharp constant one. -/
theorem eLpNormOn_positivePartSubConst_grad_coord_le
    (hU : IsOpenBoundedConvexDomain U)
    (u : H1Function U) (c : ℝ) (i : Fin d) :
    eLpNormOn U 2
        (fun x => (u.positivePartSubConst hU c).grad x i) ≤
      eLpNormOn U 2 (fun x => u.grad x i) := by
  simpa only [positivePartSubConst,
    W1pFunction.toH1Function_grad,
    H1Function.toW1pFunction_grad] using
    W1pFunction.eLpNormOn_positivePartSubConst_grad_coord_le
      hU (by norm_num) (by norm_num) u.toW1pFunction c i

/-- Existential positive-part facade matching LIH's representative-level
interface. -/
theorem exists_h1_max_sub_const
    (hU : IsOpenBoundedConvexDomain U)
    (u : H1Function U) (c : ℝ) :
    ∃ v : H1Function U,
      v.toFun = (fun x => max (u.toFun x - c) 0) ∧
      ∀ᵐ x ∂(volumeOn U),
        v.grad x =
          {y | c < u.toFun y}.indicator u.grad x :=
  ⟨u.positivePartSubConst hU c, rfl,
    Filter.Eventually.of_forall fun _ => rfl⟩

end H1Function

end PDE
