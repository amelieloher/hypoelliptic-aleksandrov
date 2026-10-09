module

public import PDEFoundation.Sobolev.H1.Basic
public import PDEFoundation.Sobolev.W1p.Algebra
public import Mathlib.Algebra.Module.TransferInstance

/-!
# Linear algebra for representative-level `H¹`

The algebraic structure on `H1Function U` is transported across the exact
equivalence with `W1pFunction U 2`. Thus all analytic closure facts come from
the generic `W^{1,p}` layer; this file contains only the `p = 2`
compatibility surface used by the application repositories.
-/

@[expose] public section

namespace PDE

namespace H1Function

instance {d : ℕ} {U : Set (Vec d)} : Zero (H1Function U) :=
  h1FunctionEquivW1pFunction.zero

instance {d : ℕ} {U : Set (Vec d)} : Add (H1Function U) :=
  h1FunctionEquivW1pFunction.add

instance {d : ℕ} {U : Set (Vec d)} : Neg (H1Function U) :=
  h1FunctionEquivW1pFunction.Neg

instance {d : ℕ} {U : Set (Vec d)} : Sub (H1Function U) :=
  h1FunctionEquivW1pFunction.sub

instance {d : ℕ} {U : Set (Vec d)} : SMul ℝ (H1Function U) :=
  h1FunctionEquivW1pFunction.smul ℝ

@[simp]
theorem zero_toFun {d : ℕ} {U : Set (Vec d)} :
    (0 : H1Function U).toFun = 0 :=
  rfl

@[simp]
theorem zero_grad {d : ℕ} {U : Set (Vec d)} :
    (0 : H1Function U).grad = 0 :=
  rfl

@[simp]
theorem add_toFun {d : ℕ} {U : Set (Vec d)}
    (u v : H1Function U) :
    (u + v).toFun = fun x => u x + v x :=
  rfl

@[simp]
theorem add_grad {d : ℕ} {U : Set (Vec d)}
    (u v : H1Function U) :
    (u + v).grad = fun x => u.grad x + v.grad x :=
  rfl

@[simp]
theorem neg_toFun {d : ℕ} {U : Set (Vec d)}
    (u : H1Function U) :
    (-u).toFun = fun x => -u x :=
  rfl

@[simp]
theorem neg_grad {d : ℕ} {U : Set (Vec d)}
    (u : H1Function U) :
    (-u).grad = fun x => -u.grad x :=
  rfl

@[simp]
theorem sub_toFun {d : ℕ} {U : Set (Vec d)}
    (u v : H1Function U) :
    (u - v).toFun = fun x => u x - v x :=
  rfl

@[simp]
theorem sub_grad {d : ℕ} {U : Set (Vec d)}
    (u v : H1Function U) :
    (u - v).grad = fun x => u.grad x - v.grad x :=
  rfl

@[simp]
theorem smul_toFun {d : ℕ} {U : Set (Vec d)}
    (c : ℝ) (u : H1Function U) :
    (c • u).toFun = fun x => c * u x :=
  rfl

@[simp]
theorem smul_grad {d : ℕ} {U : Set (Vec d)}
    (c : ℝ) (u : H1Function U) :
    (c • u).grad = fun x => c • u.grad x :=
  rfl

instance {d : ℕ} {U : Set (Vec d)} : AddCommGroup (H1Function U) :=
  h1FunctionEquivW1pFunction.addCommGroup

instance {d : ℕ} {U : Set (Vec d)} : Module ℝ (H1Function U) :=
  h1FunctionEquivW1pFunction.addEquiv.module ℝ

end H1Function

end PDE
