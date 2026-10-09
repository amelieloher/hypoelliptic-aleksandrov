module

public import PDEFoundation.Sobolev.H1.Algebra
public import PDEFoundation.Sobolev.W1p.Mean

/-!
# Integral means for representative-level `H¹`

This file is the LIH-compatible `p = 2` facade over the generic
`W1pFunction` mean API. Constants, addition of constants, subtraction of the
average, and the zero-mean theorem are transported without repeating the
underlying integrability or weak-derivative arguments.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

open MeasureTheory

namespace H1Function

variable {d : ℕ} {U : Set (Vec d)}

/-- An `H¹(U)` value representative is integrable when restricted volume is
finite. -/
theorem integrableOn [IsFiniteMeasure (volumeOn U)]
    (u : H1Function U) :
    IntegrableOn u U volume := by
  simpa only [H1Function.toW1pFunction_toFun] using
    u.toW1pFunction.integrableOn

/-- The constant `H¹(U)` representative with zero weak gradient. -/
noncomputable def const [IsFiniteMeasure (volumeOn U)]
    (c : ℝ) : H1Function U :=
  (W1pFunction.const (U := U) (p := (2 : ℝ≥0∞)) c).toH1Function

@[simp]
theorem const_apply [IsFiniteMeasure (volumeOn U)]
    (c : ℝ) (x : Vec d) :
    (const (U := U) c) x = c :=
  rfl

@[simp]
theorem grad_const [IsFiniteMeasure (volumeOn U)]
    (c : ℝ) (x : Vec d) :
    (const (U := U) c).grad x = 0 :=
  rfl

/-- Add a scalar constant without changing the chosen weak gradient. -/
noncomputable def addConst [IsFiniteMeasure (volumeOn U)]
    (u : H1Function U) (c : ℝ) : H1Function U :=
  (u.toW1pFunction.addConst c).toH1Function

@[simp]
theorem addConst_apply [IsFiniteMeasure (volumeOn U)]
    (u : H1Function U) (c : ℝ) (x : Vec d) :
    u.addConst c x = u x + c :=
  rfl

@[simp]
theorem grad_addConst [IsFiniteMeasure (volumeOn U)]
    (u : H1Function U) (c : ℝ) (x : Vec d) :
    (u.addConst c).grad x = u.grad x := by
  simpa only [addConst, W1pFunction.toH1Function_grad,
    H1Function.toW1pFunction_grad] using
      u.toW1pFunction.addConst_grad c x

/-- Subtract a scalar constant on a bounded convex domain without exposing a
finite-measure typeclass argument in the public API. -/
noncomputable def subConst
    (u : H1Function U) (hU : IsOpenBoundedConvexDomain U)
    (c : ℝ) : H1Function U := by
  letI : IsFiniteMeasure (volumeOn U) :=
    hU.isFiniteMeasure_volumeOn
  exact u.addConst (-c)

@[simp]
theorem subConst_apply
    (u : H1Function U) (hU : IsOpenBoundedConvexDomain U)
    (c : ℝ) (x : Vec d) :
    u.subConst hU c x = u x - c := by
  let : IsFiniteMeasure (volumeOn U) :=
    hU.isFiniteMeasure_volumeOn
  rw [subConst]
  simp only [addConst_apply]
  ring

@[simp]
theorem grad_subConst
    (u : H1Function U) (hU : IsOpenBoundedConvexDomain U)
    (c : ℝ) (x : Vec d) :
    (u.subConst hU c).grad x = u.grad x := by
  let : IsFiniteMeasure (volumeOn U) :=
    hU.isFiniteMeasure_volumeOn
  rw [subConst]
  exact grad_addConst u (-c) x

/-- Subtract the arithmetic integral average without changing the chosen weak
gradient. -/
noncomputable def subAverage [IsFiniteMeasure (volumeOn U)]
    (u : H1Function U) : H1Function U :=
  u.toW1pFunction.subAverage.toH1Function

@[simp]
theorem subAverage_apply [IsFiniteMeasure (volumeOn U)]
    (u : H1Function U) (x : Vec d) :
    u.subAverage x = u x - integralAverage U u := by
  simpa only [subAverage, W1pFunction.toH1Function_apply,
    H1Function.toW1pFunction_apply,
    H1Function.toW1pFunction_toFun] using
      u.toW1pFunction.subAverage_apply x

@[simp]
theorem grad_subAverage [IsFiniteMeasure (volumeOn U)]
    (u : H1Function U) (x : Vec d) :
    u.subAverage.grad x = u.grad x := by
  simpa only [subAverage, W1pFunction.toH1Function_grad,
    H1Function.toW1pFunction_grad] using
      u.toW1pFunction.subAverage_grad x

/-- Subtracting the average gives a zero-mean `H¹` representative on a
positive finite-volume set. -/
theorem meanZeroOn_subAverage [IsFiniteMeasure (volumeOn U)]
    (u : H1Function U)
    (hUPos : 0 < volume U) (hUTop : volume U < ∞) :
    MeanZeroOn U u.subAverage := by
  simpa only [subAverage, W1pFunction.toH1Function_toFun] using
    u.toW1pFunction.meanZeroOn_subAverage hUPos hUTop

end H1Function

end PDE
