module

public import PDEFoundation.Sobolev.Mean
public import PDEFoundation.Sobolev.W1p.Algebra

/-!
# Means of representative-level `W^{1,p}` functions

This is the compatibility layer needed by mean-zero Poincaré estimates.  The
arithmetic mean is the scalar definition from `PDEFoundation.Sobolev.Mean`;
subtracting it changes only the value representative and leaves the chosen
weak gradient exactly unchanged.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

open MeasureTheory

namespace W1pFunction

variable {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}

/-- On finite restricted volume, a `W^{1,p}` value is integrable when
`1 ≤ p`. -/
theorem integrableOn [Fact (1 ≤ p)]
    [IsFiniteMeasure (volumeOn U)]
    (u : W1pFunction U p) :
    IntegrableOn u.toFun U volume := by
  simpa only [IntegrableOn, volumeOn] using
    u.memLp.integrable Fact.out

/-- The constant representative with zero weak gradient. -/
noncomputable def const [IsFiniteMeasure (volumeOn U)]
    (c : ℝ) : W1pFunction U p where
  toFun := fun _ => c
  grad := fun _ => 0
  memLp := by
    simpa using
      (memLp_const (μ := volumeOn U) (p := p) (c := c))
  gradMemLp := by
    intro i
    exact
      memLp_const (μ := volumeOn U) (p := p) (c := (0 : ℝ))
  hasWeakGradient := by
    convert HasWeakGradientOn.of_contDiff
      (U := U) (f := fun _ : Vec d => c) contDiff_const using 1
    funext x i
    simp

@[simp]
theorem const_apply [IsFiniteMeasure (volumeOn U)]
    (c : ℝ) (x : Vec d) :
    (const (U := U) (p := p) c) x = c :=
  rfl

@[simp]
theorem const_grad [IsFiniteMeasure (volumeOn U)]
    (c : ℝ) (x : Vec d) :
    (const (U := U) (p := p) c).grad x = 0 :=
  rfl

/-- Add a scalar constant without changing the weak gradient. -/
noncomputable def addConst [Fact (1 ≤ p)]
    [IsFiniteMeasure (volumeOn U)]
    (u : W1pFunction U p) (c : ℝ) :
    W1pFunction U p :=
  u + const (U := U) (p := p) c

@[simp]
theorem addConst_apply [Fact (1 ≤ p)]
    [IsFiniteMeasure (volumeOn U)]
    (u : W1pFunction U p) (c : ℝ) (x : Vec d) :
    u.addConst c x = u x + c :=
  rfl

@[simp]
theorem addConst_grad [Fact (1 ≤ p)]
    [IsFiniteMeasure (volumeOn U)]
    (u : W1pFunction U p) (c : ℝ) (x : Vec d) :
    (u.addConst c).grad x = u.grad x := by
  simp only [addConst, add_grad, const_grad, add_zero]

/-- Subtract the arithmetic integral average from the value representative. -/
noncomputable def subAverage [Fact (1 ≤ p)]
    [IsFiniteMeasure (volumeOn U)]
    (u : W1pFunction U p) : W1pFunction U p :=
  u.addConst (-integralAverage U u.toFun)

@[simp]
theorem subAverage_apply [Fact (1 ≤ p)]
    [IsFiniteMeasure (volumeOn U)]
    (u : W1pFunction U p) (x : Vec d) :
    u.subAverage x = u x - integralAverage U u.toFun := by
  simp only [subAverage, addConst_apply, sub_eq_add_neg]

@[simp]
theorem subAverage_grad [Fact (1 ≤ p)]
    [IsFiniteMeasure (volumeOn U)]
    (u : W1pFunction U p) (x : Vec d) :
    u.subAverage.grad x = u.grad x := by
  simp only [subAverage, addConst_grad]

/-- Subtracting the average produces a zero-mean representative. -/
theorem meanZeroOn_subAverage [Fact (1 ≤ p)]
    [IsFiniteMeasure (volumeOn U)]
    (u : W1pFunction U p)
    (hUPos : 0 < volume U) (hUTop : volume U < ∞) :
    MeanZeroOn U u.subAverage.toFun := by
  have hmean :=
    meanZeroOn_sub_integralAverage
      u.integrableOn hUPos hUTop
  apply hmean.congr_ae
  exact Filter.Eventually.of_forall fun x => by
    rw [subAverage_apply]

end W1pFunction

end PDE
