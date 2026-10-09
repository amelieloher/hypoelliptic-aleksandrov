module

public import HypoellipticAleksandrov.Measure.TimeVelocity
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-!
# Native-norm parabolic mollifier kernels

This module constructs normalized smooth compactly supported kernels on the
time--velocity carrier.  Their balls use the inherited finite-product
norm; no Euclidean metric instance is introduced here.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ContDiff ENNReal Topology

namespace HypoellipticAleksandrov.Parabolic

/-- The outer radius of the `n`th native-norm parabolic mollifier. -/
noncomputable def parabolicMollifierScale (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 1)

/-- A smooth bump with inner radius half of, and outer radius equal to, the
native-norm mollifier scale. -/
noncomputable def parabolicMollifierBump (d n : ℕ) :
    ContDiffBump (0 : TimeVelocity d) :=
  ⟨parabolicMollifierScale n / 2, parabolicMollifierScale n,
    by
      unfold parabolicMollifierScale
      positivity,
    by
      apply half_lt_self
      unfold parabolicMollifierScale
      positivity⟩

/-- The normalized native-norm mollifier against the product volume. -/
noncomputable def parabolicMollifier (d n : ℕ) : TimeVelocity d → ℝ :=
  (parabolicMollifierBump d n).normed (volume : Measure (TimeVelocity d))

/-- Every native-norm mollifier scale is positive. -/
theorem parabolicMollifierScale_pos (n : ℕ) :
    0 < parabolicMollifierScale n := by
  unfold parabolicMollifierScale
  positivity

/-- Every native-norm mollifier scale is at most one. -/
theorem parabolicMollifierScale_le_one (n : ℕ) :
    parabolicMollifierScale n ≤ 1 := by
  unfold parabolicMollifierScale
  rw [div_le_one₀]
  · norm_num
  · positivity

/-- The native-norm mollifier scales converge to zero. -/
theorem tendsto_parabolicMollifierScale_zero :
    Tendsto parabolicMollifierScale atTop (nhds 0) := by
  change Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (nhds 0)
  exact
    (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (nhds 0))

/-- The bump's outer radius is exactly its specified mollifier scale. -/
@[simp] theorem parabolicMollifierBump_rOut (d n : ℕ) :
    (parabolicMollifierBump d n).rOut = parabolicMollifierScale n :=
  rfl

/-- Each normalized native-norm mollifier is smooth. -/
theorem contDiff_parabolicMollifier (d n : ℕ) :
    ContDiff ℝ ∞ (parabolicMollifier d n) := by
  exact (parabolicMollifierBump d n).contDiff_normed

/-- Each normalized native-norm mollifier has compact topological support. -/
theorem hasCompactSupport_parabolicMollifier (d n : ℕ) :
    HasCompactSupport (parabolicMollifier d n) := by
  exact (parabolicMollifierBump d n).hasCompactSupport_normed

/-- Normalized native-norm mollifiers are pointwise nonnegative. -/
theorem parabolicMollifier_nonneg (d n : ℕ) (z : TimeVelocity d) :
    0 ≤ parabolicMollifier d n z := by
  exact (parabolicMollifierBump d n).nonneg_normed z

/-- Each normalized native-norm mollifier integrates to one against product volume. -/
theorem integral_parabolicMollifier (d n : ℕ) :
    (integral (volume : Measure (TimeVelocity d)) (parabolicMollifier d n)) = 1 := by
  exact (parabolicMollifierBump d n).integral_normed

/-- The function support is exactly the open native-norm ball at its scale. -/
theorem support_parabolicMollifier (d n : ℕ) :
    Function.support (parabolicMollifier d n) =
      Metric.ball (0 : TimeVelocity d) (parabolicMollifierScale n) := by
  exact (parabolicMollifierBump d n).support_normed_eq

/-- The topological support is exactly the closed native-norm ball at its scale. -/
theorem tsupport_parabolicMollifier (d n : ℕ) :
    tsupport (parabolicMollifier d n) =
      Metric.closedBall (0 : TimeVelocity d) (parabolicMollifierScale n) := by
  exact (parabolicMollifierBump d n).tsupport_normed_eq

end HypoellipticAleksandrov.Parabolic
