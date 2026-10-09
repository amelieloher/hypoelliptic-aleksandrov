module

public import PDEFoundation.Geometry.AxisCube
public import PDEFoundation.Measure.BallVolume
public import PDEFoundation.Measure.CubeVolume
public import PDEFoundation.Measure.NormalizedLp
public import PDEFoundation.Sobolev.Mean
public import PDEFoundation.Sobolev.W1p.Basic

/-!
# Quantitative mean-zero Poincaré theorem conditions

The analytic proof will be supplied once for bounded open convex domains.
This file fixes the public quantitative statement and derives its round-ball
and axis-cube specializations.  In particular, the constant is chosen after
the dimension but before the exponent, so the conditions records that there is
no growth in `p`.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

open MeasureTheory

/-- `C` is a dimension-`d` mean-zero Poincaré constant, uniformly for every
finite real exponent `p ≥ 1` and every bounded open convex domain.

The norm is normalized volume, the geometric scale is the explicit Euclidean
diameter bound `D`, and the gradient magnitude is the explicit Euclidean
magnitude of the native gradient. -/
def IsUniformMeanZeroPoincareConstant (d : ℕ) (C : ℝ) : Prop :=
  0 ≤ C ∧
    ∀ (p : ℝ), 1 ≤ p →
      ∀ (U : Set (Vec d)) (D : ℝ),
        IsOpenBoundedConvexDomain U →
        HasEuclideanDiameterLE U D →
        0 ≤ D →
        0 < volume U →
        volume U < ∞ →
        ∀ u : W1pFunction U (ENNReal.ofReal p),
          MeanZeroOn U u.toFun →
          eLpMeanNormOn U (ENNReal.ofReal p) u.toFun ≤
            ENNReal.ofReal (C * D) *
              euclideanFieldELpMeanNormOn U
                (ENNReal.ofReal p) u.grad

namespace IsUniformMeanZeroPoincareConstant

/-- The normalized statement on a bounded open convex domain. This named
projection is the common theorem used by the shape-specific interfaces. -/
theorem on_domain {d : ℕ} {C : ℝ}
    (hC : IsUniformMeanZeroPoincareConstant d C)
    {p : ℝ} (hp : 1 ≤ p) {U : Set (Vec d)}
    {D : ℝ}
    (hU : IsOpenBoundedConvexDomain U)
    (hUDiameter : HasEuclideanDiameterLE U D)
    (hD : 0 ≤ D) (hUPos : 0 < volume U)
    (hUTop : volume U < ∞)
    (u : W1pFunction U (ENNReal.ofReal p))
    (huMean : MeanZeroOn U u.toFun) :
    eLpMeanNormOn U (ENNReal.ofReal p) u.toFun ≤
      ENNReal.ofReal (C * D) *
        euclideanFieldELpMeanNormOn U
          (ENNReal.ofReal p) u.grad :=
  hC.2 p hp U D hU hUDiameter hD hUPos hUTop u huMean

/-- The unnormalized form on a bounded open convex domain. The same exponent
appears on both sides, so the exact volume factors cancel without changing
the constant. -/
theorem on_domain_unnormalized {d : ℕ} {C : ℝ}
    (hC : IsUniformMeanZeroPoincareConstant d C)
    {p : ℝ} (hp : 1 ≤ p) {U : Set (Vec d)}
    {D : ℝ}
    (hU : IsOpenBoundedConvexDomain U)
    (hUDiameter : HasEuclideanDiameterLE U D)
    (hD : 0 ≤ D) (hUPos : 0 < volume U)
    (hUTop : volume U < ∞)
    (u : W1pFunction U (ENNReal.ofReal p))
    (huMean : MeanZeroOn U u.toFun) :
    eLpNormOn U (ENNReal.ofReal p) u.toFun ≤
      ENNReal.ofReal (C * D) *
        euclideanFieldELpNormOn U (ENNReal.ofReal p) u.grad := by
  have hNormalized :=
    hC.on_domain hp hU hUDiameter hD hUPos hUTop u huMean
  rw [eLpNormOn_eq_volume_rpow_mul_eLpMeanNormOn
      hUPos hUTop,
    euclideanFieldELpNormOn_eq_volume_rpow_mul
      hUPos hUTop]
  calc
    volume U ^ (1 / ENNReal.ofReal p).toReal *
          eLpMeanNormOn U (ENNReal.ofReal p) u.toFun ≤
        volume U ^ (1 / ENNReal.ofReal p).toReal *
          (ENNReal.ofReal (C * D) *
            euclideanFieldELpMeanNormOn U
              (ENNReal.ofReal p) u.grad) :=
      mul_le_mul_right hNormalized _
    _ = ENNReal.ofReal (C * D) *
        (volume U ^ (1 / ENNReal.ofReal p).toReal *
          euclideanFieldELpMeanNormOn U
            (ENNReal.ofReal p) u.grad) := by
      ac_rfl

/-- The round-ball specialization has the explicit diameter `2 * R`. -/
theorem on_euclideanBall {d : ℕ} {C : ℝ}
    (hC : IsUniformMeanZeroPoincareConstant d C)
    {p : ℝ} (hp : 1 ≤ p) (x₀ : Vec d)
    {R : ℝ} (hR : 0 < R)
    (u : W1pFunction (euclideanBall x₀ R) (ENNReal.ofReal p))
    (huMean : MeanZeroOn (euclideanBall x₀ R) u.toFun) :
    eLpMeanNormOn (euclideanBall x₀ R)
        (ENNReal.ofReal p) u.toFun ≤
      ENNReal.ofReal (C * (2 * R)) *
        euclideanFieldELpMeanNormOn (euclideanBall x₀ R)
          (ENNReal.ofReal p) u.grad := by
  exact
    hC.on_domain hp
      (isOpenBoundedConvexDomain_euclideanBall x₀ hR)
      (hasEuclideanDiameterLE_euclideanBall x₀ hR)
      (mul_nonneg (by norm_num) hR.le)
      (volume_euclideanBall_pos x₀ hR)
      (lt_top_iff_ne_top.mpr
        (volume_euclideanBall_ne_top x₀ hR.le))
      u huMean

/-- Unnormalized round-ball specialization. -/
theorem on_euclideanBall_unnormalized {d : ℕ} {C : ℝ}
    (hC : IsUniformMeanZeroPoincareConstant d C)
    {p : ℝ} (hp : 1 ≤ p) (x₀ : Vec d)
    {R : ℝ} (hR : 0 < R)
    (u : W1pFunction (euclideanBall x₀ R) (ENNReal.ofReal p))
    (huMean : MeanZeroOn (euclideanBall x₀ R) u.toFun) :
    eLpNormOn (euclideanBall x₀ R)
        (ENNReal.ofReal p) u.toFun ≤
      ENNReal.ofReal (C * (2 * R)) *
        euclideanFieldELpNormOn (euclideanBall x₀ R)
          (ENNReal.ofReal p) u.grad := by
  exact
    hC.on_domain_unnormalized hp
      (isOpenBoundedConvexDomain_euclideanBall x₀ hR)
      (hasEuclideanDiameterLE_euclideanBall x₀ hR)
      (mul_nonneg (by norm_num) hR.le)
      (volume_euclideanBall_pos x₀ hR)
      (lt_top_iff_ne_top.mpr
        (volume_euclideanBall_ne_top x₀ hR.le))
      u huMean

/-- The axis-cube specialization has the explicit diameter
`sqrt d * L`. -/
theorem on_axisCube {d : ℕ} {C : ℝ}
    (hC : IsUniformMeanZeroPoincareConstant d C)
    {p : ℝ} (hp : 1 ≤ p) (z : Vec d)
    {L : ℝ} (hL : 0 < L)
    (u : W1pFunction (axisCube z L) (ENNReal.ofReal p))
    (huMean : MeanZeroOn (axisCube z L) u.toFun) :
    eLpMeanNormOn (axisCube z L)
        (ENNReal.ofReal p) u.toFun ≤
      ENNReal.ofReal (C * (Real.sqrt d * L)) *
        euclideanFieldELpMeanNormOn (axisCube z L)
          (ENNReal.ofReal p) u.grad := by
  exact
    hC.on_domain hp
      (isOpenBoundedConvexDomain_axisCube z L)
      (hasEuclideanDiameterLE_axisCube z hL.le)
      (mul_nonneg (Real.sqrt_nonneg d) hL.le)
      (volume_axisCube_pos z hL)
      (lt_top_iff_ne_top.mpr (volume_axisCube_ne_top z L))
      u huMean

/-- Unnormalized axis-cube specialization. -/
theorem on_axisCube_unnormalized {d : ℕ} {C : ℝ}
    (hC : IsUniformMeanZeroPoincareConstant d C)
    {p : ℝ} (hp : 1 ≤ p) (z : Vec d)
    {L : ℝ} (hL : 0 < L)
    (u : W1pFunction (axisCube z L) (ENNReal.ofReal p))
    (huMean : MeanZeroOn (axisCube z L) u.toFun) :
    eLpNormOn (axisCube z L)
        (ENNReal.ofReal p) u.toFun ≤
      ENNReal.ofReal (C * (Real.sqrt d * L)) *
        euclideanFieldELpNormOn (axisCube z L)
          (ENNReal.ofReal p) u.grad := by
  exact
    hC.on_domain_unnormalized hp
      (isOpenBoundedConvexDomain_axisCube z L)
      (hasEuclideanDiameterLE_axisCube z hL.le)
      (mul_nonneg (Real.sqrt_nonneg d) hL.le)
      (volume_axisCube_pos z hL)
      (lt_top_iff_ne_top.mpr (volume_axisCube_ne_top z L))
      u huMean

end IsUniformMeanZeroPoincareConstant

end PDE
