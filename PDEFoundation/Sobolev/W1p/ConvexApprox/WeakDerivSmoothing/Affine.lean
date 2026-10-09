module

public import PDEFoundation.Sobolev.W1p.ConvexApprox.SmoothRepresentative
public import PDEFoundation.Sobolev.WeakDerivative.Affine
public import PDEFoundation.Sobolev.WeakDerivative.Algebra
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Affine transport for convex-domain smoothing

Precomposition by each fixed convex-approximation sampling map transports weak
partial derivatives and weak gradients with the exact affine factor `1 - ε`.
-/

@[expose] public section

open scoped Pointwise

namespace PDE

namespace HasWeakPartialDerivOn

/-- Precomposition by the affine convex-approximation sample multiplies a
weak partial derivative by the exact linear factor `1 - ε`. -/
theorem comp_convexApproxSample
    {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U)
    {i : Fin d} {u gi : Vec d → ℝ}
    (hu : HasWeakPartialDerivOn U i u gi)
    {x0 z : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 ≤ r) (hz : ‖z‖ ≤ 1)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    HasWeakPartialDerivOn U i
      (fun x => u (convexApproxSample x0 z r ε x))
      (fun x =>
        (1 - ε) * gi (convexApproxSample x0 z r ε x)) := by
  let a : ℝ := 1 - ε
  let b : Vec d := ε • (x0 - r • z)
  let V : Set (Vec d) := translateSet b (a • U)
  have ha : 0 < a := by
    dsimp only [a]
    linarith
  have hmap :
      Set.MapsTo (convexApproxSample x0 z r ε) U U :=
    convexApproxSample_mapsTo_of_isOpenBoundedConvexDomain
      hU hball hr hz hε0 hε1.le
  have hVU : V ⊆ U := by
    exact
      translateSet_smul_subset_of_convexApproxSample_mapsTo
        (x0 := x0) (z := z) (r := r) (ε := ε) hmap
  have hV :
      IsOpenBoundedConvexDomain V := by
    simpa only [V] using
      (hU.smul_of_pos ha).translateSet b
  have hRestricted :
      HasWeakPartialDerivOn V i u gi :=
    hu.restrict hV.isOpen hVU
  have hTranslated :
      HasWeakPartialDerivOn (a • U) i
        (fun x => u (x + b)) (fun x => gi (x + b)) := by
    simpa only [V, translateSet_translateSet, add_neg_cancel,
      translateSet_zero, sub_neg_eq_add] using
      hRestricted.translate (-b)
  have hDilated :
      HasWeakPartialDerivOn U i
        (fun x => a⁻¹ * u (a • x + b))
        (fun x => gi (a • x + b)) := by
    have h :=
      hTranslated.dilate_of_pos (inv_pos.mpr ha)
    simpa only [inv_inv, smul_smul,
      inv_mul_cancel₀ ha.ne', one_smul] using h
  have hScaled := hDilated.smul a
  change
    HasWeakPartialDerivOn U i
      (fun x => a * (a⁻¹ * u (a • x + b)))
      (fun x => a * gi (a • x + b)) at hScaled
  simpa only [Pi.smul_apply, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ ha.ne', one_mul, a, b,
    convexApproxSample] using hScaled

end HasWeakPartialDerivOn

namespace HasWeakGradientOn

/-- Coordinate-gradient form of
`HasWeakPartialDerivOn.comp_convexApproxSample`. -/
theorem comp_convexApproxSample
    {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U)
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (hu : HasWeakGradientOn U u Du)
    {x0 z : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 ≤ r) (hz : ‖z‖ ≤ 1)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    HasWeakGradientOn U
      (fun x => u (convexApproxSample x0 z r ε x))
      (fun x i =>
        (1 - ε) * Du (convexApproxSample x0 z r ε x) i) := by
  intro i
  exact
    (hu i).comp_convexApproxSample
      hU hball hr hz hε0 hε1

end HasWeakGradientOn

end PDE
