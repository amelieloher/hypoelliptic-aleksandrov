module

public import PDEFoundation.Geometry.ConvexSegment
public import PDEFoundation.Measure.AffineVolume

/-!
# Integration along affine segment maps

Exact change of variables for the map sending `y` to the point with parameter
`t` on the segment from `y` to a fixed point `x`.  Convexity then controls the
image of the first half of every such segment.
-/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped Pointwise

private theorem segmentBlend_eq_smul_sub_add {d : ℕ}
    (x y : Vec d) (t : ℝ) :
    segmentBlend x t y = (1 - t) • (y - x) + x := by
  rw [segmentBlend_eq_smul_add]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

/-- Exact change of variables under segment blending toward a fixed point.

For `t < 1`, the map `y ↦ segmentBlend x t y` has linear part
`(1 - t) • id`, image
`translateSet x ((1 - t) • translateSet (-x) U)`, and inverse-Jacobian factor
`((1 - t) ^ d)⁻¹`. -/
theorem setIntegral_comp_segmentBlend_of_lt_one
    {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (x : Vec d) {t : ℝ} (ht : t < 1) (U : Set (Vec d))
    (φ : Vec d → E) :
    ∫ y in U, φ (segmentBlend x t y) ∂volume =
      ((1 - t) ^ d)⁻¹ •
        ∫ z in translateSet x
          ((1 - t) • translateSet (-x) U), φ z ∂volume := by
  have hscale : 0 < 1 - t := sub_pos.mpr ht
  have hIntegrand :
      (fun y : Vec d => φ (segmentBlend x t y)) =
        fun y => φ ((1 - t) • (y + -x) + x) := by
    funext y
    rw [segmentBlend_eq_smul_sub_add]
    simp only [sub_eq_add_neg]
  rw [hIntegrand]
  calc
    (∫ y in U, φ ((1 - t) • (y + -x) + x) ∂volume) =
        ∫ z in translateSet (-x) U,
          φ ((1 - t) • z + x) ∂volume :=
      setIntegral_comp_addRight_translateSet
        (-x) U (fun z => φ ((1 - t) • z + x))
    _ = ((1 - t) ^ d)⁻¹ •
        ∫ w in (1 - t) • translateSet (-x) U,
          φ (w + x) ∂volume :=
      setIntegral_comp_smul_of_pos hscale
        (translateSet (-x) U) (fun w => φ (w + x))
    _ = ((1 - t) ^ d)⁻¹ •
        ∫ z in translateSet x
          ((1 - t) • translateSet (-x) U), φ z ∂volume := by
      rw [setIntegral_comp_addRight_translateSet]

/-- On the first half of segments toward a point of a convex set, composition
costs at most the dimensionally sharp Jacobian factor `2 ^ d`.

The integrand is assumed nonnegative everywhere and integrable on `U`; no
diameter or boundedness hypothesis is involved. -/
theorem setIntegral_comp_segmentBlend_le_two_pow_mul
    {d : ℕ} {U : Set (Vec d)} {φ : Vec d → ℝ}
    {x : Vec d} {t : ℝ} (hU : Convex ℝ U) (hx : x ∈ U)
    (ht0 : 0 ≤ t) (htHalf : t ≤ (1 / 2 : ℝ))
    (hφ : IntegrableOn φ U volume) (hφNonneg : ∀ y, 0 ≤ φ y) :
    ∫ y in U, φ (segmentBlend x t y) ∂volume ≤
      (2 : ℝ) ^ d * ∫ y in U, φ y ∂volume := by
  have htOne : t < 1 := by
    linarith
  have htOneLe : t ≤ 1 := htOne.le
  have hscale : 0 < 1 - t := sub_pos.mpr htOne
  let V : Set (Vec d) :=
    translateSet x ((1 - t) • translateSet (-x) U)
  have hVU : V ⊆ U := by
    intro z hz
    rcases hz with ⟨w, hw, rfl⟩
    rcases Set.mem_smul_set.mp hw with ⟨v, hv, rfl⟩
    rcases hv with ⟨y, hy, rfl⟩
    have hsegment : segmentBlend x t y ∈ U :=
      segmentBlend_mem hU hx hy ht0 htOneLe
    have heq :
        (1 - t) • (y + -x) + x = segmentBlend x t y := by
      rw [segmentBlend_eq_smul_sub_add]
      simp only [sub_eq_add_neg]
    rw [heq]
    exact hsegment
  have hIntegralMono :
      (∫ z in V, φ z ∂volume) ≤ ∫ y in U, φ y ∂volume :=
    setIntegral_mono_set hφ
      (ae_restrict_of_ae (Filter.Eventually.of_forall hφNonneg))
      hVU.eventuallyLE
  have hIntegralNonneg : 0 ≤ ∫ z in V, φ z ∂volume :=
    setIntegral_nonneg_of_ae
      (Filter.Eventually.of_forall hφNonneg)
  have hInvScale : (1 - t)⁻¹ ≤ 2 := by
    rw [inv_le_iff_one_le_mul₀' hscale]
    linarith
  have hFactor :
      ((1 - t) ^ d)⁻¹ ≤ (2 : ℝ) ^ d := by
    calc
      ((1 - t) ^ d)⁻¹ = ((1 - t)⁻¹) ^ d :=
        (inv_pow (1 - t) d).symm
      _ ≤ (2 : ℝ) ^ d :=
        pow_le_pow_left₀ (inv_nonneg.mpr hscale.le) hInvScale d
  rw [setIntegral_comp_segmentBlend_of_lt_one x htOne U φ]
  change
    ((1 - t) ^ d)⁻¹ * (∫ z in V, φ z ∂volume) ≤
      (2 : ℝ) ^ d * ∫ y in U, φ y ∂volume
  calc
    ((1 - t) ^ d)⁻¹ * (∫ z in V, φ z ∂volume) ≤
        (2 : ℝ) ^ d * (∫ z in V, φ z ∂volume) :=
      mul_le_mul_of_nonneg_right hFactor hIntegralNonneg
    _ ≤ (2 : ℝ) ^ d * ∫ y in U, φ y ∂volume :=
      mul_le_mul_of_nonneg_left hIntegralMono (pow_nonneg (by norm_num) d)

end PDE
