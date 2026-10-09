module

public import HypoellipticAleksandrov.Parabolic.HarnackGeometry
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Parabolic coordinate geometry for Morrey regularity

This module introduces the time--velocity parabolic coordinate distance used
by the Morrey layer.  It deliberately retains the inherited topology and
metric structure on `TimeVelocity`; the distance is a quantitative tool, not
a new metric-space instance.
-/

@[expose] public section

open Filter Set

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

/-- The coordinate parabolic distance: square-root time separation and native
velocity-norm separation. -/
noncomputable def parabolicCoordinateDist {d : Nat}
    (z w : TimeVelocity d) : Real :=
  max (Real.sqrt |z.1 - w.1|) ‖z.2 - w.2‖

/-- The open coordinate box of parabolic radius `r` about `z0`. -/
def parabolicCoordinateBox {d : Nat} (z0 : TimeVelocity d) (r : Real) :
    Set (TimeVelocity d) :=
  {z | parabolicCoordinateDist z z0 < r}

/-- A pointwise parabolic Hölder-seminorm upper bound on a set. -/
def ParabolicHolderSeminormLE {d : Nat} (S : Set (TimeVelocity d))
    (u : TimeVelocity d -> Real) (alpha K : Real) : Prop :=
  ∀ z ∈ S, ∀ w ∈ S,
    |u z - u w| <= K * parabolicCoordinateDist z w ^ alpha

/-- The parabolic coordinate distance is nonnegative. -/
theorem parabolicCoordinateDist_nonneg {d : Nat} (z w : TimeVelocity d) :
    0 ≤ parabolicCoordinateDist z w := by
  unfold parabolicCoordinateDist
  exact le_trans (Real.sqrt_nonneg _) (le_max_left _ _)

/-- The parabolic coordinate distance from a point to itself vanishes. -/
@[simp] theorem parabolicCoordinateDist_self {d : Nat} (z : TimeVelocity d) :
    parabolicCoordinateDist z z = 0 := by
  simp [parabolicCoordinateDist]

/-- The parabolic coordinate distance separates points. -/
@[simp] theorem parabolicCoordinateDist_eq_zero_iff {d : Nat}
    (z w : TimeVelocity d) : parabolicCoordinateDist z w = 0 ↔ z = w := by
  constructor
  · intro h
    change max (Real.sqrt |z.1 - w.1|) ‖z.2 - w.2‖ = 0 at h
    have htimeRoot : Real.sqrt |z.1 - w.1| = 0 := by
      apply le_antisymm
      · simpa only [h] using le_max_left (Real.sqrt |z.1 - w.1|) ‖z.2 - w.2‖
      · exact Real.sqrt_nonneg _
    have htimeAbs : |z.1 - w.1| = 0 :=
      (Real.sqrt_eq_zero (abs_nonneg _)).mp htimeRoot
    have htime : z.1 = w.1 := sub_eq_zero.mp (abs_eq_zero.mp htimeAbs)
    have hvelocityNorm : ‖z.2 - w.2‖ = 0 := by
      apply le_antisymm
      · simpa only [h] using le_max_right (Real.sqrt |z.1 - w.1|) ‖z.2 - w.2‖
      · exact norm_nonneg _
    have hvelocity : z.2 = w.2 := sub_eq_zero.mp (norm_eq_zero.mp hvelocityNorm)
    exact Prod.ext htime hvelocity
  · rintro rfl
    exact parabolicCoordinateDist_self z

/-- The parabolic coordinate distance is symmetric. -/
theorem parabolicCoordinateDist_comm {d : Nat} (z w : TimeVelocity d) :
    parabolicCoordinateDist z w = parabolicCoordinateDist w z := by
  simp [parabolicCoordinateDist, abs_sub_comm, norm_sub_rev]

/-- The square-root time component satisfies the triangle inequality. -/
private theorem sqrt_abs_sub_le_add_sqrt_abs_sub (a b c : Real) :
    Real.sqrt |a - c| ≤ Real.sqrt |a - b| + Real.sqrt |b - c| := by
  have habs : |a - c| ≤ |a - b| + |b - c| := by
    calc
      |a - c| = |(a - b) + (b - c)| := by
        congr 1
        ring
      _ ≤ |a - b| + |b - c| := abs_add_le _ _
  have hsqLeft : Real.sqrt |a - b| ^ 2 = |a - b| :=
    Real.sq_sqrt (abs_nonneg _)
  have hsqRight : Real.sqrt |b - c| ^ 2 = |b - c| :=
    Real.sq_sqrt (abs_nonneg _)
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · nlinarith [mul_nonneg (Real.sqrt_nonneg |a - b|) (Real.sqrt_nonneg |b - c|)]

/-- The parabolic coordinate distance satisfies the triangle inequality. -/
theorem parabolicCoordinateDist_triangle {d : Nat} (z y w : TimeVelocity d) :
    parabolicCoordinateDist z w ≤
      parabolicCoordinateDist z y + parabolicCoordinateDist y w := by
  apply max_le
  · calc
      Real.sqrt |z.1 - w.1| ≤
          Real.sqrt |z.1 - y.1| + Real.sqrt |y.1 - w.1| :=
        sqrt_abs_sub_le_add_sqrt_abs_sub z.1 y.1 w.1
      _ ≤ parabolicCoordinateDist z y + parabolicCoordinateDist y w := by
        exact add_le_add
          (le_max_left (Real.sqrt |z.1 - y.1|) ‖z.2 - y.2‖)
          (le_max_left (Real.sqrt |y.1 - w.1|) ‖y.2 - w.2‖)
  · calc
      ‖z.2 - w.2‖ = ‖(z.2 - y.2) + (y.2 - w.2)‖ := by
        congr 1
        abel
      _ ≤ ‖z.2 - y.2‖ + ‖y.2 - w.2‖ := norm_add_le _ _
      _ ≤ parabolicCoordinateDist z y + parabolicCoordinateDist y w := by
        exact add_le_add
          (le_max_right (Real.sqrt |z.1 - y.1|) ‖z.2 - y.2‖)
          (le_max_right (Real.sqrt |y.1 - w.1|) ‖y.2 - w.2‖)

/-- The parabolic coordinate distance is continuous in the inherited product topology. -/
theorem continuous_parabolicCoordinateDist {d : Nat} :
    Continuous (fun p : TimeVelocity d × TimeVelocity d =>
      parabolicCoordinateDist p.1 p.2) := by
  have htime : Continuous (fun p : TimeVelocity d × TimeVelocity d =>
      Real.sqrt |p.1.1 - p.2.1|) := by
    fun_prop
  have hvelocity : Continuous (fun p : TimeVelocity d × TimeVelocity d =>
      ‖p.1.2 - p.2.2‖) := by
    fun_prop
  simpa only [parabolicCoordinateDist] using htime.max hvelocity

/-- The parabolic coordinate distance to a fixed point tends to zero there. -/
theorem tendsto_parabolicCoordinateDist_nhds_self {d : Nat} (z : TimeVelocity d) :
    Tendsto (fun w => parabolicCoordinateDist w z) (nhds z) (nhds 0) := by
  have hpair : Tendsto (fun w : TimeVelocity d => (w, z)) (nhds z) (nhds (z, z)) :=
    tendsto_id.prodMk_nhds tendsto_const_nhds
  have hdist := (continuous_parabolicCoordinateDist (d := d)).tendsto (z, z)
  simpa only [Function.comp_def, parabolicCoordinateDist_self] using hdist.comp hpair

/-- Membership in a parabolic coordinate box is its defining strict inequality. -/
@[simp] theorem mem_parabolicCoordinateBox_iff {d : Nat} {z z0 : TimeVelocity d} {r : Real} :
    z ∈ parabolicCoordinateBox z0 r ↔ parabolicCoordinateDist z z0 < r :=
  Iff.rfl

/-- Parabolic coordinate boxes are open in the inherited topology. -/
theorem isOpen_parabolicCoordinateBox {d : Nat} (z0 : TimeVelocity d) (r : Real) :
    IsOpen (parabolicCoordinateBox z0 r) := by
  change IsOpen {z : TimeVelocity d | parabolicCoordinateDist z z0 < r}
  exact isOpen_lt
    ((continuous_parabolicCoordinateDist (d := d)).comp
      (continuous_id.prodMk continuous_const))
    continuous_const

/-- Parabolic affine maps scale the coordinate distance by the absolute radius. -/
theorem parabolicCoordinateDist_parabolicAffine {d : Nat} (t0 : Real) (v0 : PDE.Vec d)
    (r : Real) (z w : TimeVelocity d) :
    parabolicCoordinateDist (parabolicAffine t0 v0 r z) (parabolicAffine t0 v0 r w) =
      |r| * parabolicCoordinateDist z w := by
  have htime :
      Real.sqrt |(parabolicAffine t0 v0 r z).1 - (parabolicAffine t0 v0 r w).1| =
        |r| * Real.sqrt |z.1 - w.1| := by
    change Real.sqrt |t0 + r ^ 2 * z.1 - (t0 + r ^ 2 * w.1)| = _
    rw [show t0 + r ^ 2 * z.1 - (t0 + r ^ 2 * w.1) = r ^ 2 * (z.1 - w.1) by ring,
      abs_mul, abs_pow]
    calc
      Real.sqrt (|r| ^ 2 * |z.1 - w.1|) =
          Real.sqrt (|r| ^ 2) * Real.sqrt |z.1 - w.1| := by
        rw [Real.sqrt_mul (sq_nonneg |r|)]
      _ = |r| * Real.sqrt |z.1 - w.1| := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (abs_nonneg _)]
  have hvelocity :
      ‖(parabolicAffine t0 v0 r z).2 - (parabolicAffine t0 v0 r w).2‖ =
        |r| * ‖z.2 - w.2‖ := by
    change ‖(v0 + r • z.2) - (v0 + r • w.2)‖ = |r| * ‖z.2 - w.2‖
    rw [show (v0 + r • z.2) - (v0 + r • w.2) = r • (z.2 - w.2) by module,
      norm_smul, Real.norm_eq_abs]
  unfold parabolicCoordinateDist
  rw [htime, hvelocity, ← mul_max_of_nonneg _ _ (abs_nonneg r)]

/-- A positive parabolic affine map pulls a translated coordinate box back to its source box. -/
theorem mem_parabolicAffine_preimage_parabolicCoordinateBox_iff {d : Nat}
    {t0 r R : Real} {v0 : PDE.Vec d} {z z0 : TimeVelocity d} (hr : 0 < r) :
    parabolicAffine t0 v0 r z ∈
        parabolicCoordinateBox (parabolicAffine t0 v0 r z0) (r * R) ↔
      z ∈ parabolicCoordinateBox z0 R := by
  rw [mem_parabolicCoordinateBox_iff, mem_parabolicCoordinateBox_iff,
    parabolicCoordinateDist_parabolicAffine, abs_of_pos hr]
  constructor
  · intro h
    exact lt_of_mul_lt_mul_left h hr.le
  · intro h
    exact mul_lt_mul_of_pos_left h hr

/-- A positive parabolic affine map sends a source coordinate box into its translated box. -/
theorem mapsTo_parabolicAffine_parabolicCoordinateBox {d : Nat}
    {t0 r R : Real} {v0 : PDE.Vec d} {z0 : TimeVelocity d} (hr : 0 < r) :
    Set.MapsTo (parabolicAffine t0 v0 r)
      (parabolicCoordinateBox z0 R)
      (parabolicCoordinateBox (parabolicAffine t0 v0 r z0) (r * R)) := by
  intro z hz
  exact (mem_parabolicAffine_preimage_parabolicCoordinateBox_iff hr).mpr hz

namespace ParabolicHolderSeminormLE

/-- A positive-exponent parabolic Hölder bound yields continuity on its set. -/
theorem continuousOn {d : Nat} {S : Set (TimeVelocity d)} {u : TimeVelocity d -> Real}
    {alpha K : Real} (h : ParabolicHolderSeminormLE S u alpha K) (halpha : 0 < alpha)
    (hK : 0 <= K) : ContinuousOn u S := by
  intro z hz
  change Tendsto u (nhdsWithin z S) (nhds (u z))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hdist : Tendsto (fun w => parabolicCoordinateDist w z) (nhdsWithin z S) (nhds 0) :=
    (tendsto_parabolicCoordinateDist_nhds_self z).mono_left nhdsWithin_le_nhds
  have hpow : Tendsto (fun w => parabolicCoordinateDist w z ^ alpha) (nhdsWithin z S)
      (nhds 0) := by
    simpa only [Function.comp_def, Real.zero_rpow halpha.ne'] using
      ((Real.continuous_rpow_const halpha.le).tendsto 0).comp hdist
  have hupper : Tendsto (fun w => K * parabolicCoordinateDist w z ^ alpha)
      (nhdsWithin z S) (nhds 0) := by
    have hK_zero : K * (0 : Real) = 0 := by
      apply le_antisymm
      · exact mul_nonpos_of_nonneg_of_nonpos hK le_rfl
      · exact mul_nonneg hK le_rfl
    simpa only [hK_zero] using (tendsto_const_nhds (x := K)).mul hpow
  have hbound : ∀ᶠ w in nhdsWithin z S,
      |u w - u z| ≤ K * parabolicCoordinateDist w z ^ alpha := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact h w hw z hz
  have habs : Tendsto (fun w => |u w - u z|) (nhdsWithin z S) (nhds 0) :=
    squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) hbound hupper
  simpa only [Real.norm_eq_abs] using habs

end ParabolicHolderSeminormLE

end

end HypoellipticAleksandrov.Parabolic
