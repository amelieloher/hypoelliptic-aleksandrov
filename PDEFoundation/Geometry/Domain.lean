module

public import PDEFoundation.Ambient.EuclideanNorm
public import PDEFoundation.Geometry.Affine
public import Mathlib.Basic.Real.Pointwise
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Quantitative domain predicates

The compatibility boundedness predicate is retained alongside an explicit
Euclidean-diameter bound for quantitative Sobolev estimates.
-/

@[expose] public section

open scoped Pointwise

namespace PDE

/-- Coordinatewise boundedness, compatible with the existing LIH API. -/
def IsBoundedDomain {d : ℕ} (U : Set (Vec d)) : Prop :=
  ∃ R : ℝ, 0 < R ∧ ∀ x ∈ U, ∀ i, |x i| ≤ R

/-- The minimal measurable bounded domain class used by Sobolev integration. -/
def IsSobolevRegularDomain {d : ℕ} (U : Set (Vec d)) : Prop :=
  MeasurableSet U ∧ IsBoundedDomain U

/-- Every pair of points in `U` is at Euclidean distance at most `D`. -/
def HasEuclideanDiameterLE {d : ℕ}
    (U : Set (Vec d)) (D : ℝ) : Prop :=
  ∀ ⦃x⦄, x ∈ U → ∀ ⦃y⦄, y ∈ U →
    vecEuclideanNorm (x - y) ≤ D

namespace IsSobolevRegularDomain

theorem measurableSet {d : ℕ} {U : Set (Vec d)}
    (hU : IsSobolevRegularDomain U) :
    MeasurableSet U :=
  hU.1

theorem isBoundedDomain {d : ℕ} {U : Set (Vec d)}
    (hU : IsSobolevRegularDomain U) :
    IsBoundedDomain U :=
  hU.2

end IsSobolevRegularDomain

namespace HasEuclideanDiameterLE

theorem mono {d : ℕ} {U V : Set (Vec d)} {D : ℝ}
    (hU : HasEuclideanDiameterLE U D) (hVU : V ⊆ U) :
    HasEuclideanDiameterLE V D := by
  intro x hx y hy
  exact hU (hVU hx) (hVU hy)

/-- A diameter bound for a nonempty set is necessarily nonnegative. -/
theorem nonneg {d : ℕ} {U : Set (Vec d)} {D : ℝ}
    (hU : HasEuclideanDiameterLE U D) (hU_nonempty : U.Nonempty) :
    0 ≤ D := by
  rcases hU_nonempty with ⟨x, hx⟩
  have hxx := hU hx hx
  have hzero : vecEuclideanNorm (0 : Vec d) = 0 :=
    vecEuclideanNorm_eq_zero_iff.2 rfl
  simpa only [sub_self, hzero] using hxx

/-- Translating a set preserves its Euclidean diameter bound exactly. -/
theorem translateSet {d : ℕ} {U : Set (Vec d)} {D : ℝ}
    (hU : HasEuclideanDiameterLE U D) (z : Vec d) :
    HasEuclideanDiameterLE (PDE.translateSet z U) D := by
  intro x hx y hy
  rcases hx with ⟨x', hx', rfl⟩
  rcases hy with ⟨y', hy', rfl⟩
  simpa only [add_sub_add_right_eq_sub] using hU hx' hy'

/-- A set and any of its translates have the same diameter-bound predicate. -/
theorem translateSet_iff {d : ℕ} {U : Set (Vec d)}
    {D : ℝ} (z : Vec d) :
    HasEuclideanDiameterLE (PDE.translateSet z U) D ↔
      HasEuclideanDiameterLE U D := by
  constructor
  · intro hTranslated x hx y hy
    have hxTranslated : x + z ∈ PDE.translateSet z U :=
      ⟨x, hx, rfl⟩
    have hyTranslated : y + z ∈ PDE.translateSet z U :=
      ⟨y, hy, rfl⟩
    simpa only [add_sub_add_right_eq_sub] using
      hTranslated hxTranslated hyTranslated
  · intro h
    exact h.translateSet z

/-- Scalar multiplication scales a Euclidean diameter bound by the absolute
value of the scalar. -/
theorem smul {d : ℕ} {U : Set (Vec d)} {D : ℝ}
    (hU : HasEuclideanDiameterLE U D) (r : ℝ) :
    HasEuclideanDiameterLE (r • U) (|r| * D) := by
  intro x hx y hy
  rcases Set.mem_smul_set.mp hx with ⟨x', hx', rfl⟩
  rcases Set.mem_smul_set.mp hy with ⟨y', hy', rfl⟩
  rw [← smul_sub, vecEuclideanNorm_smul]
  exact mul_le_mul_of_nonneg_left (hU hx' hy') (abs_nonneg r)

/-- A nonnegative dilation scales a Euclidean diameter bound by the dilation
factor. -/
theorem smul_of_nonneg {d : ℕ} {U : Set (Vec d)}
    {D r : ℝ} (hU : HasEuclideanDiameterLE U D) (hr : 0 ≤ r) :
    HasEuclideanDiameterLE (r • U) (r * D) := by
  simpa only [abs_of_nonneg hr] using hU.smul r

/-- A positive dilation has a diameter bound by `r * D` exactly when the
original set has diameter bound `D`. -/
theorem smul_iff_of_pos {d : ℕ} {U : Set (Vec d)}
    {D r : ℝ} (hr : 0 < r) :
    HasEuclideanDiameterLE (r • U) (r * D) ↔
      HasEuclideanDiameterLE U D := by
  constructor
  · intro hScaled x hx y hy
    have hxy :=
      hScaled (Set.smul_mem_smul_set hx)
        (Set.smul_mem_smul_set hy)
    rw [← smul_sub, vecEuclideanNorm_smul, abs_of_pos hr] at hxy
    exact (mul_le_mul_iff_right₀ hr).mp hxy
  · intro h
    exact h.smul_of_nonneg hr.le

end HasEuclideanDiameterLE

end PDE
