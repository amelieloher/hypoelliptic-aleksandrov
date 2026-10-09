module

public import PDEFoundation.Sobolev.ClassicalGradient
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Topology.Algebra.Support

/-!
# Quantitative smooth cutoff data

This file defines a geometry-independent bundle for a smooth cutoff between
an inner set and an outer set. Its pointwise derivative estimate uses the
explicit Euclidean norm of `PDE.classicalGradient`.

## Main definition

* `PDE.QuantitativeSmoothCutoff`: smooth cutoff data with compact support,
  range and plateau properties, topological support control, and an explicit
  pointwise Euclidean gradient bound.
* `PDE.QuantitativeSmoothCutoff.reindex`: shrink the plateau set and enlarge
  the permitted support set without changing the cutoff or its bound.

## Main results

* `PDE.QuantitativeSmoothCutoff.abs_classicalGradient_apply_le`: each gradient
  coordinate is bounded by the Euclidean gradient constant.
* `PDE.QuantitativeSmoothCutoff.abs_fderiv_apply_basisVec_le`: the equivalent
  coordinate directional-derivative estimate.
-/

@[expose] public section

namespace PDE

/-- A quantitative smooth cutoff between `inner` and `outer`.

The constant `K` bounds the explicit Euclidean norm of the coordinate
gradient pointwise. In particular, the field does not use the operator norm
induced by the ambient product norm. -/
structure QuantitativeSmoothCutoff {d : ℕ}
    (inner outer : Set (Vec d)) (K : ℝ) where
  /-- The cutoff function. -/
  toFun : Vec d → ℝ
  /-- Smoothness to every order. -/
  smooth : ContDiff ℝ (⊤ : ℕ∞) toFun
  /-- The cutoff has compact topological support. -/
  hasCompactSupport : HasCompactSupport toFun
  /-- The topological support lies in the prescribed outer set. -/
  tsupport_subset : tsupport toFun ⊆ outer
  /-- The cutoff is nonnegative. -/
  nonneg : ∀ x, 0 ≤ toFun x
  /-- The cutoff is at most one. -/
  le_one : ∀ x, toFun x ≤ 1
  /-- The cutoff equals one throughout the inner set. -/
  eq_one_on_inner : ∀ x ∈ inner, toFun x = 1
  /-- Pointwise explicit Euclidean gradient bound. -/
  gradient_bound :
    ∀ x, vecEuclideanNorm (classicalGradient toFun x) ≤ K

namespace QuantitativeSmoothCutoff

variable {d : ℕ}
variable {inner outer : Set (Vec d)}
variable {K : ℝ}

instance :
    CoeFun (QuantitativeSmoothCutoff inner outer K)
      (fun _ => Vec d → ℝ) where
  coe η := η.toFun

/-- Restrict the plateau set and enlarge the permitted support set without
changing the cutoff function or its gradient constant. -/
def reindex
    {inner' outer' : Set (Vec d)}
    (η : QuantitativeSmoothCutoff inner outer K)
    (hinner : inner' ⊆ inner) (houter : outer ⊆ outer') :
    QuantitativeSmoothCutoff inner' outer' K where
  toFun := η.toFun
  smooth := η.smooth
  hasCompactSupport := η.hasCompactSupport
  tsupport_subset := η.tsupport_subset.trans houter
  nonneg := η.nonneg
  le_one := η.le_one
  eq_one_on_inner := fun x hx =>
    η.eq_one_on_inner x (hinner hx)
  gradient_bound := η.gradient_bound

@[simp]
theorem reindex_toFun
    {inner' outer' : Set (Vec d)}
    (η : QuantitativeSmoothCutoff inner outer K)
    (hinner : inner' ⊆ inner) (houter : outer ⊆ outer') :
    (η.reindex hinner houter).toFun = η.toFun :=
  rfl

private theorem classicalGradient_sq_toFun
    (η : QuantitativeSmoothCutoff inner outer K) (x : Vec d) :
    classicalGradient (fun y => η.toFun y ^ 2) x =
      (2 * η.toFun x) • classicalGradient η.toFun x := by
  have hηDiff : DifferentiableAt ℝ η.toFun x :=
    η.smooth.contDiffAt.differentiableAt (by simp)
  funext i
  simp only [classicalGradient_apply, Pi.smul_apply, smul_eq_mul]
  have hsquare :
      (fun y => η.toFun y ^ 2) = η.toFun * η.toFun := by
    funext y
    simp only [Pi.mul_apply, pow_two]
  rw [hsquare, fderiv_mul hηDiff hηDiff]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- Square a quantitative cutoff.

The support and plateau sets are unchanged, while the explicit Euclidean
gradient constant becomes `2 * K`.
-/
def sq (η : QuantitativeSmoothCutoff inner outer K) :
    QuantitativeSmoothCutoff inner outer (2 * K) where
  toFun := fun x => η.toFun x ^ 2
  smooth := η.smooth.pow 2
  hasCompactSupport := by
    have hsquare :
        (fun x => η.toFun x ^ 2) = η.toFun * η.toFun := by
      funext x
      simp only [Pi.mul_apply, pow_two]
    rw [hsquare]
    exact η.hasCompactSupport.mul_right (f' := η.toFun)
  tsupport_subset := by
    simpa only [pow_two] using
      (tsupport_mul_subset_left
        (f := η.toFun) (g := η.toFun)).trans η.tsupport_subset
  nonneg := fun x => sq_nonneg (η.toFun x)
  le_one := fun x =>
    (sq_le_one_iff₀ (η.nonneg x)).2 (η.le_one x)
  eq_one_on_inner := by
    intro x hx
    rw [η.eq_one_on_inner x hx]
    norm_num
  gradient_bound := by
    intro x
    rw [classicalGradient_sq_toFun, vecEuclideanNorm_smul]
    have hcoefficient : |2 * η.toFun x| ≤ 2 := by
      rw [abs_of_nonneg (mul_nonneg (by norm_num) (η.nonneg x))]
      exact mul_le_of_le_one_right (by norm_num) (η.le_one x)
    calc
      |2 * η.toFun x| *
            vecEuclideanNorm (classicalGradient η.toFun x) ≤
          2 * vecEuclideanNorm (classicalGradient η.toFun x) :=
        mul_le_mul_of_nonneg_right hcoefficient
          (vecEuclideanNorm_nonneg _)
      _ ≤ 2 * K :=
        mul_le_mul_of_nonneg_left (η.gradient_bound x) (by norm_num)

@[simp]
theorem sq_toFun
    (η : QuantitativeSmoothCutoff inner outer K) :
    η.sq.toFun = fun x => η.toFun x ^ 2 :=
  rfl

@[simp]
theorem sq_apply
    (η : QuantitativeSmoothCutoff inner outer K) (x : Vec d) :
    η.sq x = η x ^ 2 :=
  rfl

/-- The classical gradient of the squared cutoff is exactly
`2 * η * ∇η`. -/
theorem sq_classicalGradient
    (η : QuantitativeSmoothCutoff inner outer K) (x : Vec d) :
    classicalGradient η.sq.toFun x =
      (2 * η x) • classicalGradient η.toFun x :=
  classicalGradient_sq_toFun η x

/-- Every cutoff value belongs to the interval `[0, 1]`. -/
theorem mem_Icc
    (η : QuantitativeSmoothCutoff inner outer K) (x : Vec d) :
    η x ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨η.nonneg x, η.le_one x⟩

/-- The ordinary support is contained in the prescribed outer set. -/
theorem support_subset
    (η : QuantitativeSmoothCutoff inner outer K) :
    Function.support η.toFun ⊆ outer :=
  (subset_tsupport η.toFun).trans η.tsupport_subset

/-- The cutoff vanishes outside the prescribed outer set. -/
theorem eq_zero_of_not_mem_outer
    (η : QuantitativeSmoothCutoff inner outer K)
    {x : Vec d} (hx : x ∉ outer) :
    η x = 0 :=
  image_eq_zero_of_notMem_tsupport
    (fun hxt => hx (η.tsupport_subset hxt))

/-- The classical gradient of a cutoff vanishes outside its prescribed outer
set. -/
theorem classicalGradient_eq_zero_of_not_mem_outer
    (η : QuantitativeSmoothCutoff inner outer K)
    {x : Vec d} (hx : x ∉ outer) :
    classicalGradient η.toFun x = 0 := by
  have hxt : x ∉ tsupport η.toFun :=
    fun hmem => hx (η.tsupport_subset hmem)
  have hfderiv : fderiv ℝ η.toFun x = 0 :=
    fderiv_of_notMem_tsupport ℝ hxt
  funext i
  rw [classicalGradient_apply, hfderiv]
  exact zero_apply _

/-- A quantitative cutoff is stationary at every point of its plateau.

No openness hypothesis on `inner` is needed: a plateau point has value one,
and the global upper bound `η ≤ 1` makes it a local maximum. -/
theorem classicalGradient_eq_zero_of_mem_inner
    (η : QuantitativeSmoothCutoff inner outer K)
    {x : Vec d} (hx : x ∈ inner) :
    classicalGradient η.toFun x = 0 := by
  have hmax : IsMaxOn η.toFun Set.univ x := by
    intro y _
    rw [η.eq_one_on_inner x hx]
    exact η.le_one y
  have hlocal : IsLocalMax η.toFun x :=
    hmax.isLocalMax (by simp)
  have hfderiv : fderiv ℝ η.toFun x = 0 :=
    IsLocalMax.fderiv_eq_zero hlocal
  funext i
  rw [classicalGradient_apply, hfderiv]
  exact zero_apply _

/-- The plateau and support properties force the inner set to lie in the
outer set. -/
theorem inner_subset_outer
    (η : QuantitativeSmoothCutoff inner outer K) :
    inner ⊆ outer := by
  intro x hx
  apply η.support_subset
  change η.toFun x ≠ 0
  rw [η.eq_one_on_inner x hx]
  exact one_ne_zero

/-- Any realized pointwise Euclidean gradient bound is nonnegative. -/
theorem gradient_bound_nonneg
    (η : QuantitativeSmoothCutoff inner outer K) :
    0 ≤ K :=
  (vecEuclideanNorm_nonneg
    (classicalGradient η.toFun (0 : Vec d))).trans
      (η.gradient_bound 0)

/-- Every coordinate of the classical gradient is bounded by `K`. -/
theorem abs_classicalGradient_apply_le
    (η : QuantitativeSmoothCutoff inner outer K)
    (x : Vec d) (i : Fin d) :
    |classicalGradient η.toFun x i| ≤ K :=
  (abs_apply_le_vecEuclideanNorm
    (classicalGradient η.toFun x) i).trans
      (η.gradient_bound x)

/-- Coordinate directional derivatives are bounded by the same explicit
Euclidean gradient constant `K`. -/
theorem abs_fderiv_apply_basisVec_le
    (η : QuantitativeSmoothCutoff inner outer K)
    (x : Vec d) (i : Fin d) :
    |(fderiv ℝ η.toFun x) (basisVec i)| ≤ K := by
  rw [← classicalGradient_apply]
  exact η.abs_classicalGradient_apply_le x i

end QuantitativeSmoothCutoff

end PDE
