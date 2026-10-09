module

public import PDEFoundation.Sobolev.Cutoff.Basic
public import PDEFoundation.Sobolev.W1p.Product

/-!
# Multiplication by quantitative smooth cutoffs

This file specializes the existing smooth compact-support product rule to
`QuantitativeSmoothCutoff`. The weak product rule is not reproved: the
constructor delegates directly to
`W1pFunction.mulContDiffHasCompactSupport`.

The resulting value and coordinate-gradient estimates retain the explicit
coefficients `1` and `ENNReal.ofReal K`.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

namespace W1pFunction

variable {d : ℕ}
variable {U inner outer : Set (Vec d)}
variable {p : ℝ≥0∞}
variable {K : ℝ}

/-- A quantitative cutoff belongs to `L∞` on every restricted domain. -/
theorem cutoff_memLpTop
    (η : QuantitativeSmoothCutoff inner outer K) :
    MemLpOn U ∞ η.toFun :=
  (η.smooth.continuous.memLp_of_hasCompactSupport
    η.hasCompactSupport).restrict U

/-- Every coordinate of a quantitative cutoff gradient belongs to `L∞` on
every restricted domain. -/
theorem cutoff_gradient_memLpTop
    (η : QuantitativeSmoothCutoff inner outer K) (i : Fin d) :
    MemLpOn U ∞
      (fun x => classicalGradient η.toFun x i) := by
  have hContinuous :
      Continuous (fun x => classicalGradient η.toFun x i) := by
    simpa only [classicalGradient_apply] using
      (η.smooth.continuous_fderiv (by simp)).clm_apply
        continuous_const
  have hCompact :
      HasCompactSupport
        (fun x => classicalGradient η.toFun x i) := by
    simpa only [classicalGradient_apply] using
      η.hasCompactSupport.fderiv_apply (𝕜 := ℝ) (basisVec i)
  exact
    (hContinuous.memLp_of_hasCompactSupport hCompact).restrict U

/-- The restricted `L∞` seminorm of a quantitative cutoff is at most one. -/
theorem eLpNormOn_cutoff_top_le_one
    (η : QuantitativeSmoothCutoff inner outer K) :
    eLpNormOn U ∞ η.toFun ≤ 1 := by
  rw [eLpNormOn, MeasureTheory.eLpNorm_exponent_top
    η.smooth.continuous.aestronglyMeasurable]
  calc
    MeasureTheory.eLpNormEssSup η.toFun (volumeOn U) ≤
        ENNReal.ofReal 1 := by
      apply MeasureTheory.eLpNormEssSup_le_of_ae_bound
      exact Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (η.nonneg x)]
        exact η.le_one x
    _ = 1 := by
      norm_num

/-- Every coordinate-gradient restricted `L∞` seminorm is bounded by the
explicit Euclidean gradient constant. -/
theorem eLpNormOn_cutoff_gradient_top_le
    (η : QuantitativeSmoothCutoff inner outer K) (i : Fin d) :
    eLpNormOn U ∞
        (fun x => classicalGradient η.toFun x i) ≤
      ENNReal.ofReal K := by
  have hContinuous :
      Continuous (fun x => classicalGradient η.toFun x i) := by
    simpa only [classicalGradient_apply] using
      (η.smooth.continuous_fderiv (by simp)).clm_apply
        continuous_const
  rw [eLpNormOn, MeasureTheory.eLpNorm_exponent_top
    hContinuous.aestronglyMeasurable]
  apply MeasureTheory.eLpNormEssSup_le_of_ae_bound
  exact Filter.Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs] using
      η.abs_classicalGradient_apply_le x i

/-- Multiply a representative-level Sobolev function by a quantitative smooth
cutoff.

The exponent assumption is explicit. Internally it supplies the local
integrability hypothesis needed by the existing smooth compact-support
product rule. -/
noncomputable def mulCutoff
    (u : W1pFunction U p)
    (η : QuantitativeSmoothCutoff inner outer K)
    (hp : 1 ≤ p) :
    W1pFunction U p := by
  letI : Fact (1 ≤ p) := ⟨hp⟩
  exact
    u.mulContDiffHasCompactSupport
      η.smooth η.hasCompactSupport

@[simp]
theorem mulCutoff_toFun
    (u : W1pFunction U p)
    (η : QuantitativeSmoothCutoff inner outer K)
    (hp : 1 ≤ p) :
    (u.mulCutoff η hp).toFun =
      fun x => η.toFun x * u x := by
  let : Fact (1 ≤ p) := ⟨hp⟩
  change
    (u.mulContDiffHasCompactSupport
      η.smooth η.hasCompactSupport).toFun =
        fun x => η.toFun x * u x
  exact
    u.mulContDiffHasCompactSupport_toFun
      η.smooth η.hasCompactSupport

@[simp]
theorem mulCutoff_grad
    (u : W1pFunction U p)
    (η : QuantitativeSmoothCutoff inner outer K)
    (hp : 1 ≤ p) :
    (u.mulCutoff η hp).grad =
      fun x =>
        η.toFun x • u.grad x +
          u x • classicalGradient η.toFun x := by
  let : Fact (1 ≤ p) := ⟨hp⟩
  change
    (u.mulContDiffHasCompactSupport
      η.smooth η.hasCompactSupport).grad =
        fun x =>
          η.toFun x • u.grad x +
            u x • classicalGradient η.toFun x
  exact
    u.mulContDiffHasCompactSupport_grad
      η.smooth η.hasCompactSupport

/-- Multiplication by the square of a cutoff has the expected squared value
representative. -/
@[simp]
theorem mulCutoff_sq_toFun
    (u : W1pFunction U p)
    (η : QuantitativeSmoothCutoff inner outer K)
    (hp : 1 ≤ p) :
    (u.mulCutoff η.sq hp).toFun =
      fun x => η x ^ 2 * u x := by
  rw [mulCutoff_toFun, QuantitativeSmoothCutoff.sq_toFun]

/-- Exact product-rule gradient for multiplication by a squared cutoff. -/
theorem mulCutoff_sq_grad
    (u : W1pFunction U p)
    (η : QuantitativeSmoothCutoff inner outer K)
    (hp : 1 ≤ p) :
    (u.mulCutoff η.sq hp).grad =
      fun x =>
        η x ^ 2 • u.grad x +
          (2 * η x * u x) • classicalGradient η.toFun x := by
  rw [mulCutoff_grad]
  funext x i
  rw [QuantitativeSmoothCutoff.sq_classicalGradient]
  simp only [QuantitativeSmoothCutoff.sq_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

/-- Multiplication by a cutoff has coefficient-one cost on the value
component. -/
theorem eLpNormOn_mulCutoff_toFun_le
    (u : W1pFunction U p)
    (η : QuantitativeSmoothCutoff inner outer K)
    (hp : 1 ≤ p) :
    eLpNormOn U p (u.mulCutoff η hp).toFun ≤
      (1 : ℝ≥0∞) * eLpNormOn U p u.toFun := by
  let : Fact (1 ≤ p) := ⟨hp⟩
  have hηTop : MemLpOn U ∞ η.toFun :=
    cutoff_memLpTop η
  have hDηTop :
      ∀ i : Fin d,
        MemLpOn U ∞
          (fun x => classicalGradient η.toFun x i) :=
    cutoff_gradient_memLpTop η
  have htoFun :
      (u.mulCutoff η hp).toFun =
        (u.mulContDiffMemLpTop
          η.smooth hηTop hDηTop).toFun := by
    rw [mulCutoff_toFun, mulContDiffMemLpTop_toFun]
  rw [htoFun]
  exact
    (u.eLpNormOn_mulContDiffMemLpTop_toFun_le
      η.smooth hηTop hDηTop).trans
        (mul_le_mul_left
          (eLpNormOn_cutoff_top_le_one η)
          (eLpNormOn U p u.toFun))

/-- Coordinate-gradient cost of multiplication by a cutoff. The multiplier
term has coefficient `1`, and the product-rule error has the explicit
coefficient `ENNReal.ofReal K`. -/
theorem eLpNormOn_mulCutoff_grad_coord_le
    (u : W1pFunction U p)
    (η : QuantitativeSmoothCutoff inner outer K)
    (hp : 1 ≤ p) (i : Fin d) :
    eLpNormOn U p
        (fun x => (u.mulCutoff η hp).grad x i) ≤
      (1 : ℝ≥0∞) *
          eLpNormOn U p (fun x => u.grad x i) +
        ENNReal.ofReal K *
          eLpNormOn U p u.toFun := by
  let : Fact (1 ≤ p) := ⟨hp⟩
  have hηTop : MemLpOn U ∞ η.toFun :=
    cutoff_memLpTop η
  have hDηTop :
      ∀ j : Fin d,
        MemLpOn U ∞
          (fun x => classicalGradient η.toFun x j) :=
    cutoff_gradient_memLpTop η
  have hgrad :
      (u.mulCutoff η hp).grad =
        (u.mulContDiffMemLpTop
          η.smooth hηTop hDηTop).grad := by
    rw [mulCutoff_grad, mulContDiffMemLpTop_grad]
  rw [hgrad]
  exact
    (u.eLpNormOn_mulContDiffMemLpTop_grad_coord_le
      η.smooth hηTop hDηTop i).trans
        (add_le_add
          (mul_le_mul_left
            (eLpNormOn_cutoff_top_le_one η)
            (eLpNormOn U p (fun x => u.grad x i)))
          (mul_le_mul_left
            (eLpNormOn_cutoff_gradient_top_le η i)
            (eLpNormOn U p u.toFun)))

/-- Multiplication by a squared cutoff has coefficient-one cost on the value
component. -/
theorem eLpNormOn_mulCutoff_sq_toFun_le
    (u : W1pFunction U p)
    (η : QuantitativeSmoothCutoff inner outer K)
    (hp : 1 ≤ p) :
    eLpNormOn U p (u.mulCutoff η.sq hp).toFun ≤
      (1 : ℝ≥0∞) * eLpNormOn U p u.toFun := by
  exact u.eLpNormOn_mulCutoff_toFun_le η.sq hp

/-- The coordinate-gradient cost of multiplication by a squared cutoff. Its
product-rule error has the exact coefficient `ENNReal.ofReal (2 * K)`. -/
theorem eLpNormOn_mulCutoff_sq_grad_coord_le
    (u : W1pFunction U p)
    (η : QuantitativeSmoothCutoff inner outer K)
    (hp : 1 ≤ p) (i : Fin d) :
    eLpNormOn U p
        (fun x => (u.mulCutoff η.sq hp).grad x i) ≤
      (1 : ℝ≥0∞) *
          eLpNormOn U p (fun x => u.grad x i) +
        ENNReal.ofReal (2 * K) *
          eLpNormOn U p u.toFun := by
  exact u.eLpNormOn_mulCutoff_grad_coord_le η.sq hp i

end W1pFunction

end PDE
