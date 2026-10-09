module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.Geometry
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! # Explicit positive-time Kolmogorov Gaussian

The covariance is ((2t³/3,t²),(t²,2t)). The sign of the mixed term corresponds to
forward transport with velocity v, hence the adjoint operator -v∂X+∂vv.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- The Gaussian is defined only at strictly positive times. -/
abbrev BellmanPositiveTime := {t : ℝ // 0 < t}

/-- The exponent of the diffusivity-one joint position-velocity kernel. -/
def bellmanGaussianExponent (t : BellmanPositiveTime) (q : ℝ × ℝ) : ℝ :=
  -3 * q.1 ^ 2 / t.val ^ 3 + 3 * q.1 * q.2 / t.val ^ 2 - q.2 ^ 2 / t.val

/-- The covariance-normalized diffusivity-one Kolmogorov kernel. -/
def bellmanGaussianKernel (t : BellmanPositiveTime) (q : ℝ × ℝ) : ℝ :=
  Real.sqrt 3 / (2 * Real.pi * t.val ^ 2) * Real.exp (bellmanGaussianExponent t q)

/-- Completion of the square identifies the Gaussian decay. -/
theorem bellmanGaussianExponent_eq (t : BellmanPositiveTime) (q : ℝ × ℝ) :
    bellmanGaussianExponent t q =
      -3 / t.val ^ 3 * (q.1 - t.val * q.2 / 2) ^ 2 - q.2 ^ 2 / (4 * t.val) := by
  dsimp [bellmanGaussianExponent]
  field_simp [ne_of_gt t.property]
  ring

/-- The exponent is nonpositive. -/
theorem bellmanGaussianExponent_nonpos (t : BellmanPositiveTime) (q : ℝ × ℝ) :
    bellmanGaussianExponent t q ≤ 0 := by
  rw [bellmanGaussianExponent_eq]
  have h₁ : 0 ≤ 3 / t.val ^ 3 :=
    div_nonneg (by norm_num) (pow_nonneg t.property.le 3)
  have h₂ : 0 ≤ q.2 ^ 2 / (4 * t.val) :=
    div_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) t.property.le)
  rw [neg_div, neg_mul]
  exact sub_nonpos.mpr ((neg_nonpos.mpr
    (mul_nonneg h₁ (sq_nonneg _))).trans h₂)

/-- The kernel is strictly positive. -/
theorem bellmanGaussianKernel_pos (t : BellmanPositiveTime) (q : ℝ × ℝ) :
    0 < bellmanGaussianKernel t q := by
  unfold bellmanGaussianKernel
  exact mul_pos (div_pos (Real.sqrt_pos.2 (by norm_num))
    (mul_pos (mul_pos (by norm_num) Real.pi_pos) (pow_pos t.property 2)))
    (Real.exp_pos _)

/-- The kernel is bounded by its Gaussian prefactor. -/
theorem bellmanGaussianKernel_le (t : BellmanPositiveTime) (q : ℝ × ℝ) :
    bellmanGaussianKernel t q ≤ Real.sqrt 3 / (2 * Real.pi * t.val ^ 2) := by
  unfold bellmanGaussianKernel
  have hc : 0 ≤ Real.sqrt 3 / (2 * Real.pi * t.val ^ 2) := by positivity
  calc
    _ ≤ Real.sqrt 3 / (2 * Real.pi * t.val ^ 2) * 1 :=
      mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr
        (bellmanGaussianExponent_nonpos t q)) hc
    _ = _ := mul_one _

/-- Parabolic rescaling of positive time. -/
def bellmanScaledTime (r : ℝ) (hr : 0 < r) (t : BellmanPositiveTime) :
    BellmanPositiveTime := ⟨r ^ 2 * t.val, mul_pos (pow_pos hr 2) t.property⟩

/-- The exponent is invariant under the joint time and kinetic dilation. -/
theorem bellmanGaussianExponent_scaling (r : ℝ) (hr : 0 < r)
    (t : BellmanPositiveTime) (q : ℝ × ℝ) :
    bellmanGaussianExponent (bellmanScaledTime r hr t) (bellmanPlaneDilation r q) =
      bellmanGaussianExponent t q := by
  dsimp [bellmanGaussianExponent, bellmanScaledTime, bellmanPlaneDilation]
  field_simp [ne_of_gt t.property, ne_of_gt hr]

/-- The explicit kernel scales with the position-velocity homogeneous dimension four. -/
theorem bellmanGaussianKernel_scaling (r : ℝ) (hr : 0 < r)
    (t : BellmanPositiveTime) (q : ℝ × ℝ) :
    bellmanGaussianKernel (bellmanScaledTime r hr t) (bellmanPlaneDilation r q) =
      r⁻¹ ^ 4 * bellmanGaussianKernel t q := by
  simp only [bellmanGaussianKernel, bellmanGaussianExponent_scaling]
  dsimp [bellmanScaledTime]
  field_simp [ne_of_gt t.property, ne_of_gt hr]

end HypoellipticAleksandrov.KineticAleksandrov
