module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.GaussianKernel
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic

/-! # Spatial derivatives of the explicit Kolmogorov Gaussian -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- The exponent's position derivative. -/
theorem hasDerivAt_bellmanGaussianExponent_position (t : BellmanPositiveTime) (X v : ℝ) :
    HasDerivAt (fun x => bellmanGaussianExponent t (x, v))
      (-6 * X / t.val ^ 3 + 3 * v / t.val ^ 2) X := by
  convert ((((hasDerivAt_id X).pow 2).const_mul (-3)).div_const (t.val ^ 3)).add
    ((((hasDerivAt_id X).const_mul 3).mul_const v).div_const (t.val ^ 2)) |>.sub
      (hasDerivAt_const X (v ^ 2 / t.val)) using 1
  · funext x
    rfl
  · dsimp
    ring

/-- The exponent's velocity derivative. -/
theorem hasDerivAt_bellmanGaussianExponent_velocity (t : BellmanPositiveTime) (X v : ℝ) :
    HasDerivAt (fun y => bellmanGaussianExponent t (X, y))
      (3 * X / t.val ^ 2 - 2 * v / t.val) v := by
  convert ((hasDerivAt_const v (-3 * X ^ 2 / t.val ^ 3)).add
    (((hasDerivAt_id v).const_mul (3 * X)).div_const (t.val ^ 2))).sub
      (((hasDerivAt_id v).pow 2).div_const t.val) using 1
  · funext x
    rfl
  · dsimp
    ring

/-- The kernel's position derivative with the explicit transport sign. -/
theorem hasDerivAt_bellmanGaussianKernel_position (t : BellmanPositiveTime) (X v : ℝ) :
    HasDerivAt (fun x => bellmanGaussianKernel t (x, v))
      ((-6 * X / t.val ^ 3 + 3 * v / t.val ^ 2) *
        bellmanGaussianKernel t (X, v)) X := by
  convert (hasDerivAt_bellmanGaussianExponent_position t X v).exp.const_mul
    (Real.sqrt 3 / (2 * Real.pi * t.val ^ 2)) using 1
  all_goals simp only [bellmanGaussianKernel]
  ring

/-- The kernel's velocity derivative. -/
theorem hasDerivAt_bellmanGaussianKernel_velocity (t : BellmanPositiveTime) (X v : ℝ) :
    HasDerivAt (fun y => bellmanGaussianKernel t (X, y))
      ((3 * X / t.val ^ 2 - 2 * v / t.val) * bellmanGaussianKernel t (X, v)) v := by
  convert (hasDerivAt_bellmanGaussianExponent_velocity t X v).exp.const_mul
    (Real.sqrt 3 / (2 * Real.pi * t.val ^ 2)) using 1
  all_goals simp only [bellmanGaussianKernel]
  ring

/-- The pointwise first velocity derivative, as a function identity. -/
theorem deriv_bellmanGaussianKernel_velocity (t : BellmanPositiveTime) (X v : ℝ) :
    deriv (fun y => bellmanGaussianKernel t (X, y)) v =
      (3 * X / t.val ^ 2 - 2 * v / t.val) * bellmanGaussianKernel t (X, v) :=
  (hasDerivAt_bellmanGaussianKernel_velocity t X v).deriv

/-- The kernel's second velocity derivative. -/
theorem hasDerivAt_deriv_bellmanGaussianKernel_velocity (t : BellmanPositiveTime)
    (X v : ℝ) :
    HasDerivAt (fun y => deriv (fun z => bellmanGaussianKernel t (X, z)) y)
      (((3 * X / t.val ^ 2 - 2 * v / t.val) ^ 2 - 2 / t.val) *
        bellmanGaussianKernel t (X, v)) v := by
  have hcoeff : HasDerivAt (fun y : ℝ => 3 * X / t.val ^ 2 - 2 * y / t.val)
      (-2 / t.val) v := by
    convert (hasDerivAt_const v (3 * X / t.val ^ 2)).sub
      (((hasDerivAt_id v).const_mul 2).div_const t.val) using 1
    · funext y
      rfl
    · ring
  simp only [deriv_bellmanGaussianKernel_velocity]
  convert hcoeff.mul (hasDerivAt_bellmanGaussianKernel_velocity t X v) using 1
  ring

/-- The explicit Gaussian is smooth in the spatial variables. -/
theorem contDiff_bellmanGaussianKernel (t : BellmanPositiveTime) :
    ContDiff ℝ (⊤ : ℕ∞) (bellmanGaussianKernel t) := by
  unfold bellmanGaussianKernel bellmanGaussianExponent
  fun_prop

/-- The time derivative of the exponent, computed at a strictly positive time. -/
theorem hasDerivAt_bellmanGaussianExponent_time (t : BellmanPositiveTime) (X v : ℝ) :
    HasDerivAt (fun s : ℝ => -3 * X ^ 2 / s ^ 3 + 3 * X * v / s ^ 2 - v ^ 2 / s)
      (9 * X ^ 2 / t.val ^ 4 - 6 * X * v / t.val ^ 3 + v ^ 2 / t.val ^ 2) t.val := by
  have ht : t.val ≠ 0 := ne_of_gt t.property
  convert (((hasDerivAt_const t.val (-3 * X ^ 2)).div
    ((hasDerivAt_id t.val).pow 3) (pow_ne_zero 3 ht)).add
      ((hasDerivAt_const t.val (3 * X * v)).div
        ((hasDerivAt_id t.val).pow 2) (pow_ne_zero 2 ht))).sub
          ((hasDerivAt_const t.val (v ^ 2)).div (hasDerivAt_id t.val) ht) using 1
  · rfl
  · dsimp
    field_simp
    ring

/-- The positive-time Gaussian solves the forward Kolmogorov equation. -/
theorem hasDerivAt_bellmanGaussianKernel_time (t : BellmanPositiveTime) (X v : ℝ) :
    HasDerivAt (fun s : ℝ => Real.sqrt 3 / (2 * Real.pi * s ^ 2) *
      Real.exp (-3 * X ^ 2 / s ^ 3 + 3 * X * v / s ^ 2 - v ^ 2 / s))
      (-v * deriv (fun x => bellmanGaussianKernel t (x, v)) X +
        deriv (fun y => deriv (fun z => bellmanGaussianKernel t (X, z)) y) v) t.val := by
  have ht : t.val ≠ 0 := ne_of_gt t.property
  have hpref := (hasDerivAt_const t.val (Real.sqrt 3)).div
    (((hasDerivAt_id t.val).pow 2).const_mul (2 * Real.pi))
      (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) (pow_ne_zero 2 ht))
  have h := hpref.mul (hasDerivAt_bellmanGaussianExponent_time t X v).exp
  convert h using 1
  · rfl
  · rw [(hasDerivAt_bellmanGaussianKernel_position t X v).deriv,
      (hasDerivAt_deriv_bellmanGaussianKernel_velocity t X v).deriv]
    simp only [bellmanGaussianKernel, bellmanGaussianExponent]
    dsimp
    field_simp
    ring

end HypoellipticAleksandrov.KineticAleksandrov
