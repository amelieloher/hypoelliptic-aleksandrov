module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureJets
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureMajorant
import Mathlib.Tactic

/-! # Integrable bounds for the time derivative away from the Gaussian pole -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- The scalar time chart of the literal positive-time Gaussian. -/
def bellmanGaussianTimeChart (s : ℝ) (q : ℝ × ℝ) : ℝ :=
  Real.sqrt 3 / (2 * Real.pi * s ^ 2) *
    Real.exp (-3 * q.1 ^ 2 / s ^ 3 + 3 * q.1 * q.2 / s ^ 2 - q.2 ^ 2 / s)

/-- The coefficient of the Gaussian in its time derivative. -/
def bellmanGaussianTimeCoefficient (s : ℝ) (q : ℝ × ℝ) : ℝ :=
  9 * q.1 ^ 2 / s ^ 4 - 6 * q.1 * q.2 / s ^ 3 + q.2 ^ 2 / s ^ 2 - 2 / s

/-- A continuous polynomial bound for the time-derivative coefficient. -/
def bellmanGaussianTimeWeight (q : ℝ × ℝ) : ℝ :=
  9 * q.1 ^ 2 + 6 * |q.1 * q.2| + q.2 ^ 2 + 2

/-- The time chart has the polynomial Gaussian derivative on positive time. -/
theorem hasDerivAt_bellmanGaussianTimeChart (t : BellmanPositiveTime) (q : ℝ × ℝ) :
    HasDerivAt (fun s => bellmanGaussianTimeChart s q)
      (bellmanGaussianTimeCoefficient t.val q * bellmanGaussianKernel t q) t.val := by
  convert hasDerivAt_bellmanGaussianKernel_time t q.1 q.2 using 1
  · rfl
  · rw [(hasDerivAt_bellmanGaussianKernel_position t q.1 q.2).deriv,
      (hasDerivAt_deriv_bellmanGaussianKernel_velocity t q.1 q.2).deriv]
    dsimp [bellmanGaussianTimeCoefficient]
    field_simp [ne_of_gt t.property]
    ring

/-- Sixth-order exponential decay dominates the inverse-power singularity. -/
theorem bellman_exp_neg_le_inv_six (y : ℝ) (hy : 0 < y) :
    Real.exp (-y) ≤ 720 / y ^ 6 := by
  have h := Real.pow_div_factorial_le_exp y hy.le 6
  have hm := mul_le_mul_of_nonneg_right h (Real.exp_pos (-y)).le
  have hexp : Real.exp y * Real.exp (-y) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [hexp] at hm
  norm_num at hm
  apply (le_div_iff₀ (pow_pos hy 6)).mpr
  nlinarith only [hm]

/-- On sets away from the pole, the small-time Gaussian is bounded by a fourth power. -/
theorem bellmanGaussianKernel_le_smallTime_four (t : BellmanPositiveTime)
    (ht : t.val ≤ 1) (q : ℝ × ℝ) (a : ℝ) (ha : 0 < a)
    (hq : a ≤ q.1 ^ 2 + q.2 ^ 2) :
    bellmanGaussianKernel t q ≤
      (360 * 8 ^ 6 * Real.sqrt 3 / (Real.pi * a ^ 6)) * t.val ^ 4 := by
  have htp := t.property
  have hE : bellmanGaussianExponent t q ≤ -a / (8 * t.val) := by
    refine (bellmanGaussianExponent_le_smallTime t ht q).trans ?_
    exact div_le_div_of_nonneg_right (neg_le_neg hq) (by positivity)
  have he : Real.exp (bellmanGaussianExponent t q) ≤
      720 / (a / (8 * t.val)) ^ 6 := by
    refine (Real.exp_le_exp.mpr hE).trans ?_
    rw [neg_div]
    exact bellman_exp_neg_le_inv_six _ (by positivity)
  have hm := mul_le_mul_of_nonneg_left he
    (show 0 ≤ Real.sqrt 3 / (2 * Real.pi * t.val ^ 2) by positivity)
  unfold bellmanGaussianKernel
  refine hm.trans_eq ?_
  field_simp [ne_of_gt t.property]
  ring

/-- The polynomial weight is nonnegative. -/
theorem bellmanGaussianTimeWeight_nonneg (q : ℝ × ℝ) :
    0 ≤ bellmanGaussianTimeWeight q := by
  unfold bellmanGaussianTimeWeight
  positivity

/-- A small-time coefficient bound after multiplication by the fourth time power. -/
theorem bellmanGaussianTimeCoefficient_small (t : BellmanPositiveTime)
    (ht : t.val ≤ 1) (q : ℝ × ℝ) :
    |bellmanGaussianTimeCoefficient t.val q| ≤
      bellmanGaussianTimeWeight q / t.val ^ 4 := by
  have ht2 : t.val ^ 2 ≤ 1 := by nlinarith only [t.property, ht]
  have ht3 : t.val ^ 3 ≤ 1 := by
    calc t.val ^ 3 = t.val ^ 2 * t.val := by ring
         _ ≤ 1 * 1 := mul_le_mul ht2 ht t.property.le (by norm_num)
         _ = 1 := one_mul _
  have he : bellmanGaussianTimeCoefficient t.val q * t.val ^ 4 =
      9 * q.1 ^ 2 - 6 * q.1 * q.2 * t.val + q.2 ^ 2 * t.val ^ 2 - 2 * t.val ^ 3 := by
    dsimp [bellmanGaussianTimeCoefficient]
    field_simp [ne_of_gt t.property]
  apply (le_div_iff₀ (pow_pos t.property 4)).mpr
  rw [← abs_of_pos (pow_pos t.property 4), ← abs_mul, he]
  calc
    |9 * q.1 ^ 2 - 6 * q.1 * q.2 * t.val + q.2 ^ 2 * t.val ^ 2 - 2 * t.val ^ 3|
        ≤ |9 * q.1 ^ 2| + |6 * q.1 * q.2 * t.val| +
          |q.2 ^ 2 * t.val ^ 2| + |2 * t.val ^ 3| := by
            have h1 := abs_sub (9 * q.1 ^ 2) (6 * q.1 * q.2 * t.val)
            have h2 := abs_add_le (9 * q.1 ^ 2 - 6 * q.1 * q.2 * t.val)
              (q.2 ^ 2 * t.val ^ 2)
            have h3 := abs_sub
              (9 * q.1 ^ 2 - 6 * q.1 * q.2 * t.val + q.2 ^ 2 * t.val ^ 2)
              (2 * t.val ^ 3)
            linarith only [h1, h2, h3]
    _ ≤ bellmanGaussianTimeWeight q := by
      simp only [abs_mul, abs_of_nonneg (sq_nonneg q.1),
        abs_of_nonneg (sq_nonneg q.2), abs_of_pos t.property,
        abs_of_nonneg (pow_nonneg t.property.le 2),
        abs_of_nonneg (pow_nonneg t.property.le 3)]
      norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 9),
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6),
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      have hx : |q.1| * |q.2| = |q.1 * q.2| := (abs_mul _ _).symm
      dsimp [bellmanGaussianTimeWeight]
      rw [mul_assoc 6, hx]
      nlinarith only [mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ 6 * |q.1 * q.2|),
        mul_le_mul_of_nonneg_left ht2 (sq_nonneg q.2), ht3]

/-- A large-time coefficient bound by the same polynomial weight. -/
theorem bellmanGaussianTimeCoefficient_large (t : BellmanPositiveTime)
    (ht : 1 ≤ t.val) (q : ℝ × ℝ) :
    |bellmanGaussianTimeCoefficient t.val q| ≤ bellmanGaussianTimeWeight q := by
  have hp (n : ℕ) : 1 ≤ t.val ^ n := one_le_pow₀ ht
  unfold bellmanGaussianTimeCoefficient
  calc
    |9 * q.1 ^ 2 / t.val ^ 4 - 6 * q.1 * q.2 / t.val ^ 3 +
        q.2 ^ 2 / t.val ^ 2 - 2 / t.val|
        ≤ |9 * q.1 ^ 2 / t.val ^ 4| + |6 * q.1 * q.2 / t.val ^ 3| +
          |q.2 ^ 2 / t.val ^ 2| + |2 / t.val| := by
            have h1 := abs_sub (9 * q.1 ^ 2 / t.val ^ 4)
              (6 * q.1 * q.2 / t.val ^ 3)
            have h2 := abs_add_le
              (9 * q.1 ^ 2 / t.val ^ 4 - 6 * q.1 * q.2 / t.val ^ 3)
              (q.2 ^ 2 / t.val ^ 2)
            have h3 := abs_sub
              (9 * q.1 ^ 2 / t.val ^ 4 - 6 * q.1 * q.2 / t.val ^ 3 +
                q.2 ^ 2 / t.val ^ 2) (2 / t.val)
            linarith only [h1, h2, h3]
    _ ≤ bellmanGaussianTimeWeight q := by
      simp only [abs_div, abs_mul, abs_of_nonneg (sq_nonneg q.1),
        abs_of_nonneg (sq_nonneg q.2), abs_of_pos t.property,
        abs_of_nonneg (pow_nonneg t.property.le 2),
        abs_of_nonneg (pow_nonneg t.property.le 3),
        abs_of_nonneg (pow_nonneg t.property.le 4)]
      norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 9),
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6),
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      dsimp [bellmanGaussianTimeWeight]
      rw [mul_assoc 6, ← abs_mul]
      exact add_le_add (add_le_add (add_le_add
        (div_le_self (by positivity) (hp 4))
        (div_le_self (by positivity) (hp 3)))
        (div_le_self (sq_nonneg _) (hp 2))) (div_le_self (by norm_num) ht)

end HypoellipticAleksandrov.KineticAleksandrov
