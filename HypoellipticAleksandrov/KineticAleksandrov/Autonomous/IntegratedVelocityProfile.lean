module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic

/-! # Smooth convex velocity test

The regularized absolute value has a positive second derivative on the velocity band.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous

/-- Regularized absolute value with squared regularization parameter. -/
def velocityConvexProfile (R v : ℝ) : ℝ := Real.sqrt (R + v ^ 2)

/-- The profile is smooth for a strictly positive regularization parameter. -/
theorem velocityConvexProfile_contDiff {R : ℝ} (hR : 0 < R) :
    ContDiff ℝ (⊤ : ℕ∞) (velocityConvexProfile R) := by
  exact (contDiff_const.add (contDiff_id.pow 2)).sqrt
    (fun v => ne_of_gt (add_pos_of_pos_of_nonneg hR (sq_nonneg v)))

/-- First derivative of the convex profile. -/
theorem velocityConvexProfile_hasDerivAt {R : ℝ} (hR : 0 < R) (v : ℝ) :
    HasDerivAt (velocityConvexProfile R) (v / Real.sqrt (R + v ^ 2)) v := by
  have hd : HasDerivAt (fun w : ℝ => R + w ^ 2) (2 * v) v := by
    have hpow : HasDerivAt (fun w : ℝ => w ^ 2) (2 * v) v := by
      simpa using hasDerivAt_pow 2 v
    exact hpow.const_add R
  have h := hd.sqrt
    (ne_of_gt (add_pos_of_pos_of_nonneg hR (sq_nonneg v)))
  convert h using 1
  · rfl
  · field_simp

/-- The total first derivative agrees with the explicit smooth formula. -/
theorem velocityConvexProfile_deriv {R : ℝ} (hR : 0 < R) :
    deriv (velocityConvexProfile R) = fun v => v / Real.sqrt (R + v ^ 2) := by
  funext v
  exact (velocityConvexProfile_hasDerivAt hR v).deriv

/-- Second derivative of the convex profile. -/
theorem velocityConvexProfile_second_deriv {R : ℝ} (hR : 0 < R) (v : ℝ) :
    deriv (deriv (velocityConvexProfile R)) v =
      R / Real.sqrt (R + v ^ 2) ^ 3 := by
  rw [velocityConvexProfile_deriv hR]
  have hp : 0 < R + v ^ 2 := add_pos_of_pos_of_nonneg hR (sq_nonneg v)
  have hs : Real.sqrt (R + v ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hp)
  have hd := (hasDerivAt_id v).div (velocityConvexProfile_hasDerivAt hR v) hs
  change deriv (id / velocityConvexProfile R) v = _
  rw [hd.deriv]
  dsimp only [velocityConvexProfile, id_eq]
  have hsq := Real.sq_sqrt hp.le
  field_simp
  nlinarith

/-- The second derivative controls the entire velocity band with a uniform constant. -/
theorem velocityConvexProfile_band_lower {r v : ℝ} (hr : 0 < r)
    (hv : |v| ≤ 3 * r) :
    1 / (64 * r) ≤ r ^ 2 / Real.sqrt (r ^ 2 + v ^ 2) ^ 3 := by
  have hp : 0 < r ^ 2 + v ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hr)
    (sq_nonneg v)
  have hs : 0 < Real.sqrt (r ^ 2 + v ^ 2) := Real.sqrt_pos.2 hp
  have hsq := Real.sq_sqrt hp.le
  have hv2 : v ^ 2 ≤ 9 * r ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg v) hv 2
    rw [sq_abs] at h
    nlinarith only [h]
  have hb : Real.sqrt (r ^ 2 + v ^ 2) ≤ 4 * r := by
    nlinarith
  have hc : Real.sqrt (r ^ 2 + v ^ 2) ^ 3 ≤ 64 * r ^ 3 := by
    have := pow_le_pow_left₀ hs.le hb 3
    nlinarith
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith

/-- Increasing the squared regularization by `h` changes the profile by at most `sqrt h`.
This bound is independent of the velocity. -/
theorem velocityConvexProfile_increment {R h : ℝ} (hR : 0 ≤ R) (hh : 0 ≤ h)
    (v : ℝ) :
    0 ≤ velocityConvexProfile (R + h) v - velocityConvexProfile R v ∧
      velocityConvexProfile (R + h) v - velocityConvexProfile R v ≤ Real.sqrt h := by
  have ha : 0 ≤ R + v ^ 2 := add_nonneg hR (sq_nonneg v)
  have hb : 0 ≤ R + h + v ^ 2 := by linarith
  have hs := Real.sqrt_nonneg (R + v ^ 2)
  have ht := Real.sqrt_nonneg (R + h + v ^ 2)
  have hu := Real.sqrt_nonneg h
  have hx := Real.sq_sqrt ha
  have hy := Real.sq_sqrt hb
  have hz := Real.sq_sqrt hh
  have hm : Real.sqrt (R + v ^ 2) ≤ Real.sqrt (R + h + v ^ 2) :=
    Real.sqrt_le_sqrt (by linarith)
  unfold velocityConvexProfile
  constructor
  · linarith
  · nlinarith [mul_nonneg hs hu]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
