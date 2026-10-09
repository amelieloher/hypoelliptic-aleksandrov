module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # The literal error-function heat barrier

The half-line barrier in Lemma 3.8 is defined by its source integral.
For positive time and ellipticity its heat equation and concavity give the supersolution.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open MeasureTheory Set

/-- The source error function, using the oriented integral also for negative arguments. -/
def intervalErf (x : ℝ) : ℝ :=
  (2 / Real.sqrt Real.pi) * ∫ t in 0..x, Real.exp (-t ^ 2)

/-- The half-line heat barrier; derivative statements require positive ellipticity and time. -/
def intervalHeat (lam θ x : ℝ) : ℝ :=
  intervalErf (x / (2 * Real.sqrt (lam * θ)))

/-- The derivative of the literal error-function integral. -/
theorem hasDerivAt_intervalErf (x : ℝ) :
    HasDerivAt intervalErf ((2 / Real.sqrt Real.pi) * Real.exp (-x ^ 2)) x := by
  have hc : Continuous (fun t : ℝ => Real.exp (-t ^ 2)) := by fun_prop
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 x)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_mul _

/-- The error function vanishes at the origin. -/
@[simp] theorem intervalErf_zero : intervalErf 0 = 0 := by
  simp only [intervalErf, intervalIntegral.integral_same, mul_zero]

/-- The error function is smooth, with the source C-infinity order. -/
theorem contDiff_intervalErf : ContDiff ℝ (⊤ : ℕ∞) intervalErf := by
  apply contDiff_infty_iff_deriv.2
  refine ⟨fun x => (hasDerivAt_intervalErf x).differentiableAt, ?_⟩
  have heq : deriv intervalErf =
      fun x => (2 / Real.sqrt Real.pi) * Real.exp (-x ^ 2) := by
    funext x
    exact (hasDerivAt_intervalErf x).deriv
  rw [heq]
  fun_prop

/-- Strict increase of the literal error function. -/
theorem strictMono_intervalErf : StrictMono intervalErf := by
  apply strictMono_of_deriv_pos
  intro x
  rw [(hasDerivAt_intervalErf x).deriv]
  exact mul_pos (div_pos (by norm_num) (Real.sqrt_pos.2 Real.pi_pos)) (Real.exp_pos _)

/-- Nonnegativity of the error function on the nonnegative half-line. -/
theorem intervalErf_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ intervalErf x := by
  simpa only [intervalErf_zero] using strictMono_intervalErf.monotone hx

/-- Every finite nonnegative argument leaves a strictly positive Gaussian tail. -/
theorem intervalErf_lt_one {x : ℝ} (hx : 0 ≤ x) : intervalErf x < 1 := by
  have hi : Integrable (fun t : ℝ => Real.exp (-t ^ 2)) := by
    simpa only [neg_mul, one_mul] using integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1)
  have : NeZero (volume.restrict (Ioi x) : Measure ℝ) := ⟨by
    intro h
    have he := congrArg (fun ν : Measure ℝ => ν univ) h
    simp at he⟩
  have htail : 0 < ∫ t in Ioi x, Real.exp (-t ^ 2) :=
    integral_exp_pos hi.integrableOn
  have hsplit := intervalIntegral.integral_Ioi_sub_Ioi
    (hi.integrableOn (s := Ioi (0 : ℝ))) hx
  have hfull : (∫ t in Ioi (0 : ℝ), Real.exp (-t ^ 2)) = Real.sqrt Real.pi / 2 := by
    simpa only [neg_mul, one_mul, div_one] using integral_gaussian_Ioi 1
  rw [hfull] at hsplit
  have hlt : (∫ t in (0:ℝ)..x, Real.exp (-t ^ 2)) < Real.sqrt Real.pi / 2 := by
    linarith only [hsplit, htail]
  have hk : 0 < 2 / Real.sqrt Real.pi := div_pos (by norm_num)
    (Real.sqrt_pos.2 Real.pi_pos)
  have hbound := mul_lt_mul_of_pos_left hlt hk
  have hnorm : (2 / Real.sqrt Real.pi) * (Real.sqrt Real.pi / 2) = 1 := by
    field_simp
  simpa only [intervalErf, hnorm] using hbound

/-- At positive ellipticity the source's length-squared block has strict loss. -/
theorem intervalErf_killing_block_lt_one {lam : ℝ} (hlam : 0 < lam) :
    intervalErf (1 / (4 * Real.sqrt lam)) < 1 :=
  intervalErf_lt_one (by positivity)

/-- Gaussian normalization gives the error-function limit at positive infinity. -/
theorem tendsto_intervalErf_atTop :
    Filter.Tendsto intervalErf Filter.atTop (nhds (1 : ℝ)) := by
  have hi : Integrable (fun t : ℝ => Real.exp (-t ^ 2)) := by
    simpa only [neg_mul, one_mul] using integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1)
  have ht := (intervalIntegral_tendsto_integral_Ioi 0 hi.integrableOn
    Filter.tendsto_id).const_mul (2 / Real.sqrt Real.pi)
  have hfull : (∫ t in Ioi (0 : ℝ), Real.exp (-t ^ 2)) = Real.sqrt Real.pi / 2 := by
    simpa only [neg_mul, one_mul, div_one] using integral_gaussian_Ioi 1
  rw [hfull] at ht
  have hnorm : (2 / Real.sqrt Real.pi) * (Real.sqrt Real.pi / 2) = 1 := by
    field_simp
  rw [hnorm] at ht
  exact ht

/-- Spatial derivative of the heat barrier. -/
theorem hasDerivAt_intervalHeat_space (lam θ : ℝ)
    (x : ℝ) :
    HasDerivAt (intervalHeat lam θ)
      ((2 / Real.sqrt Real.pi) * Real.exp (-(x / (2 * Real.sqrt (lam * θ))) ^ 2) /
        (2 * Real.sqrt (lam * θ))) x := by
  unfold intervalHeat
  simpa only [Function.comp_def, id_eq, mul_one_div] using
    (hasDerivAt_intervalErf (x / (2 * Real.sqrt (lam * θ)))).comp x
      ((hasDerivAt_id x).div_const (2 * Real.sqrt (lam * θ)))

/-- Spatial derivative written as an equality of functions. -/
theorem deriv_intervalHeat_space (lam θ : ℝ) :
    deriv (intervalHeat lam θ) = fun x =>
      (2 / Real.sqrt Real.pi) * Real.exp (-(x / (2 * Real.sqrt (lam * θ))) ^ 2) /
        (2 * Real.sqrt (lam * θ)) := by
  funext x
  exact (hasDerivAt_intervalHeat_space lam θ x).deriv

/-- Second spatial derivative of the barrier. -/
theorem deriv2_intervalHeat_space {lam θ : ℝ} (hlam : 0 < lam) (hθ : 0 < θ)
    (x : ℝ) :
    deriv (deriv (intervalHeat lam θ)) x =
      -(2 * x * (2 / Real.sqrt Real.pi) *
        Real.exp (-(x / (2 * Real.sqrt (lam * θ))) ^ 2)) /
        (2 * Real.sqrt (lam * θ)) ^ 3 := by
  rw [deriv_intervalHeat_space lam θ]
  have h := ((((hasDerivAt_id x).div_const (2 * Real.sqrt (lam * θ))).pow 2).neg.exp
    |>.const_mul (2 / Real.sqrt Real.pi)).div_const (2 * Real.sqrt (lam * θ))
  dsimp only [id_eq, Pi.neg_apply, Pi.pow_apply] at h
  rw [h.deriv]
  simp only [Nat.reduceSub, pow_one]
  field_simp [(Real.sqrt_pos.2 (mul_pos hlam hθ)).ne']
  ring

/-- Time derivative of the barrier. -/
theorem hasDerivAt_intervalHeat_time {lam θ : ℝ} (hlam : 0 < lam) (hθ : 0 < θ)
    (x : ℝ) :
    HasDerivAt (fun t => intervalHeat lam t x)
      (-(2 * x * lam * (2 / Real.sqrt Real.pi) *
        Real.exp (-(x / (2 * Real.sqrt (lam * θ))) ^ 2)) /
        (2 * Real.sqrt (lam * θ)) ^ 3) θ := by
  have hs : Real.sqrt (lam * θ) ≠ 0 := (Real.sqrt_pos.2 (mul_pos hlam hθ)).ne'
  have hd : 2 * Real.sqrt (lam * θ) ≠ 0 := mul_ne_zero (by norm_num) hs
  have hg := (((hasDerivAt_id θ).const_mul lam).sqrt (mul_pos hlam hθ).ne').const_mul 2
  have h := (hasDerivAt_intervalErf (x / (2 * Real.sqrt (lam * θ)))).comp θ
    ((hasDerivAt_const θ x).div hg hd)
  dsimp only [id_eq, Function.comp_def, Pi.div_apply] at h
  convert h using 1
  · rfl
  · field_simp
    ring

/-- The barrier solves the half-line heat equation with diffusivity `lam`. -/
theorem intervalHeat_heatEquation {lam θ : ℝ} (hlam : 0 < lam) (hθ : 0 < θ)
    (x : ℝ) :
    deriv (fun t => intervalHeat lam t x) θ =
      lam * deriv (deriv (intervalHeat lam θ)) x := by
  rw [(hasDerivAt_intervalHeat_time hlam hθ x).deriv,
    deriv2_intervalHeat_space hlam hθ]
  ring

/-- Concavity on the nonnegative half-line. -/
theorem intervalHeat_secondDerivative_nonpos {lam θ x : ℝ}
    (hlam : 0 < lam) (hθ : 0 < θ) (hx : 0 ≤ x) :
    deriv (deriv (intervalHeat lam θ)) x ≤ 0 := by
  rw [deriv2_intervalHeat_space hlam hθ]
  apply div_nonpos_of_nonpos_of_nonneg
  · exact neg_nonpos.2 (by positivity)
  · positivity

/-- The source supersolution inequality for any coefficient at least `lam`. -/
theorem intervalHeat_supersolution {lam θ x A : ℝ}
    (hlam : 0 < lam) (hθ : 0 < θ) (hx : 0 ≤ x) (hA : lam ≤ A) :
    deriv (fun t => intervalHeat lam t x) θ =
        lam * deriv (deriv (intervalHeat lam θ)) x ∧
      deriv (deriv (intervalHeat lam θ)) x ≤ 0 ∧
      0 ≤ deriv (fun t => intervalHeat lam t x) θ -
        A * deriv (deriv (intervalHeat lam θ)) x := by
  have heq := intervalHeat_heatEquation hlam hθ x
  have hneg := intervalHeat_secondDerivative_nonpos hlam hθ hx
  refine ⟨heq, hneg, ?_⟩
  rw [heq, ← sub_mul]
  exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 hA) hneg

end HypoellipticAleksandrov.KineticAleksandrov.Interval
