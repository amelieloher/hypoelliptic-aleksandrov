module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Tactic

/-! # Interval integrations of the angular density and flux identities -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- The oriented first angular moment from the source. -/
def bellmanAngularFirstMoment (f : ℝ → ℝ) (y : ℝ) : ℝ := ∫ z in 0..y, z * f z

/-- The oriented second angular moment from the source. -/
def bellmanAngularSecondMoment (f : ℝ → ℝ) (y : ℝ) : ℝ := ∫ z in 0..y, z ^ 2 * f z

/-- Local absolute continuity on ordered intervals also applies to oriented intervals. -/
theorem bellman_locallyAC_oriented {g : ℝ → ℝ}
    (hg : ∀ a b : ℝ, a ≤ b → AbsolutelyContinuousOnInterval g a b) (a b : ℝ) :
    AbsolutelyContinuousOnInterval g a b := by
  rcases le_total a b with h | h
  · exact hg a b h
  · exact (hg b a h).symm

/-- Locally integrable angular densities have integrable polynomial moments on every interval. -/
theorem bellmanAngularMoment_intervalIntegrable {f : ℝ → ℝ}
    (hf : LocallyIntegrable f volume) (a b : ℝ) (n : ℕ) :
    IntervalIntegrable (fun z => z ^ n * f z) volume a b := by
  apply (intervalIntegrable_iff').mpr
  exact (hf.integrableOn_isCompact isCompact_uIcc).continuousOn_mul
    (by fun_prop) isCompact_uIcc

/-- Integrating the flux derivative gives its first-moment formula. -/
theorem bellmanAngularFlux_integrated (β : ℝ) (f J : ℝ → ℝ)
    (hJ : ∀ a b : ℝ, a ≤ b → AbsolutelyContinuousOnInterval J a b)
    (hdJ : ∀ᵐ y ∂volume, deriv J y = -(β - 2) / 3 * y * f y) (y : ℝ) :
    J y = J 0 - ((β - 2) / 3) * bellmanAngularFirstMoment f y := by
  have he := (bellman_locallyAC_oriented hJ 0 y).integral_deriv_eq_sub
  have hc : (∫ z in 0..y, deriv J z) =
      -((β - 2) / 3) * bellmanAngularFirstMoment f y := by
    calc
      _ = ∫ z in 0..y, -((β - 2) / 3) * (z * f z) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [hdJ] with z hz
        intro _
        rw [hz]
        ring
      _ = _ := by rw [intervalIntegral.integral_const_mul]; rfl
  rw [hc] at he
  linarith

/-- Two source interval integrations yield the exact angular identity. -/
theorem bellmanAngularDensity_integrated (β : ℝ) (f h J : ℝ → ℝ)
    (hf : LocallyIntegrable f volume)
    (hh : ∀ a b : ℝ, a ≤ b → AbsolutelyContinuousOnInterval h a b)
    (hJ : ∀ a b : ℝ, a ≤ b → AbsolutelyContinuousOnInterval J a b)
    (hdh : ∀ᵐ y ∂volume, deriv h y = J y - y ^ 2 * f y / 3)
    (hdJ : ∀ᵐ y ∂volume, deriv J y = -(β - 2) / 3 * y * f y) :
    ∀ y : ℝ, h y = h 0 + J 0 * y - ((β - 2) / 3) * y *
      bellmanAngularFirstMoment f y + ((β - 3) / 3) * bellmanAngularSecondMoment f y := by
  intro y
  have hJa := bellman_locallyAC_oriented hJ 0 y
  have hha := bellman_locallyAC_oriented hh 0 y
  have hid : AbsolutelyContinuousOnInterval (fun z : ℝ => z) 0 y :=
    (contDiff_id : ContDiff ℝ 1 (fun z : ℝ => z)).contDiffOn.absolutelyContinuousOnInterval
  have hip := hJa.integral_mul_deriv_eq_deriv_mul hid
  simp only [deriv_id'', mul_one, mul_zero, sub_zero] at hip
  have hm : (∫ z in 0..y, deriv J z * z) =
      -((β - 2) / 3) * bellmanAngularSecondMoment f y := by
    calc
      _ = ∫ z in 0..y, -((β - 2) / 3) * (z ^ 2 * f z) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [hdJ] with z hz
        intro _
        rw [hz]
        ring
      _ = _ := by rw [intervalIntegral.integral_const_mul]; rfl
  rw [hm, bellmanAngularFlux_integrated β f J hJ hdJ y] at hip
  have hjInt : IntervalIntegrable J volume 0 y := hJa.continuousOn.intervalIntegrable
  have hmInt := bellmanAngularMoment_intervalIntegrable hf 0 y 2
  have hhe := hha.integral_deriv_eq_sub
  have hhInt : (∫ z in 0..y, deriv h z) =
      (∫ z in 0..y, J z) - bellmanAngularSecondMoment f y / 3 := by
    calc
      _ = ∫ z in 0..y, J z - (z ^ 2 * f z) / 3 := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [hdh] with z hz
        intro _
        exact hz
      _ = _ := by
        rw [intervalIntegral.integral_sub hjInt (hmInt.div_const 3),
          intervalIntegral.integral_div]
        rfl
  rw [hhInt, hip] at hhe
  linear_combination -hhe

end HypoellipticAleksandrov.KineticAleksandrov
