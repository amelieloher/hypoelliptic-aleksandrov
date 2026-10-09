module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoxConcentrationSetting
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Tactic

/-! # Source box domination by the singular gauge weight

This measure inequality is unconditional and retains origin mass.
It does not assume or assert a Green identity or occupation estimate.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov MeasureTheory Set
open scoped ENNReal

/-- The source gauge is nonnegative everywhere. -/
theorem rho_nonneg (z : Z) : 0 ≤ rho z :=
  Real.rpow_nonneg (bellmanGaugePower_nonneg z) _

/-- The singular weight is infinite at the origin for a positive exponent. -/
theorem rhoWeight_origin {g : ℝ} (hg : 0 < g) : rhoWeight g (0,0) = ⊤ := by
  have hr : rho (0,0) = 0 := by
    dsimp only [rho]
    norm_num
  rw [rhoWeight, hr, ENNReal.ofReal_zero]
  exact ENNReal.zero_rpow_of_neg (by linarith)

/-- The literal box has the precise homogeneous gauge radius. -/
theorem box_rho_le {A0 r Y : ℝ} (hA0 : 0 < A0) (hr : 0 < r)
    {z : Z} (hz : z ∈ box A0 r Y) :
    rho (z.1-Y,z.2) ≤ (A0^2+A0^6)^(1/6 : ℝ)*r := by
  have hx := pow_le_pow_left₀ (abs_nonneg (z.1-Y)) hz.1 2
  have hv := pow_le_pow_left₀ (abs_nonneg z.2) hz.2 6
  rw [sq_abs] at hx
  rw [pow_abs, abs_of_nonneg (Even.pow_nonneg (by decide : Even 6) z.2)] at hv
  have hs : (z.1-Y)^2+z.2^6 ≤ (A0^2+A0^6)*r^6 := by
    calc
      _ ≤ (A0*r^3)^2+(A0*r)^6 := add_le_add hx hv
      _ = _ := by ring
  have ha : 0 ≤ A0^2+A0^6 := by positivity
  have hb := Real.rpow_le_rpow (bellmanGaugePower_nonneg (z.1-Y,z.2)) hs
    (by norm_num : 0 ≤ (1/6 : ℝ))
  have he : (r^(6 : ℕ))^(1/6 : ℝ) = r := by
    convert Real.pow_rpow_inv_natCast hr.le (by decide : (6 : ℕ) ≠ 0) using 1
    norm_num
  have hm := Real.mul_rpow (z := (1/6 : ℝ)) ha (pow_nonneg hr.le 6)
  rw [he] at hm
  change Real.rpow ((z.1-Y)^2+z.2^6) (1/6) ≤ _
  exact hb.trans_eq hm

/-- On the source box the singular weight dominates its indicator, including the origin. -/
theorem box_indicator_le_weight {A0 r Y g : ℝ} (hA0 : 0 < A0) (hr : 0 < r)
    (hg : 0 ≤ g) (z : Z) :
    (box A0 r Y).indicator (fun _ => (1 : ENNReal)) z ≤
      ENNReal.ofReal (((A0^2+A0^6)^(1/6 : ℝ)*r)^g)*rhoWeight g (z.1-Y,z.2) := by
  by_cases hz : z ∈ box A0 r Y
  · rw [indicator_of_mem hz]
    let D : ℝ := (A0^2+A0^6)^(1/6 : ℝ)*r
    have hD : 0 < D := by dsimp only [D]; positivity
    have hC : 0 < D^g := Real.rpow_pos_of_pos hD _
    have hb : (ENNReal.ofReal (rho (z.1-Y,z.2)))^g ≤ ENNReal.ofReal (D^g) := by
      exact (ENNReal.rpow_le_rpow
        (ENNReal.ofReal_le_ofReal (box_rho_le hA0 hr hz)) hg).trans_eq
          (ENNReal.ofReal_rpow_of_pos hD)
    have hi := ENNReal.inv_le_inv' hb
    rw [← ENNReal.rpow_neg] at hi
    calc
      1 = ENNReal.ofReal (D^g)*(ENNReal.ofReal (D^g))⁻¹ :=
        (ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr hC).ne' ENNReal.ofReal_lt_top.ne).symm
      _ ≤ _ := mul_le_mul le_rfl hi bot_le bot_le
  · rw [indicator_of_notMem hz]
    exact bot_le

/-- Every measure's source-box mass is dominated by its extended singular integral. -/
theorem box_measure_le_weight (mu : Measure Z) {A0 r Y g : ℝ}
    (hA0 : 0 < A0) (hr : 0 < r) (hg : 0 ≤ g) :
    mu (box A0 r Y) ≤ ENNReal.ofReal (((A0^2+A0^6)^(1/6 : ℝ)*r)^g)*
      ∫⁻ z, rhoWeight g (z.1-Y,z.2) ∂mu := by
  rw [← lintegral_indicator_one (box_measurable A0 r Y)]
  apply (lintegral_mono (box_indicator_le_weight hA0 hr hg)).trans_eq
  exact lintegral_const_mul' _ _ ENNReal.ofReal_lt_top.ne

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
