module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic

/-! # Radial integration by parts with the exact homogeneous exponent -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- Radial integration by parts produces the source coefficient β-2. -/
theorem bellmanAngularRadial_integrationByParts (β a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hza : ζ a = 0) (hzb : ζ b = 0) :
    (∫ s in a..b, s ^ (2 - β) * deriv ζ s) =
      (β - 2) * (∫ s in a..b, s ^ (1 - β) * ζ s) := by
  have hp : ∀ s ∈ uIcc a b, 0 < s := by
    intro s hs
    rw [uIcc_of_le hab] at hs
    exact ha.trans_le hs.1
  have hw : ContDiffOn ℝ 1 (fun s : ℝ => s ^ (2 - β)) (uIcc a b) :=
    contDiffOn_id.rpow_const_of_ne fun s hs => (hp s hs).ne'
  have hac := hw.absolutelyContinuousOnInterval
  have hz : AbsolutelyContinuousOnInterval ζ a b :=
    ContDiffOn.absolutelyContinuousOnInterval
      (hζ.of_le (by simp : (1 : WithTop ℕ∞) ≤ (⊤ : ℕ∞))).contDiffOn
  have he := hac.integral_mul_deriv_eq_deriv_mul hz
  rw [hza, hzb, mul_zero, mul_zero, sub_self, zero_sub] at he
  have hd : (∫ s in a..b, deriv (fun z : ℝ => z ^ (2 - β)) s * ζ s) =
      (2 - β) * (∫ s in a..b, s ^ (1 - β) * ζ s) := by
    calc
      _ = ∫ s in a..b, (2 - β) * (s ^ (1 - β) * ζ s) := by
        apply intervalIntegral.integral_congr
        intro s hs
        change deriv (fun z : ℝ => z ^ (2 - β)) s * ζ s =
          (2 - β) * (s ^ (1 - β) * ζ s)
        have hspos := hp s hs
        rw [(Real.hasDerivAt_rpow_const (p := 2 - β) (Or.inl hspos.ne')).deriv]
        have hex : (2 - β) - 1 = 1 - β := by ring
        rw [hex]
        ring
      _ = _ := intervalIntegral.integral_const_mul _ _
  rw [hd] at he
  linear_combination he

end HypoellipticAleksandrov.KineticAleksandrov
