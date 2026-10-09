module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Absorption of the larger supremum in the return estimate

A two-case argument gives the same bound as Young's inequality.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous

/-- A nonlinear height comparison implies a linear absorption bound. -/
theorem return_height_absorption (beta gamma c eps d Ma Mb U : ℝ)
    (hgamma : 0 < gamma) (hc : 0 < c) (heps : 0 < eps) (hd : 0 < d)
    (hMa : 0 ≤ Ma) (hMb : Ma ≤ Mb) (hU : 0 ≤ U)
    (hheight : 0 < Mb → c * d ^ beta * Ma ^ (1 + gamma) * Mb ^ (-gamma) ≤ U) :
    Ma ≤ eps * Mb + (c * eps ^ gamma)⁻¹ * d ^ (-beta) * U := by
  have hMb0 : 0 ≤ Mb := hMa.trans hMb
  have herr0 : 0 ≤ (c * eps ^ gamma)⁻¹ * d ^ (-beta) * U := by positivity
  by_cases hsmall : Ma ≤ eps * Mb
  · exact hsmall.trans (le_add_of_nonneg_right herr0)
  have hlarge : eps * Mb < Ma := lt_of_not_ge hsmall
  have hMapos : 0 < Ma := (mul_nonneg heps.le hMb0).trans_lt hlarge
  have hMbpos : 0 < Mb := hMapos.trans_le hMb
  have hpow := Real.rpow_le_rpow (mul_nonneg hMb0 heps.le)
    (by nlinarith : Mb * eps ≤ Ma) hgamma.le
  rw [Real.mul_rpow hMb0 heps.le] at hpow
  have hinv : Mb ^ gamma * Mb ^ (-gamma) = 1 := by
    rw [← Real.rpow_add hMbpos, add_neg_cancel, Real.rpow_zero]
  have hmul := mul_le_mul_of_nonneg_right hpow
    (mul_nonneg hMa (Real.rpow_nonneg hMb0 (-gamma)))
  have hlower : eps ^ gamma * Ma ≤ Ma ^ (1 + gamma) * Mb ^ (-gamma) := by
    rw [Real.rpow_add hMapos, Real.rpow_one]
    calc
      _ = (eps ^ gamma * Ma) * (Mb ^ gamma * Mb ^ (-gamma)) := by rw [hinv, mul_one]
      _ = (Mb ^ gamma * eps ^ gamma) * (Ma * Mb ^ (-gamma)) := by ring
      _ ≤ _ := hmul
      _ = _ := by ring
  have hineq := (mul_le_mul_of_nonneg_left hlower
    (mul_nonneg hc.le (Real.rpow_nonneg hd.le beta))).trans
    (by simpa only [mul_assoc] using hheight hMbpos)
  have hden : 0 < c * d ^ beta * eps ^ gamma := by positivity
  have hbound : Ma ≤ U / (c * d ^ beta * eps ^ gamma) := by
    apply (le_div_iff₀ hden).mpr
    nlinarith [hineq]
  have he : U / (c * d ^ beta * eps ^ gamma) =
      (c * eps ^ gamma)⁻¹ * d ^ (-beta) * U := by
    rw [Real.rpow_neg hd.le]
    field_simp
  rw [he] at hbound
  exact hbound.trans (le_add_of_nonneg_left (mul_nonneg heps.le hMb0))

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
