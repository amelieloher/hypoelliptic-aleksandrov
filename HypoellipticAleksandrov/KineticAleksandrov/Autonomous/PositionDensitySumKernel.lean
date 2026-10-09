module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionDensitySumYoung
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Tactic

/-! # A summable two-index majorant for finite-speed exponential overlap

The source kernel has linear position support and exponential delay decay.
A product of exponential absolute-value sequences majorizes it and makes
its finite l1 norm explicit without introducing any analytic assumption.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open scoped ENNReal

/-- A product exponential majorant on the literal two-index lattice. -/
def positionYoungKernel (d : ℝ) (z : ℤ × ℤ) : ℝ :=
  Real.exp (-d * |(z.1 : ℝ)|) * Real.exp (-d * |(z.2 : ℝ)|)

/-- Finite-speed overlap is majorized by a separable exponential kernel. -/
theorem position_overlap_majorant (c h k : ℝ) (hc : 0 < c) (hh : 0 ≤ h)
    (hk : |k| ≤ 5 * (h + 1)) :
    Real.exp (-c * max (h - 1) 0) ≤
      Real.exp (2 * c) * (Real.exp (-(c / 12) * |h|) * Real.exp (-(c / 12) * |k|)) := by
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [abs_of_nonneg hh]
  have hm := le_max_left (h - 1) 0
  have hm0 := le_max_right (h - 1) 0
  nlinarith only [hc, hh, hk, hm, hm0]

/-- Exponential absolute-value tails on the integer grid are summable. -/
theorem position_exp_abs_summable (d : ℝ) (hd : 0 < d) :
    Summable (fun k : ℤ => Real.exp (-d * |(k : ℝ)|)) := by
  apply summable_int_iff_summable_nat_and_neg.mpr
  constructor
  · have h := (Real.summable_exp_nat_mul_iff).mpr (show -d < 0 by linarith)
    simpa only [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _), mul_comm]
      using h
  · have h := (Real.summable_exp_nat_mul_iff).mpr (show -d < 0 by linarith)
    simpa only [Int.cast_neg, Int.cast_natCast, abs_neg,
      abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _), mul_comm] using h

/-- The two-index majorant has finite real l1 mass. -/
theorem positionYoungKernel_summable (d : ℝ) (hd : 0 < d) :
    Summable (positionYoungKernel d) := by
  exact (position_exp_abs_summable d hd).mul_of_nonneg
    (position_exp_abs_summable d hd) (fun _ => (Real.exp_pos _).le)
    (fun _ => (Real.exp_pos _).le)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
