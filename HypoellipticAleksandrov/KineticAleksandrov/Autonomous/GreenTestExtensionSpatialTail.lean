module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GreenTestExtensionTraceApproximation
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.HomogeneousReconstructionUniformBound
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Genuine exponential control of discarded spatial boundary values -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Parabolic
open SectionTwo TheoremA Evolution

/-- The proper spatial weight dominates the exponential of absolute position. -/
theorem reconstructionSpatialWeight_exp_abs_le (x : ℝ) :
    Real.exp |x| ≤ reconstructionSpatialWeight x := by
  unfold reconstructionSpatialWeight
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
    exact le_add_of_nonneg_right (Real.exp_pos _).le
  · rw [abs_of_nonpos (not_le.mp hx).le]
    exact le_add_of_nonneg_left (Real.exp_pos _).le

/-- A scaled proper supersolution dominates its constant amplitude outside a position box. -/
theorem reconstructionSpatialBarrier_tail (H : Interval) (T R C : ℝ) (hC : 0 ≤ C)
    (p : Point) (ht : p.time ≤ T) (hx : R ≤ |p.velocity 0|) :
    C ≤ C * Real.exp (-R) * reconstructionSpatialBarrier (max |H.lo| |H.hi| + 1) T p := by
  have hV : 0 ≤ max |H.lo| |H.hi| + 1 := by positivity
  have ht' : 1 ≤ Real.exp ((max |H.lo| |H.hi| + 1) * (T - p.time)) :=
    Real.one_le_exp_iff.mpr (mul_nonneg hV (sub_nonneg.mpr ht))
  have hx' := (Real.exp_le_exp.mpr hx).trans
    (reconstructionSpatialWeight_exp_abs_le (p.velocity 0))
  have hq : Real.exp R ≤ reconstructionSpatialBarrier (max |H.lo| |H.hi| + 1) T p := by
    unfold reconstructionSpatialBarrier
    exact (by simpa only [one_mul] using
      mul_le_mul ht' hx' (Real.exp_pos R).le (le_trans zero_le_one ht'))
  have hmul := mul_le_mul_of_nonneg_left hq (mul_nonneg hC (Real.exp_pos (-R)).le)
  have he : Real.exp (-R) * Real.exp R = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  simpa only [mul_assoc, he, mul_one] using hmul

/-- Every nonnegative scalar multiple remains an actual classical supersolution. -/
theorem reconstructionSpatialBarrier_scaled_operator {lam Lam : ℝ}
    (A : SmoothAutonomous lam Lam) (H : Interval) (T C : ℝ) (hC : 0 ≤ C)
    (p : Point) (hp : p ∈ evolutionPastOpenCylinder (intervalDomain H) (fun _ => 0) T) :
    transportedForwardOperator (evolutionCoefficient A.a) (identityDrift 1)
      (fun q => C * reconstructionSpatialBarrier (max |H.lo| |H.hi| + 1) T q) p ≤ 0 := by
  rw [← viscousTransportedOperator_zero,
    viscousTransportedOperator_const_mul C (reconstructionSpatialBarrier_regular _ _ p),
    viscousTransportedOperator_zero]
  have hh := reconstructionSpatialBarrier_operator_le A.a H T p hp
  have hw : 0 ≤ reconstructionSpatialWeight (p.velocity 0) :=
    add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  exact mul_nonpos_of_nonneg_of_nonpos hC (hh.trans (neg_nonpos.mpr hw))

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
