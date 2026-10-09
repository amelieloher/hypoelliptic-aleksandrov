module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.SkeletonApproximation
import PDEFoundation.Ambient.HilbertVec
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Tactic

/-! # The exact half-acceleration remainder along a compatible smooth skeleton -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Set MeasureTheory

/-- The tangent-line position error has exactly the source coefficient one half. -/
theorem skeleton_position_remainder_le {d : ℕ} {x v : ℝ → PDE.Vec d} {H : ℝ}
    (hv : Continuous v) (hkin : ∀ t, HasDerivAt x (v t) t)
    (hLip : ∀ s t, PDE.vecEuclideanNorm (v s - v t) ≤ H * |s - t|)
    (s b : ℝ) (hsb : s ≤ b) :
    PDE.vecEuclideanNorm (x s - x b - (s - b) • v b) ≤ H * (b - s) ^ 2 / 2 := by
  have hsk : IsSkeleton x v H s b :=
    ⟨hv.continuousOn, fun t _ => (hkin t).hasDerivWithinAt, fun t _ r _ => hLip t r⟩
  have hpos := hsk.position_eq_integral (show b ∈ Icc s b from ⟨hsb, le_rfl⟩)
  have hint : IntervalIntegrable (fun t => v t - v b) volume s b :=
    (hv.intervalIntegrable s b).sub intervalIntegrable_const
  have hI : (∫ t in s..b, v t - v b) = x b - x s - (b - s) • v b := by
    rw [intervalIntegral.integral_sub (hv.intervalIntegrable s b) intervalIntegrable_const,
      intervalIntegral.integral_const]
    rw [hpos]
    abel_nf
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  have he := e.toContinuousLinearMap.intervalIntegral_comp_comm hint
  change (∫ t in s..b, e (v t - v b)) = e (∫ t in s..b, v t - v b) at he
  have hc := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
    (f := fun t => e (v t - v b)) hsb
  have hc1 : Continuous (fun t => ‖e (v t - v b)‖) :=
    (e.continuous.comp (hv.sub continuous_const)).norm
  have hc2 : Continuous (fun t : ℝ => H * (b - t)) := by fun_prop
  have hm := intervalIntegral.integral_mono_on (μ := volume) hsb (hc1.intervalIntegrable s b)
    (hc2.intervalIntegrable s b) (fun t ht => show ‖e (v t - v b)‖ ≤ H * (b - t) from by
      change ‖(v t - v b).toHilbertVec‖ ≤ H * (b - t)
      rw [← PDE.Vec.vecEuclideanNorm_eq_norm_toHilbertVec]
      have h := hLip t b
      rw [abs_of_nonpos (sub_nonpos.mpr ht.2)] at h
      simpa only [neg_sub] using h)
  have hid : IntervalIntegrable (fun t : ℝ => t) volume s b :=
    continuous_id.intervalIntegrable s b
  have hi : (∫ t in s..b, H * (b - t)) = H * (b - s) ^ 2 / 2 := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub intervalIntegrable_const hid,
      intervalIntegral.integral_const, integral_id]
    simp only [smul_eq_mul]
    ring
  have hb := hc.trans (hm.trans_eq hi)
  rw [he] at hb
  have hneg : x s - x b - (s - b) • v b = -(x b - x s - (b - s) • v b) := by
    ext i
    simp only [Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hneg, PDE.vecEuclideanNorm_neg, ← hI, PDE.Vec.vecEuclideanNorm_eq_norm_toHilbertVec]
  exact hb

end HypoellipticAleksandrov.KineticAleksandrov.Holder
