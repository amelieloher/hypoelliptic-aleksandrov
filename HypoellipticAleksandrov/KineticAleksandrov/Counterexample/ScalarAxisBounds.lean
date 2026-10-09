module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarAxis
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarDerivativeGrowth
import Mathlib.Tactic

/-! # Scaled similarity tails stay bounded at every nonzero position-axis point -/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open Filter Asymptotics Set
open scoped Topology

/-- Exact power cancellation for every real jet degree, including negative degrees. -/
theorem scalar_similarity_power_cancel_general (beta x v : ℝ) (hx : 0 < x) :
    Real.rpow x (beta / 3) * Real.rpow |scalarSimilarity x v| beta = Real.rpow |v| beta := by
  simp only [scalarSimilarity, Real.rpow_eq_pow, abs_div, abs_neg,
    abs_of_pos (Real.rpow_pos_of_pos hx (1 / 3 : ℝ))]
  rw [Real.div_rpow (abs_nonneg _) (Real.rpow_nonneg hx.le _),
    ← Real.rpow_mul hx.le, show (1 / 3 : ℝ) * beta = beta / 3 by ring]
  have hp := (Real.rpow_pos_of_pos hx (beta / 3)).ne'
  field_simp

/-- The signed similarity coordinate tends to the appropriate infinite ray in a joint axis limit. -/
theorem scalarSimilarity_tendsto_axis {ι : Type*} (l : Filter ι) (X V : ι → ℝ)
    (v : ℝ) (hv : v ≠ 0) (hX : Tendsto X l (𝓝 0))
    (hXp : ∀ᶠ i in l, 0 < X i) (hV : Tendsto V l (𝓝 v)) :
    Tendsto (fun i => scalarSimilarity (X i) (V i)) l
      (if v < 0 then atTop else atBot) := by
  have hK : Tendsto (fun i => Real.rpow (X i) (1 / 3)) l (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have h := (Real.continuous_rpow_const (by norm_num : 0 ≤ (1 / 3 : ℝ))).tendsto 0
      simpa only [Real.rpow_eq_pow, Function.comp_def,
        Real.zero_rpow (by norm_num : (1 / 3 : ℝ) ≠ 0)] using h.comp hX
    · filter_upwards [hXp] with i hi
      exact Real.rpow_pos_of_pos hi _
  have hInv := hK.inv_tendsto_nhdsGT_zero
  rcases lt_or_gt_of_ne hv with hv | hv
  · rw [ite_eq_left hv]
    simpa only [scalarSimilarity, div_eq_mul_inv, Pi.inv_apply] using
      hV.neg.pos_mul_atTop (neg_pos.mpr hv) hInv
  · rw [ite_eq_right (not_lt.mpr hv.le)]
    simpa only [scalarSimilarity, div_eq_mul_inv, Pi.inv_apply] using
      hV.neg.neg_mul_atTop (neg_neg_of_pos hv) hInv

/-- Two actual similarity-tail bounds give local boundedness after kinetic rescaling at an axis. -/
theorem scalar_scaled_tail_bounded {ι : Type*} (l : Filter ι) (f : ℝ → ℝ) (beta : ℝ)
    (ht : IsBigO atTop f (fun s => Real.rpow |s| beta))
    (hb : IsBigO atBot f (fun s => Real.rpow |s| beta))
    (X V : ι → ℝ) (v : ℝ) (hv : v ≠ 0) (hX : Tendsto X l (𝓝 0))
    (hXp : ∀ᶠ i in l, 0 < X i) (hV : Tendsto V l (𝓝 v)) :
    IsBigO l (fun i => Real.rpow (X i) (beta / 3) * f (scalarSimilarity (X i) (V i)))
      (fun _ => (1 : ℝ)) := by
  have hS := scalarSimilarity_tendsto_axis l X V v hv hX hXp hV
  have hf : IsBigO l (fun i => f (scalarSimilarity (X i) (V i)))
      (fun i => Real.rpow |scalarSimilarity (X i) (V i)| beta) := by
    by_cases hvn : v < 0
    · rw [ite_eq_left hvn] at hS
      exact ht.comp_tendsto hS
    · rw [ite_eq_right hvn] at hS
      exact hb.comp_tendsto hS
  have hm := (isBigO_refl (fun i => Real.rpow (X i) (beta / 3)) l).mul hf
  have he : (fun i => Real.rpow (X i) (beta / 3) *
      Real.rpow |scalarSimilarity (X i) (V i)| beta) =ᶠ[l] fun i => Real.rpow |V i| beta := by
    filter_upwards [hXp] with i hi
    exact scalar_similarity_power_cancel_general beta (X i) (V i) hi
  have hP : Tendsto (fun i => Real.rpow |V i| beta) l (𝓝 (Real.rpow |v| beta)) := by
    simpa only [Real.rpow_eq_pow, Function.comp_def] using
      (Real.continuousAt_rpow_const |v| beta (Or.inl (abs_ne_zero.mpr hv))).tendsto.comp hV.abs
  exact (hm.congr' EventuallyEq.rfl he).trans (isBigO_const_of_tendsto hP one_ne_zero)

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
