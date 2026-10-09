module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarAxisBounds
import Mathlib.Tactic

/-! # Local boundedness of reflected, kinetically rescaled similarity functions -/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open Filter Asymptotics Set
open scoped Topology

/-- The reflected scalar rescaling, with zero values on the position axis. -/
def scalarRescaled (f : ℝ → ℝ) (beta : ℝ) (q : XV 1) : ℝ :=
  if 0 < q.1 0 then Real.rpow (q.1 0) (beta / 3) * f (scalarSimilarity (q.1 0) (q.2 0))
  else if q.1 0 < 0 then Real.rpow (-q.1 0) (beta / 3) *
    f (scalarSimilarity (-q.1 0) (-q.2 0)) else 0

/-- Off-axis continuity follows from continuity of the similarity function. -/
theorem scalarRescaled_continuousAt_off_axis (f : ℝ → ℝ) (beta : ℝ) (hf : Continuous f)
    (q : XV 1) (hx : q.1 0 ≠ 0) : ContinuousAt (scalarRescaled f beta) q := by
  have hX : Continuous (fun z : XV 1 => z.1 0) := by fun_prop
  have hV : Continuous (fun z : XV 1 => z.2 0) := by fun_prop
  rcases lt_or_gt_of_ne hx with hx | hx
  · have hxp : 0 < -q.1 0 := neg_pos.mpr hx
    have hXn : ContinuousAt (fun z : XV 1 => -z.1 0) q := by fun_prop
    have hP : ContinuousAt (fun z : XV 1 => Real.rpow (-z.1 0) (beta / 3)) q := by
      simpa only [Real.rpow_eq_pow] using
        (Real.continuousAt_rpow_const (-q.1 0) (beta / 3) (Or.inl hxp.ne')).comp'
          (f := fun z : XV 1 => -z.1 0) hXn
    have hK : ContinuousAt (fun z : XV 1 => Real.rpow (-z.1 0) (1 / 3)) q := by
      simpa only [Real.rpow_eq_pow] using
        (Real.continuousAt_rpow_const (-q.1 0) (1 / 3) (Or.inl hxp.ne')).comp'
          (f := fun z : XV 1 => -z.1 0) hXn
    have hk : Real.rpow (-q.1 0) (1 / 3) ≠ 0 := by
      simpa only [Real.rpow_eq_pow] using (Real.rpow_pos_of_pos hxp (1 / 3 : ℝ)).ne'
    have hS : ContinuousAt (fun z : XV 1 => scalarSimilarity (-z.1 0) (-z.2 0)) q := by
      simpa only [scalarSimilarity, neg_neg, Pi.div_def] using (hV.continuousAt (x := q)).div hK hk
    have hh := hP.mul (hf.continuousAt.comp' hS)
    apply hh.congr_of_eventuallyEq
    filter_upwards [hX.continuousAt.preimage_mem_nhds (Iio_mem_nhds hx)] with z hz
    simp only [scalarRescaled, scalarSimilarity, not_lt.mpr (show z.1 0 < 0 from hz).le,
      show z.1 0 < 0 from hz, ↓reduceIte, neg_neg, Pi.mul_def]
  · have hP : ContinuousAt (fun z : XV 1 => Real.rpow (z.1 0) (beta / 3)) q := by
      simpa only [Real.rpow_eq_pow] using
        (Real.continuousAt_rpow_const (q.1 0) (beta / 3) (Or.inl hx.ne')).comp'
          (f := fun z : XV 1 => z.1 0)
          (hX.continuousAt (x := q))
    have hK : ContinuousAt (fun z : XV 1 => Real.rpow (z.1 0) (1 / 3)) q := by
      simpa only [Real.rpow_eq_pow] using
        (Real.continuousAt_rpow_const (q.1 0) (1 / 3) (Or.inl hx.ne')).comp'
          (f := fun z : XV 1 => z.1 0)
          (hX.continuousAt (x := q))
    have hk : Real.rpow (q.1 0) (1 / 3) ≠ 0 := by
      simpa only [Real.rpow_eq_pow] using (Real.rpow_pos_of_pos hx (1 / 3 : ℝ)).ne'
    have hS : ContinuousAt (fun z : XV 1 => scalarSimilarity (z.1 0) (z.2 0)) q := by
      simpa only [scalarSimilarity, Pi.neg_def, Pi.div_def] using
        (hV.continuousAt (x := q)).neg.div hK hk
    have hh := hP.mul (hf.continuousAt.comp' hS)
    apply hh.congr_of_eventuallyEq
    filter_upwards [hX.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hx)] with z hz
    simp only [scalarRescaled, scalarSimilarity, show 0 < z.1 0 from hz, ↓reduceIte, Pi.mul_def]

/-- The reflected rescaling is bounded near nonzero position-axis points. -/
theorem scalarRescaled_isBigO_axis (f : ℝ → ℝ) (beta : ℝ)
    (ht : IsBigO atTop f (fun s => Real.rpow |s| beta))
    (hb : IsBigO atBot f (fun s => Real.rpow |s| beta))
    (q : XV 1) (hx : q.1 0 = 0) (hv : q.2 0 ≠ 0) :
    IsBigO (𝓝 q) (scalarRescaled f beta) (fun _ => (1 : ℝ)) := by
  have hX : Continuous (fun z : XV 1 => z.1 0) := by fun_prop
  have hV : Continuous (fun z : XV 1 => z.2 0) := by fun_prop
  let Sp : Set (XV 1) := {z | 0 < z.1 0}
  let Sn : Set (XV 1) := {z | z.1 0 < 0}
  let Sz : Set (XV 1) := {z | z.1 0 = 0}
  have hUnion : Sp ∪ Sn ∪ Sz = univ := by
    ext z
    simp only [Sp, Sn, Sz, mem_union, mem_ofPred_eq, mem_univ, iff_true]
    rcases lt_trichotomy (z.1 0) 0 with h | h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
    · exact Or.inl (Or.inl h)
  rw [← nhdsWithin_univ q, ← hUnion, nhdsWithin_union, nhdsWithin_union, isBigO_sup,
    isBigO_sup]
  constructor
  · constructor
    · have hh := scalar_scaled_tail_bounded (𝓝[Sp] q) f beta ht hb
        (fun z => z.1 0) (fun z => z.2 0) (q.2 0) hv
        (by simpa only [hx] using
          ((hX.tendsto q).mono_left (nhdsWithin_le_nhds (s := Sp))))
        self_mem_nhdsWithin ((hV.tendsto q).mono_left nhdsWithin_le_nhds)
      apply hh.congr' _ EventuallyEq.rfl
      filter_upwards [self_mem_nhdsWithin] with z hz
      simp only [scalarRescaled, show 0 < z.1 0 from hz, ↓reduceIte]
    · have hh := scalar_scaled_tail_bounded (𝓝[Sn] q) f beta ht hb
        (fun z => -z.1 0) (fun z => -z.2 0) (-q.2 0) (neg_ne_zero.mpr hv)
        (by simpa only [hx, neg_zero] using
          ((hX.tendsto q).neg.mono_left (nhdsWithin_le_nhds (s := Sn))))
        (by filter_upwards [self_mem_nhdsWithin] with z hz; exact neg_pos.mpr hz)
        ((hV.tendsto q).neg.mono_left nhdsWithin_le_nhds)
      apply hh.congr' _ EventuallyEq.rfl
      filter_upwards [self_mem_nhdsWithin] with z hz
      simp only [scalarRescaled, not_lt.mpr (show z.1 0 < 0 from hz).le,
        show z.1 0 < 0 from hz, ↓reduceIte]
  · apply (isBigO_zero (fun _ : XV 1 => (1 : ℝ)) (𝓝[Sz] q)).congr' _ EventuallyEq.rfl
    filter_upwards [self_mem_nhdsWithin] with z hz
    simp only [scalarRescaled, show z.1 0 = 0 from hz, lt_self_iff_false, ↓reduceIte]

/-- The rescaled function is locally bounded away from the origin. -/
theorem scalarRescaled_locally_bounded (f : ℝ → ℝ) (beta : ℝ) (hf : Continuous f)
    (ht : IsBigO atTop f (fun s => Real.rpow |s| beta))
    (hb : IsBigO atBot f (fun s => Real.rpow |s| beta)) (q : XV 1) (hq : q ≠ 0) :
    ∃ M : ℝ, ∀ᶠ z in 𝓝 q, |scalarRescaled f beta z| ≤ M := by
  have hh : IsBigO (𝓝 q) (scalarRescaled f beta) (fun _ => (1 : ℝ)) := by
    by_cases hx : q.1 0 = 0
    · have hv : q.2 0 ≠ 0 := by
        intro hv
        apply hq
        apply Prod.ext <;> funext i
        all_goals have hi : i = 0 := Subsingleton.elim _ _
        all_goals subst i
        · exact hx
        · exact hv
      exact scalarRescaled_isBigO_axis f beta ht hb q hx hv
    · exact isBigO_const_of_tendsto
        (scalarRescaled_continuousAt_off_axis f beta hf q hx).tendsto one_ne_zero
  obtain ⟨M, hM⟩ := hh.bound
  refine ⟨M, ?_⟩
  simpa only [Real.norm_eq_abs, norm_one, mul_one] using hM

/-- Every compact set away from the origin has a uniform rescaled-tail bound. -/
theorem scalarRescaled_compact_bound (f : ℝ → ℝ) (beta : ℝ) (hf : Continuous f)
    (ht : IsBigO atTop f (fun s => Real.rpow |s| beta))
    (hb : IsBigO atBot f (fun s => Real.rpow |s| beta))
    (K : Set (XV 1)) (hK : IsCompact K) (hz : 0 ∉ K) :
    ∃ M : ℝ, ∀ q ∈ K, |scalarRescaled f beta q| ≤ M := by
  classical
  have hKnz (q : K) : (q : XV 1) ≠ 0 := by
    intro hq
    exact hz (hq ▸ q.2)
  choose M hM using fun q : K => scalarRescaled_locally_bounded f beta hf ht hb q (hKnz q)
  let U : ∀ q ∈ K, Set (XV 1) := fun q hq => {z | |scalarRescaled f beta z| ≤ M ⟨q, hq⟩}
  obtain ⟨J, hJ⟩ := hK.elim_nhds_subcover' U (fun q hq => hM ⟨q, hq⟩)
  refine ⟨∑ j ∈ J, |M j|, ?_⟩
  intro q hq
  obtain ⟨p, hp, hqp⟩ := mem_iUnion₂.mp (hJ hq)
  have hh : |scalarRescaled f beta q| ≤ M p := hqp
  exact hh.trans ((le_abs_self (M p)).trans (Finset.single_le_sum
    (fun j _ => abs_nonneg (M j)) hp))

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
