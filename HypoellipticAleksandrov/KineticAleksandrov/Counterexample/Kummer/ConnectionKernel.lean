module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.BasisM
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
# The renormalized connection kernel

Subtracting the leading fractional Gamma kernel leaves an integrable function. This is
the kernel needed to identify the second coefficient at the singular endpoint.
-/

@[expose] public noncomputable section

open Set MeasureTheory Real

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

/-- A concave translated power differs from one by at most its linear tangent. -/
theorem one_add_rpow_sub_one_le (q s : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hs : 0 ≤ s) :
    (1 + s) ^ q - 1 ≤ q * s := by
  have hd : ∀ u ∈ Icc (0 : ℝ) s,
      HasDerivWithinAt (fun t : ℝ => (1 + t) ^ q)
        (q * (1 + u) ^ (q - 1)) (Icc 0 s) u := by
    intro u hu
    have hu1 : 0 < 1 + u := add_pos_of_pos_of_nonneg zero_lt_one hu.1
    have h := ((hasDerivAt_const u (1 : ℝ)).add (hasDerivAt_id u)).rpow_const
      (p := q) (Or.inl hu1.ne')
    simpa only [zero_add, one_mul, Pi.add_apply, id_eq] using h.hasDerivWithinAt
  have hb : ∀ u ∈ Ico (0 : ℝ) s, ‖q * (1 + u) ^ (q - 1)‖ ≤ q := by
    intro u hu
    have hu1 : 1 ≤ 1 + u := by linarith only [hu.1]
    have hp : (1 + u) ^ (q - 1) ≤ 1 := by
      simpa only [Real.rpow_zero] using
        Real.rpow_le_rpow_of_exponent_le hu1 (sub_nonpos.mpr hq1)
    rw [Real.norm_of_nonneg (mul_nonneg hq (Real.rpow_nonneg (by linarith only [hu.1]) _))]
    exact (mul_le_mul_of_nonneg_left hp hq).trans_eq (mul_one q)
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hd hb s ⟨hs, le_rfl⟩
  simp only [add_zero, Real.one_rpow, sub_zero] at h
  exact (le_abs_self ((1 + s) ^ q - 1)).trans h

/-- The integrable difference used to renormalize the singular connection integral. -/
def connectionKernel (c t : ℝ) : ℝ :=
  t ^ (c - 1) * (1 + t) ^ (1 / 3 - c) - t ^ (-(2 / 3 : ℝ))

/-- The renormalized kernel is nonnegative for the shifted source parameter range. -/
theorem connectionKernel_nonneg (c t : ℝ) (hc : c ≤ 1 / 3) (ht : 0 < t) :
    0 ≤ connectionKernel c t := by
  have hp : t ^ (1 / 3 - c) ≤ (1 + t) ^ (1 / 3 - c) :=
    Real.rpow_le_rpow ht.le (by linarith) (sub_nonneg.mpr hc)
  have h := mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg ht.le (c - 1))
  rw [← Real.rpow_add ht] at h
  rw [show c - 1 + (1 / 3 - c) = -(2 / 3 : ℝ) by ring] at h
  exact sub_nonneg.mpr h

/-- Factorization at infinity isolates a small reciprocal argument. -/
theorem connectionKernel_factor (c t : ℝ) (ht : 0 < t) :
    connectionKernel c t = t ^ (-(2 / 3 : ℝ)) *
      ((1 + t⁻¹) ^ (1 / 3 - c) - 1) := by
  have hbase : 1 + t = t * (1 + t⁻¹) := by field_simp; ring
  rw [connectionKernel, hbase, Real.mul_rpow ht.le (by positivity),
    ← mul_assoc, ← Real.rpow_add ht,
    show c - 1 + (1 / 3 - c) = -(2 / 3 : ℝ) by ring]
  ring

/-- The renormalized kernel has an integrable inverse-power tail. -/
theorem connectionKernel_tail_bound (c t : ℝ) (hc : 0 < c) (hc1 : c < 1 / 3)
    (ht : 0 < t) :
    connectionKernel c t ≤ (1 / 3 - c) * t ^ (-(5 / 3 : ℝ)) := by
  rw [connectionKernel_factor c t ht]
  have hq : 0 ≤ 1 / 3 - c := (sub_pos.mpr hc1).le
  have hq1 : 1 / 3 - c ≤ 1 := by linarith only [hc]
  have h := mul_le_mul_of_nonneg_left
    (one_add_rpow_sub_one_le (1 / 3 - c) t⁻¹ hq hq1 (inv_pos.mpr ht).le)
    (Real.rpow_nonneg ht.le (-(2 / 3 : ℝ)))
  have heq : t ^ (-(2 / 3 : ℝ)) * t⁻¹ = t ^ (-(5 / 3 : ℝ)) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add ht]
    congr 1
    ring
  exact h.trans_eq (by rw [mul_comm (1 / 3 - c), ← mul_assoc, heq]; ring)

/-- Continuity of the subtracted kernel away from the integration endpoint. -/
theorem continuousOn_connectionKernel (c : ℝ) :
    ContinuousOn (connectionKernel c) (Ioi 0) := by
  apply ContinuousOn.sub
  · exact (continuousOn_id.rpow_const (fun _ ht => Or.inl ht.ne')).mul
      ((continuousOn_const.add continuousOn_id).rpow_const
        (fun t ht => Or.inl (ne_of_gt (add_pos zero_lt_one ht))))
  · exact continuousOn_id.rpow_const (fun _ ht => Or.inl ht.ne')

/-- The subtracted kernel is integrable at both endpoints in the source parameter range. -/
theorem integrableOn_connectionKernel (c : ℝ) (hc : 0 < c) (hc1 : c < 1 / 3) :
    IntegrableOn (connectionKernel c) (Ioi 0) volume := by
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1), integrableOn_union]
  constructor
  · have hdom := ((integrableOn_gammaKernel c 1 hc zero_lt_one).mono_set
      (show Ioc (0 : ℝ) 1 ⊆ Ioi 0 from Ioc_subset_Ioi_self))
      |>.const_mul ((2 : ℝ) ^ (1 / 3 - c) * Real.exp 1)
    apply hdom.mono'
    · exact ContinuousOn.aestronglyMeasurable
        ((continuousOn_connectionKernel c).mono Ioc_subset_Ioi_self) measurableSet_Ioc
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [Real.norm_of_nonneg (connectionKernel_nonneg c t hc1.le ht.1)]
      have hq : 0 ≤ 1 / 3 - c := (sub_pos.mpr hc1).le
      have hp : (1 + t) ^ (1 / 3 - c) ≤ (2 : ℝ) ^ (1 / 3 - c) :=
        Real.rpow_le_rpow (by linarith only [ht.1]) (by linarith only [ht.2]) hq
      have hexp : 1 ≤ Real.exp 1 * Real.exp (-t) := by
        rw [← Real.exp_add]
        exact Real.one_le_exp_iff.mpr (by linarith only [ht.2])
      have hpow : 0 ≤ t ^ (c - 1) := Real.rpow_nonneg ht.1.le _
      have htwo : 0 ≤ (2 : ℝ) ^ (1 / 3 - c) := Real.rpow_nonneg (by norm_num) _
      calc
        connectionKernel c t ≤ t ^ (c - 1) * (1 + t) ^ (1 / 3 - c) :=
          sub_le_self _ (Real.rpow_nonneg ht.1.le _)
        _ ≤ t ^ (c - 1) * (2 : ℝ) ^ (1 / 3 - c) :=
          mul_le_mul_of_nonneg_left hp hpow
        _ = (2 : ℝ) ^ (1 / 3 - c) * t ^ (c - 1) := by ring
        _ ≤ ((2 : ℝ) ^ (1 / 3 - c) * t ^ (c - 1)) *
            (Real.exp 1 * Real.exp (-t)) :=
          le_mul_of_one_le_right (mul_nonneg htwo hpow) hexp
        _ = ((2 : ℝ) ^ (1 / 3 - c) * Real.exp 1) *
            (Real.exp (-(1 * t)) * t ^ (c - 1)) := by rw [one_mul]; ring
  · have hdom := (integrableOn_Ioi_rpow_of_lt
      (by norm_num : -(5 / 3 : ℝ) < -1) zero_lt_one).const_mul (1 / 3 - c)
    apply hdom.mono'
    · exact ContinuousOn.aestronglyMeasurable
        ((continuousOn_connectionKernel c).mono (Ioi_subset_Ioi zero_le_one)) measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 := zero_lt_one.trans ht
      rw [Real.norm_of_nonneg (connectionKernel_nonneg c t hc1.le ht0)]
      exact connectionKernel_tail_bound c t hc hc1 ht0

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
