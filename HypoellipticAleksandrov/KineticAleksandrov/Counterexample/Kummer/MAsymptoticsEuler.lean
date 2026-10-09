module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.MAsymptoticsCoefficients
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.MAsymptoticsLaplace
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Euler-integral estimates for the negative-axis expansion

The near-endpoint Taylor error and the far-endpoint exponential tail are estimated separately.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

open MeasureTheory Set Filter Asymptotics

/-- The negative-axis Euler kernel. -/
def eulerLaplace (a c X t : ℝ) : ℝ := betaWeight a c t * Real.exp (-(X * t))

/-- Integrability of the Euler kernel for positive endpoint parameters. -/
theorem intervalIntegrable_eulerLaplace (a c X : ℝ) (ha : 0 < a) (hc : 0 < c) :
    IntervalIntegrable (eulerLaplace a c X) volume 0 1 := by
  exact (intervalIntegrable_betaWeight a c ha hc).mul_continuousOn
    (by fun_prop : Continuous (fun t : ℝ => Real.exp (-(X * t)))).continuousOn

/-- Integrability of a Gamma moment on the first half interval. -/
theorem intervalIntegrable_laplaceMoment (a X : ℝ) (ha : 0 < a) (hX : 0 < X) :
    IntervalIntegrable (laplaceMoment a X) volume 0 (1 / 2) := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
  exact (integrable_laplaceMoment a X ha hX).mono_set Ioc_subset_Ioi_self

/-- The first half Gamma moment differs from its full value by an exponentially small tail. -/
theorem laplaceMoment_half_isBigO (a r : ℝ) (ha : 0 < a) :
    IsBigO atTop
      (fun X => (∫ t in (0 : ℝ)..(1 / 2), laplaceMoment a X t) -
        X ^ (-a) * Real.Gamma a) (fun X => X ^ r) := by
  apply (laplaceMoment_tail_isBigO a r ha).neg_left.congr'
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    have he := intervalIntegral.integral_Ioi_sub_Ioi
      (integrable_laplaceMoment a X ha hX) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [integral_laplaceMoment a X ha hX] at he
    linarith only [he]
  · exact Filter.Eventually.of_forall (fun _ => rfl)

/-- The far endpoint of the Euler integral has an exponential bound. -/
theorem eulerLaplace_tail_bound (a c X : ℝ) (ha : 0 < a) (hc : 0 < c)
    (hX : 0 ≤ X) :
    |∫ t in (1 / 2 : ℝ)..1, eulerLaplace a c X t| ≤
      Real.exp (-(X / 2)) * (∫ t in (0 : ℝ)..1, betaWeight a c t) := by
  have hb := intervalIntegrable_betaWeight a c ha hc
  have he := intervalIntegrable_eulerLaplace a c X ha hc
  have hsub : Set.uIcc (1 / 2 : ℝ) 1 ⊆ Set.uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le (by norm_num), uIcc_of_le (by norm_num)]
    intro t ht
    exact ⟨by linarith only [ht.1], ht.2⟩
  have hn : 0 ≤ ∫ t in (1 / 2 : ℝ)..1, eulerLaplace a c X t := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro t ht
    exact mul_nonneg (betaWeight_nonneg a c t ⟨by linarith only [ht.1], ht.2⟩)
      (Real.exp_pos _).le
  rw [abs_of_nonneg hn]
  calc
    _ ≤ ∫ t in (1 / 2 : ℝ)..1, Real.exp (-(X / 2)) * betaWeight a c t := by
      apply intervalIntegral.integral_mono_on (by norm_num) (he.mono_set hsub)
        ((hb.mono_set hsub).const_mul _)
      intro t ht
      rw [eulerLaplace, mul_comm]
      apply mul_le_mul_of_nonneg_right _
        (betaWeight_nonneg a c t ⟨by linarith only [ht.1], ht.2⟩)
      apply Real.exp_le_exp.mpr
      nlinarith only [mul_nonneg hX (sub_nonneg.mpr ht.1)]
    _ = Real.exp (-(X / 2)) * ∫ t in (1 / 2 : ℝ)..1, betaWeight a c t :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ Real.exp (-(X / 2)) * ∫ t in (0 : ℝ)..1, betaWeight a c t := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      rw [intervalIntegral.integral_of_le (by norm_num),
        intervalIntegral.integral_of_le (by norm_num)]
      apply setIntegral_mono_set hb.1
        (ae_restrict_of_forall_mem measurableSet_Ioc
          (fun t ht => betaWeight_nonneg a c t ⟨ht.1.le, ht.2⟩))
      exact Filter.Eventually.of_forall (fun t ht => ⟨by linarith only [ht.1], ht.2⟩)

/-- The far endpoint is smaller than every prescribed algebraic order. -/
theorem eulerLaplace_tail_isBigO (a c r : ℝ) (ha : 0 < a) (hc : 0 < c) :
    IsBigO atTop (fun X => ∫ t in (1 / 2 : ℝ)..1, eulerLaplace a c X t)
      (fun X => X ^ r) := by
  have he : IsBigO atTop (fun X : ℝ => Real.exp (-(X / 2))) (fun X => X ^ r) := by
    simpa only [neg_div, div_eq_mul_inv, mul_comm, one_mul, mul_neg] using
      (isLittleO_exp_neg_mul_rpow_atTop (a := 1 / 2) (by norm_num) r).isBigO
  apply IsBigO.trans ?_ he
  refine IsBigO.of_bound (∫ t in (0 : ℝ)..1, betaWeight a c t) ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with X hX
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_comm] using
    eulerLaplace_tail_bound a c X ha hc hX

/-- The Euler Taylor polynomial multiplied by the Gamma kernel. -/
def polynomialLaplace (a c : ℝ) (N : ℕ) (X t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, poch (1 - c) n / (n.factorial : ℝ) *
    laplaceMoment (a + n) X t

/-- Multiplying a Gamma kernel by a monomial shifts its moment index. -/
theorem laplaceMoment_mul_pow (a X t : ℝ) (ht : 0 < t) (n : ℕ) :
    laplaceMoment a X t * t ^ n = laplaceMoment (a + n) X t := by
  rw [laplaceMoment, laplaceMoment, ← Real.rpow_natCast, mul_right_comm,
    ← Real.rpow_add ht]
  congr 2
  ring

/-- The polynomial Gamma kernel is the Taylor polynomial times the zeroth kernel. -/
theorem polynomialLaplace_eq (a c : ℝ) (N : ℕ) (X t : ℝ) (ht : 0 < t) :
    polynomialLaplace a c N X t = laplaceMoment a X t * betaPolynomial (1 - c) N t := by
  simp only [polynomialLaplace, betaPolynomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [← laplaceMoment_mul_pow a X t ht n]
  ring

/-- Integrability of the polynomial Gamma kernel on the first half interval. -/
theorem intervalIntegrable_polynomialLaplace (a c : ℝ) (N : ℕ) (X : ℝ)
    (ha : 0 < a) (hX : 0 < X) :
    IntervalIntegrable (polynomialLaplace a c N X) volume 0 (1 / 2) := by
  have hs := IntervalIntegrable.sum (Finset.range N) (fun n _ =>
    (intervalIntegrable_laplaceMoment (a + n) X
      (add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg n)) hX).const_mul
      (poch (1 - c) n / (n.factorial : ℝ)))
  convert hs using 1
  ext t
  simp only [polynomialLaplace, Finset.sum_apply]

/-- The Taylor remainder is dominated by the next positive Gamma moment. -/
theorem eulerLaplace_remainder_pointwise (a c : ℝ) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ X t : ℝ, 0 < t → t ≤ 1 / 2 →
      |eulerLaplace a c X t - polynomialLaplace a c N X t| ≤
        C * laplaceMoment (a + N) X t := by
  obtain ⟨C, hC, hb⟩ := betaFactor_remainder_bound (1 - c) N
  refine ⟨C, hC, ?_⟩
  intro X t ht ht1
  have he : eulerLaplace a c X t =
      laplaceMoment a X t * (1 - t) ^ (-(1 - c)) := by
    rw [eulerLaplace, betaWeight, laplaceMoment]
    rw [show -(1 - c) = c - 1 by ring]
    ring
  rw [he, polynomialLaplace_eq a c N X t ht, ← mul_sub, abs_mul,
    abs_of_nonneg (laplaceMoment_nonneg a X t ht.le)]
  calc
    _ ≤ laplaceMoment a X t * (C * t ^ N) :=
      mul_le_mul_of_nonneg_left (hb t ht.le ht1) (laplaceMoment_nonneg a X t ht.le)
    _ = C * laplaceMoment (a + N) X t := by
      rw [← laplaceMoment_mul_pow a X t ht N]
      ring

/-- The first half Taylor error has the required algebraic order. -/
theorem eulerLaplace_near_remainder_isBigO (a c : ℝ) (N : ℕ)
    (ha : 0 < a) (hc : 0 < c) :
    IsBigO atTop
      (fun X => (∫ t in (0 : ℝ)..(1 / 2), eulerLaplace a c X t) -
        ∫ t in (0 : ℝ)..(1 / 2), polynomialLaplace a c N X t)
      (fun X => X ^ (-a - (N : ℝ))) := by
  obtain ⟨C, hC, hb⟩ := eulerLaplace_remainder_pointwise a c N
  have haN : 0 < a + N := add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg N)
  refine IsBigO.of_bound (C * Real.Gamma (a + N)) ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  have he := (intervalIntegrable_eulerLaplace a c X ha hc).mono_set
    (show uIcc (0 : ℝ) (1 / 2) ⊆ uIcc (0 : ℝ) 1 by
      rw [uIcc_of_le (by norm_num), uIcc_of_le (by norm_num)]
      intro t ht
      exact ⟨ht.1, by linarith only [ht.2]⟩)
  have hp := intervalIntegrable_polynomialLaplace a c N X ha hX
  rw [← intervalIntegral.integral_sub he hp]
  calc
    _ ≤ ∫ t in (0 : ℝ)..(1 / 2),
        ‖eulerLaplace a c X t - polynomialLaplace a c N X t‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ ≤ ∫ t in (0 : ℝ)..(1 / 2), C * laplaceMoment (a + N) X t := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num)
        (he.sub hp).norm ((intervalIntegrable_laplaceMoment (a + N) X haN hX).const_mul C)
      intro t ht
      exact hb X t ht.1 ht.2.le
    _ = C * ∫ t in (0 : ℝ)..(1 / 2), laplaceMoment (a + N) X t :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ C * ∫ t in Ioi (0 : ℝ), laplaceMoment (a + N) X t := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      rw [intervalIntegral.integral_of_le (by norm_num)]
      apply setIntegral_mono_set (integrable_laplaceMoment (a + N) X haN hX)
        (ae_restrict_of_forall_mem measurableSet_Ioi
          (fun t ht => laplaceMoment_nonneg (a + N) X t ht.le))
      exact Filter.Eventually.of_forall Ioc_subset_Ioi_self
    _ = C * Real.Gamma (a + N) * ‖X ^ (-a - (N : ℝ))‖ := by
      rw [integral_laplaceMoment (a + N) X haN hX,
        Real.norm_of_nonneg (Real.rpow_nonneg hX.le _)]
      rw [show -(a + (N : ℝ)) = -a - (N : ℝ) by ring]
      ring

/-- Full moments evaluate the polynomial Gamma kernel. -/
def gammaPolynomial (a c : ℝ) (N : ℕ) (X : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, poch (1 - c) n / (n.factorial : ℝ) *
    (X ^ (-(a + n)) * Real.Gamma (a + n))

/-- Replacing all half moments by full moments costs less than every algebraic order. -/
theorem polynomialLaplace_half_isBigO (a c r : ℝ) (N : ℕ) (ha : 0 < a) :
    IsBigO atTop
      (fun X => (∫ t in (0 : ℝ)..(1 / 2), polynomialLaplace a c N X t) -
        gammaPolynomial a c N X) (fun X => X ^ r) := by
  have hs : IsBigO atTop
      (fun X => ∑ n ∈ Finset.range N, poch (1 - c) n / (n.factorial : ℝ) *
        ((∫ t in (0 : ℝ)..(1 / 2), laplaceMoment (a + n) X t) -
          X ^ (-(a + n)) * Real.Gamma (a + n))) (fun X => X ^ r) := by
    have hn (n : ℕ) (_ : n ∈ Finset.range N) :=
      (laplaceMoment_half_isBigO (a + n) r
        (add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg n))).const_mul_left
        (poch (1 - c) n / (n.factorial : ℝ))
    convert IsBigO.sum hn using 1
    ext X
    simp only [Finset.sum_apply]
  apply hs.congr'
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    simp only [polynomialLaplace, gammaPolynomial]
    rw [intervalIntegral.integral_finsetSum]
    · simp only [intervalIntegral.integral_const_mul, mul_sub, Finset.sum_sub_distrib]
    · intro n _
      exact (intervalIntegrable_laplaceMoment (a + n) X
        (add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg n)) hX).const_mul _
  · exact Filter.Eventually.of_forall (fun _ => rfl)

/-- The complete Euler integral has its algebraic moment expansion. -/
theorem eulerLaplace_expansion (a c : ℝ) (N : ℕ) (ha : 0 < a) (hc : 0 < c) :
    IsBigO atTop
      (fun X => (∫ t in (0 : ℝ)..1, eulerLaplace a c X t) - gammaPolynomial a c N X)
      (fun X => X ^ (-a - (N : ℝ))) := by
  have h := ((eulerLaplace_near_remainder_isBigO a c N ha hc).add
    (polynomialLaplace_half_isBigO a c (-a - (N : ℝ)) N ha)).add
    (eulerLaplace_tail_isBigO a c (-a - (N : ℝ)) ha hc)
  apply h.congr_left
  intro X
  have he := intervalIntegrable_eulerLaplace a c X ha hc
  have hs := intervalIntegral.integral_add_adjacent_intervals
    (he.mono_set (by
      rw [uIcc_of_le (by norm_num), uIcc_of_le (by norm_num)]
      intro t ht
      exact ⟨ht.1, by linarith only [ht.2]⟩ : uIcc (0 : ℝ) (1 / 2) ⊆ uIcc 0 1))
    (he.mono_set (by
      rw [uIcc_of_le (by norm_num), uIcc_of_le (by norm_num)]
      intro t ht
      exact ⟨by linarith only [ht.1], ht.2⟩ : uIcc (1 / 2 : ℝ) 1 ⊆ uIcc 0 1))
  linarith only [hs]

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
