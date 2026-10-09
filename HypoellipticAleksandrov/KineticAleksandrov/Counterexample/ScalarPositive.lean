module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarNegativeJets
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarWronskian
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarProfile
public import Mathlib.Analysis.Calculus.DerivativeTest
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Tactic

/-!
# Scalar minimum principle

The curvature obstruction at a negative interior minimum is ordinary real calculus.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open Filter Set Asymptotics
open scoped Topology ContDiff

/-- A twice differentiable real function has nonnegative curvature at a local minimum. -/
theorem scalar_local_min_curvature (f : ℝ → ℝ) (s : ℝ) (hc : ContinuousAt f s)
    (hmin : IsLocalMin f s) : 0 ≤ deriv (deriv f) s := by
  by_contra hn
  have hneg : deriv (deriv f) s < 0 := lt_of_not_ge hn
  have hmax := isLocalMax_of_deriv_deriv_neg hneg hmin.deriv_eq_zero hc
  have he : f =ᶠ[𝓝 s] fun _ => f s := by
    filter_upwards [hmin, hmax] with t ht ht'
    exact le_antisymm ht' ht
  have hz := he.deriv.deriv_eq
  simp only [deriv_const', deriv_const] at hz
  rw [hz] at hneg
  exact lt_irrefl _ hneg

/-- A negative interior minimum is incompatible with the scalar equation on s<0. -/
theorem Fminus_no_negative_local_min (gamma : ScalarGamma) (Lam s : ℝ) (hs : s < 0)
    (hmin : IsLocalMin (Fminus gamma Lam) s) : 0 ≤ Fminus gamma Lam s := by
  by_contra hn
  have hneg : Fminus gamma Lam s < 0 := lt_of_not_ge hn
  have hdd := scalar_local_min_curvature (Fminus gamma Lam) s
    (contDiff_Fminus gamma Lam).continuous.continuousAt hmin
  have ho := Fminus_ode gamma Lam s
  rw [hmin.deriv_eq_zero, mul_zero, sub_zero] at ho
  have hp : 0 < gamma.1 * s * Fminus gamma Lam s :=
    mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg gamma.2.1 hs) hneg
  linarith only [ho, hdd, hp]

/-- A power remainder of three lower degrees is negligible relative to the leading power. -/
theorem scalar_tail_eventually_pos (f : ℝ → ℝ) (alpha c : ℝ) (hc : 0 < c)
    (hr : IsBigO atTop (fun s => f s - c * Real.rpow s alpha)
      (fun s => Real.rpow s (alpha - 3))) : ∀ᶠ s in atTop, 0 < f s := by
  have hb := Kummer.rpow_mul_isBigO_of_add_eq
    (fun s => f s - c * Real.rpow s alpha) (-alpha) (alpha - 3) (-3)
    (by simpa only [Real.rpow_eq_pow] using hr) (by ring)
  have hpow : Tendsto (fun s : ℝ => Real.rpow s (-3)) atTop (𝓝 0) := by
    simpa only [Real.rpow_eq_pow] using
      tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3)
  have hzero := hb.trans_tendsto hpow
  have ht : Tendsto (fun s => f s / Real.rpow s alpha) atTop (𝓝 c) := by
    have h : Tendsto (fun s => c + s ^ (-alpha) *
        (f s - c * Real.rpow s alpha)) atTop (𝓝 (c + 0)) := tendsto_const_nhds.add hzero
    simp only [add_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    simp only [Real.rpow_eq_pow]
    rw [Real.rpow_neg hs.le]
    have hp := (Real.rpow_pos_of_pos hs alpha).ne'
    field_simp
    ring
  filter_upwards [ht.eventually (Ioi_mem_nhds hc), eventually_gt_atTop (0 : ℝ)] with s hs hs0
  exact (div_pos_iff_of_pos_right (Real.rpow_pos_of_pos hs0 alpha)).mp hs

/-- The selected matching coefficient makes the negative scalar tail eventually positive. -/
theorem Fminus_eventually_pos (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam)
    (hmatch : Pgamma gamma.1 - Qgamma gamma.1 * Real.rpow Lam (-(1 / 3)) =
      Real.rpow Lam (-gamma.1)) : ∀ᶠ s in atBot, 0 < Fminus gamma Lam s := by
  have hb := Fminus_negative_ray_asymptotic_of_M_expansion
    Kummer.M_negative_expansion gamma Lam hLam
  rw [scalar_matching_trace_coefficient gamma Lam hLam hmatch] at hb
  have hp := scalar_tail_eventually_pos (fun s => Fminus gamma Lam (-s)) (3 * gamma.1)
    (Real.rpow (9 * Lam) (-gamma.1))
    (by simpa only [Real.rpow_eq_pow] using
      Real.rpow_pos_of_pos (mul_pos (by norm_num) hLam) (-gamma.1)) hb
  simpa only [neg_neg] using tendsto_neg_atBot_atTop.eventually hp

/-- The actual negative-s solution is nonnegative by the compact minimum principle. -/
theorem Fminus_nonneg (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam)
    (hmatch : Pgamma gamma.1 - Qgamma gamma.1 * Real.rpow Lam (-(1 / 3)) =
      Real.rpow Lam (-gamma.1)) (s : ℝ) (hs : s ≤ 0) : 0 ≤ Fminus gamma Lam s := by
  by_contra hn
  have hneg : Fminus gamma Lam s < 0 := lt_of_not_ge hn
  have hf0 : 0 < Fminus gamma Lam 0 := by
    rw [Fminus_zero]
    exact (gamma_constants_pos gamma.1 gamma.2.1 gamma.2.2).1
  have hs0 : s < 0 := lt_of_le_of_ne hs (by intro he; rw [he] at hneg; linarith only [hf0, hneg])
  obtain ⟨a, ha, has⟩ := ((Fminus_eventually_pos gamma Lam hLam hmatch).and
    (eventually_lt_atBot s)).exists
  have ha0 := has.trans hs0
  obtain ⟨m, hm, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr ha0.le) (contDiff_Fminus gamma Lam).continuous.continuousOn
  have hms : Fminus gamma Lam m ≤ Fminus gamma Lam s := hmin ⟨has.le, hs⟩
  have hmn := lt_of_le_of_lt hms hneg
  have ham : a < m := lt_of_le_of_ne hm.1 (by
    intro he
    rw [← he] at hmn
    linarith only [ha, hmn])
  have hm0 : m < 0 := lt_of_le_of_ne hm.2 (by
    intro he
    rw [he] at hmn
    linarith only [hf0, hmn])
  have hl := hmin.isLocalMin (Icc_mem_nhds ham hm0)
  have hc := Fminus_no_negative_local_min gamma Lam m hm0 hl
  exact not_lt_of_ge hc hmn

/-- A zero negative-s minimum is excluded by the proved nonzero Wronskian. -/
theorem Fminus_pos (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam)
    (hmatch : Pgamma gamma.1 - Qgamma gamma.1 * Real.rpow Lam (-(1 / 3)) =
      Real.rpow Lam (-gamma.1)) (s : ℝ) (hs : s ≤ 0) : 0 < Fminus gamma Lam s := by
  have hn := Fminus_nonneg gamma Lam hLam hmatch s hs
  refine lt_of_le_of_ne hn ?_
  intro hz
  have hz' : Fminus gamma Lam s = 0 := hz.symm
  have hs0 : s < 0 := lt_of_le_of_ne hs (by
    intro he
    rw [he, Fminus_zero] at hz'
    exact (gamma_constants_pos gamma.1 gamma.2.1 gamma.2.2).1.ne' hz')
  have hmin : IsLocalMin (Fminus gamma Lam) s := by
    filter_upwards [Iio_mem_nhds hs0] with t ht
    rw [hz']
    exact Fminus_nonneg gamma Lam hLam hmatch t ht.le
  exact Fminus_no_zero_jet gamma Lam s ⟨hz', hmin.deriv_eq_zero⟩

/-- The whole signed scalar profile is strictly positive for every finite s. -/
theorem F_pos (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam)
    (hmatch : Pgamma gamma.1 - Qgamma gamma.1 * Real.rpow Lam (-(1 / 3)) =
      Real.rpow Lam (-gamma.1)) (s : ℝ) : 0 < F gamma Lam s := by
  unfold F
  split_ifs with hs hs0
  · exact Fplus_pos gamma Lam s hLam hs
  · exact Fminus_pos gamma Lam hLam hmatch s hs0.le
  · exact (gamma_constants_pos gamma.1 gamma.2.1 gamma.2.2).1

/-- The literal reflected scalar H is positive away from the origin. -/
theorem scalarProfile_pos (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam)
    (hmatch : Pgamma gamma.1 - Qgamma gamma.1 * Real.rpow Lam (-(1 / 3)) =
      Real.rpow Lam (-gamma.1)) (q : XV 1) (hq : q ≠ 0) :
    0 < scalarProfile gamma Lam q := by
  unfold scalarProfile scalarAnsatz
  split_ifs with hx hx'
  · exact mul_pos (Real.rpow_pos_of_pos hx _) (F_pos gamma Lam hLam hmatch _)
  · exact mul_pos (Real.rpow_pos_of_pos (neg_pos.mpr hx') _) (F_pos gamma Lam hLam hmatch _)
  · have hx0 : q.1 0 = 0 := le_antisymm (le_of_not_gt hx) (le_of_not_gt hx')
    have hv0 : q.2 0 ≠ 0 := by
      intro hv
      apply hq
      apply Prod.ext
      · funext i
        fin_cases i
        exact hx0
      · funext i
        fin_cases i
        exact hv
    exact mul_pos (Real.rpow_pos_of_pos (mul_pos (by norm_num) hLam) _)
      (Real.rpow_pos_of_pos (abs_pos.mpr hv0) _)

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
