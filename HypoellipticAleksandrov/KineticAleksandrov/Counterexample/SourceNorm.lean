module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ShellSource
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Tactic.Linarith

/-! # The radius-uniform subcritical source norm -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open MeasureTheory Set

/-- The norm of a measurable nonnegative source supported on a finite-volume shell. -/
theorem eLpNorm_le_shell_bound {d : ℕ} (f : XV d → ℝ) (S : Set (XV d))
    (p B : ℝ) (hp : 0 < p) (hB : 0 ≤ B) (hf : AEStronglyMeasurable f volume)
    (hS : MeasurableSet S) (hbound : ∀ q, 0 ≤ f q ∧ f q ≤ B)
    (hsupp : ∀ q, q ∉ S → f q = 0) :
    eLpNorm f (ENNReal.ofReal p) volume ≤ ENNReal.ofReal B * volume S ^ (1 / p) := by
  have hm : ∀ᵐ q ∂volume, ‖f q‖ ≤ ‖S.indicator (fun _ => B) q‖ := by
    filter_upwards [] with q
    by_cases hq : q ∈ S
    · rw [indicator_of_mem hq, Real.norm_eq_abs, abs_of_nonneg (hbound q).1,
        Real.norm_eq_abs, abs_of_nonneg hB]
      exact (hbound q).2
    · rw [hsupp q hq, indicator_of_notMem hq]
  apply (eLpNorm_mono_ae hf hm).trans_eq
  rw [eLpNorm_indicator_const hS.nullMeasurableSet (ENNReal.ofReal_ne_zero_iff.mpr hp)
    ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp.le]
  rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg hB]

/-- The shell norm powers combine to the precise source exponent. -/
theorem source_norm_rpow_identity (d : ℕ) (alpha p V K r : ℝ)
    (hp : 0 < p) (hV : 0 < V) (hK : 0 ≤ K) (hr : 0 < r) :
    ENNReal.ofReal (K * Real.rpow r (alpha - 2)) *
      ENNReal.ofReal (V * r ^ (4 * d)) ^ (1 / p) =
        ENNReal.ofReal (K * Real.rpow V (1 / p) *
          Real.rpow r (alpha - 2 + 4 * (d : ℝ) / p)) := by
  simp only [Real.rpow_eq_pow]
  rw [ENNReal.ofReal_rpow_of_nonneg
    (show 0 ≤ V * r ^ (4 * d) from mul_nonneg hV.le (pow_nonneg hr.le _))
    (div_nonneg zero_le_one hp.le),
    ← ENNReal.ofReal_mul (mul_nonneg hK (Real.rpow_pos_of_pos hr _).le),
    Real.mul_rpow hV.le (pow_nonneg hr.le _), ← Real.rpow_natCast_mul hr.le]
  have he : (4 * d : ℕ) * (1 / p : ℝ) = 4 * (d : ℝ) / p := by
    push_cast
    ring
  rw [he]
  congr 1
  calc
    _ = (K * V ^ (1 / p)) * (r ^ (alpha - 2) * r ^ (4 * (d : ℝ) / p)) := by ring
    _ = _ := by rw [← Real.rpow_add hr]

/-- The literal source formula satisfies the source manuscript's Lp estimate. -/
theorem flat_source_eLpNorm_le_of_profile (d : ℕ) (alpha p : ℝ)
    (ha : 0 < alpha) (ha1 : alpha < 1) (hp : 1 ≤ p)
    (hprofile : CounterProfileStatement d alpha) :
    ∃ C r₀ : ℝ, 0 < C ∧ 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ →
      eLpNorm
        (flatSource (profileMatrix hprofile) (profileFunction hprofile) flatteningPsi alpha r)
        (ENNReal.ofReal p) (volume.restrict {q | profileFunction hprofile q < 1}) ≤
          ENNReal.ofReal (C * Real.rpow r (alpha - 2 + 4 * (d : ℝ) / p)) := by
  obtain ⟨hlam, hlamLam, hc, hC, hAm, hA, hH, hzero, hhom, hcomp,
    _, hgv, _, _, _, hgrad, _⟩ := selectedProfile_spec hprofile
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  obtain ⟨V, hV, hvol⟩ := shell_volume_bound (profileFunction hprofile) alpha
    (profileLowerComparison hprofile) ha hc hH (fun q => (hcomp q).1) hhom
  obtain ⟨K, hK, hbound⟩ := shell_source_bound (profileMatrix hprofile)
    (profileFunction hprofile) (profileVelocityJet hprofile) alpha
    (profileLowerEllipticity hprofile) (profileUpperEllipticity hprofile)
    (profileUpperComparison hprofile) ha ha1 hlam hlamLam hA hC hzero
    (fun q => (hcomp q).2) hgrad
  refine ⟨K * Real.rpow V (1 / p), 1, mul_pos hK (Real.rpow_pos_of_pos hV _),
    zero_lt_one, ?_⟩
  intro r hr _
  have hf := (measurable_flatSourceWithJet (profileMatrix hprofile)
    (profileFunction hprofile) (profileVelocityJet hprofile) alpha r
    hAm hH.measurable hgv).aestronglyMeasurable (μ := volume)
  have hS : MeasurableSet (profileShell (profileFunction hprofile) alpha r) :=
    ((isClosed_le continuous_const hH).inter (isClosed_le hH continuous_const)).measurableSet
  have hn := eLpNorm_le_shell_bound _ (profileShell (profileFunction hprofile) alpha r)
    p (K * Real.rpow r (alpha - 2)) hp0
    (mul_nonneg hK.le (Real.rpow_pos_of_pos hr _).le) hf hS (hbound r hr)
    (fun q hq => flatSourceWithJet_eq_zero_off_shell _ _ _ alpha r hr q hq)
  have hpow := ENNReal.rpow_le_rpow (hvol r hr) (div_nonneg zero_le_one hp0.le)
  have hn' := hn.trans (mul_le_mul_right hpow (ENNReal.ofReal (K * Real.rpow r (alpha - 2))))
  rw [source_norm_rpow_identity d alpha p V K r hp0 hV hK.le hr] at hn'
  apply (eLpNorm_restrict_le _ _ _ _).trans
  rw [eLpNorm_congr_ae (flatSource_ae_eq_jet_of_profile hprofile r)]
  exact hn'

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
