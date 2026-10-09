module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.NearFullCutoffMeasurable
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic

/-! # Quantitative source localization to the strict sublevel set -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Set MeasureTheory
open scoped ENNReal

/-- A bounded localized positive source is controlled by the strict-sublevel volume. -/
theorem localizedSource_norm_le_sublevel_volume {d : ℕ} (A : FullKineticCoefficient d)
    {psi u : KineticPoint d → ℝ} {Q : Set (KineticPoint d)} (hQ : IsOpen Q)
    (hQfinite : volume Q ≠ ⊤) (hpsi : ContinuousOn psi Q) (hu : ContinuousOn u Q)
    (hopm : Measurable (backwardOperator A psi)) (ell B p : ℝ)
    (hB : 0 ≤ B) (hp : 1 ≤ p) (hlevel : ∀ P ∈ Q, psi P ≤ ell)
    (hop : ∀ᵐ P ∂(volume.restrict Q), |backwardOperator A psi P| ≤ B) :
    (eLpNorm (localizedSource A psi u) (ENNReal.ofReal p) (volume.restrict Q)).toReal ≤
      B * (volume ({P | u P < ell} ∩ Q)).toReal ^ (1 / p) := by
  let E := {P | u P < ell} ∩ Q
  have hE : MeasurableSet E := by
    simpa only [E, Set.preimage, mem_Iio, inter_comm] using
      (hu.isOpen_inter_preimage hQ (isOpen_Iio (a := ell))).measurableSet
  have hm := localizedSource_aestronglyMeasurable A hQ hpsi hu hopm
  have hbound : ∀ᵐ P ∂(volume.restrict Q),
      ‖localizedSource A psi u P‖ ≤ ‖E.indicator (fun _ => B) P‖ := by
    filter_upwards [ae_restrict_mem hQ.measurableSet, hop] with P hP hb
    by_cases hs : u P < psi P
    · have hPE : P ∈ E := ⟨hs.trans_le (hlevel P hP), hP⟩
      rw [indicator_of_mem hPE]
      simp only [localizedSource, indicator, mem_ofPred_eq, hs, ite_true, Real.norm_eq_abs,
        abs_of_nonneg hB, abs_of_nonneg (le_max_right (backwardOperator A psi P) 0)]
      exact max_le ((le_abs_self _).trans hb) hB
    · simp only [localizedSource, indicator, mem_ofPred_eq, hs, ite_false, norm_zero]
      exact norm_nonneg _
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hnorm := eLpNorm_mono_ae (p := ENNReal.ofReal p) hm hbound
  rw [eLpNorm_indicator_const hE.nullMeasurableSet
    (ENNReal.ofReal_pos.mpr hp0).ne' ENNReal.ofReal_ne_top] at hnorm
  have hmeasure : (volume.restrict Q) E = volume E := by
    rw [Measure.restrict_apply hE, inter_eq_left.mpr inter_subset_right]
  rw [hmeasure, ENNReal.toReal_ofReal hp0.le] at hnorm
  have hEfinite : volume E ≠ ⊤ :=
    measure_ne_top_of_subset inter_subset_right hQfinite
  have hright : ‖B‖ₑ * volume E ^ (1 / p) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (ENNReal.rpow_ne_top_of_nonneg
      (one_div_nonneg.mpr hp0.le) hEfinite)
  have hreal := ENNReal.toReal_mono hright hnorm
  simpa only [ENNReal.toReal_mul, Real.enorm_eq_ofReal_abs, abs_of_nonneg hB,
    ENNReal.toReal_ofReal hB, ← ENNReal.toReal_rpow] using hreal

end HypoellipticAleksandrov.KineticAleksandrov.Holder
