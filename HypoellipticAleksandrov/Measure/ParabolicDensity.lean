module

public import Mathlib.Probability.Martingale.Convergence
public import HypoellipticAleksandrov.Measure.ParabolicDyadicAverage
public import HypoellipticAleksandrov.Measure.ParabolicDyadicGeneration

/-!
# Differentiation along parabolic dyadic cells

This module proves almost-everywhere convergence of the explicit complete-generation
parabolic dyadic averages.  Applying that convergence to a measurable-set indicator gives
eventual strict density in every sufficiently fine addressed cell containing the point.

The argument uses conditional-expectation convergence for the finite reference-cell measure.
It does not use metric differentiation or perform the later maximal dense-cell selection.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

private theorem integrable_indicator_one
    (d : ℕ) (Gamma : Set (ParabolicDyadicReferenceSpace d))
    (hGamma : MeasurableSet Gamma) :
    Integrable (Gamma.indicator (fun _ => (1 : ℝ)))
      (parabolicDyadicReferenceMeasure d) := by
  let : IsFiniteMeasure (parabolicDyadicReferenceMeasure d) :=
    ⟨lt_top_iff_ne_top.mpr (parabolicDyadicReferenceMeasure_univ_ne_top d)⟩
  exact IntegrableOn.integrable_indicator integrableOn_const hGamma

private theorem parabolicDyadicCellAverage_indicator_one
    {d n : ℕ} (Gamma : Set (ParabolicDyadicReferenceSpace d))
    (hGamma : MeasurableSet Gamma) (index : ParabolicDyadicIndex d n) :
    parabolicDyadicCellAverage d n
        (Gamma.indicator (fun _ => (1 : ℝ))) index =
      ((parabolicDyadicReferenceMeasure d).real
          (parabolicDyadicRestrictedCell index))⁻¹ *
        (parabolicDyadicReferenceMeasure d).real
          (parabolicDyadicRestrictedCell index ∩ Gamma) := by
  unfold parabolicDyadicCellAverage
  rw [setIntegral_indicator hGamma, setIntegral_const, smul_eq_mul, mul_one]

/-- At almost every point, the explicit complete-generation parabolic dyadic averages of an
integrable function converge to that function. -/
theorem parabolicDyadicCheckpointAverage_tendsto_ae
    (d : ℕ) (f : ParabolicDyadicReferenceSpace d → ℝ)
    (hf : Integrable f (parabolicDyadicReferenceMeasure d)) :
    ∀ᵐ z ∂parabolicDyadicReferenceMeasure d,
      Tendsto (fun n => parabolicDyadicCheckpointAverage d n f z)
        atTop (nhds (f z)) := by
  classical
  let : IsFiniteMeasure (parabolicDyadicReferenceMeasure d) :=
    ⟨lt_top_iff_ne_top.mpr (parabolicDyadicReferenceMeasure_univ_ne_top d)⟩
  let f' : ParabolicDyadicReferenceSpace d → ℝ := hf.1.mk f
  have hff' : f =ᵐ[parabolicDyadicReferenceMeasure d] f' := by
    simpa only [f'] using hf.1.ae_eq_mk
  have hf' : Integrable f' (parabolicDyadicReferenceMeasure d) :=
    hf.congr hff'
  have hf'meas : StronglyMeasurable[⨆ k, parabolicDyadicFiltration d k] f' := by
    rw [iSup_parabolicDyadicFiltration_eq_referenceMeasurableSpace]
    simpa only [f'] using hf.1.stronglyMeasurable_mk
  have hcond : ∀ᵐ z ∂parabolicDyadicReferenceMeasure d,
      Tendsto
        (fun k => ((parabolicDyadicReferenceMeasure d)[f' |
          parabolicDyadicFiltration d k]) z)
        atTop (nhds (f' z)) :=
    hf'.tendsto_ae_condExp hf'meas
  have havg : ∀ᵐ z ∂parabolicDyadicReferenceMeasure d, ∀ n,
      parabolicDyadicCheckpointAverage d n f z =
        ((parabolicDyadicReferenceMeasure d)[f' |
          parabolicDyadicFiltration d ((d + 2) * n)]) z := by
    rw [ae_all_iff]
    intro n
    exact (parabolicDyadicCheckpointAverage_ae_eq_condExp d n f hf).trans
      (condExp_congr_ae hff')
  have hcheckpoint : Tendsto (fun n : ℕ => (d + 2) * n) atTop atTop := by
    apply tendsto_atTop_mono (fun n => ?_) tendsto_id
    exact Nat.le_mul_of_pos_left n (by omega)
  filter_upwards [hcond, havg, hff'] with z hzcond hzavg hzff'
  have htendsto : Tendsto
      (fun n => ((parabolicDyadicReferenceMeasure d)[f' |
        parabolicDyadicFiltration d ((d + 2) * n)]) z)
      atTop (nhds (f' z)) :=
    hzcond.comp hcheckpoint
  have havgTendsto : Tendsto
      (fun n => parabolicDyadicCheckpointAverage d n f z)
      atTop (nhds (f' z)) :=
    Tendsto.congr' (Eventually.of_forall fun n => (hzavg n).symm) htendsto
  simpa only [hzff'] using havgTendsto

/-- At almost every point of a measurable set, every sufficiently fine addressed cell
containing the point has density strictly above the fixed threshold. -/
theorem ae_eventually_parabolicDyadicRestrictedCell_density_gt
    (d : ℕ) (Gamma : Set (ParabolicDyadicReferenceSpace d))
    (hGamma : MeasurableSet Gamma) (xi : ℝ)
    (hxi : xi ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ᵐ z ∂parabolicDyadicReferenceMeasure d,
      z ∈ Gamma →
        ∀ᶠ n in atTop, ∀ index : ParabolicDyadicIndex d n,
          z ∈ parabolicDyadicRestrictedCell index →
            xi * (parabolicDyadicReferenceMeasure d).real
                (parabolicDyadicRestrictedCell index) <
              (parabolicDyadicReferenceMeasure d).real
                (parabolicDyadicRestrictedCell index ∩ Gamma) := by
  have hconverges := parabolicDyadicCheckpointAverage_tendsto_ae d
    (Gamma.indicator (fun _ => (1 : ℝ)))
    (integrable_indicator_one d Gamma hGamma)
  filter_upwards [hconverges] with z hzconverges
  intro hzGamma
  have hzconvergesOne : Tendsto
      (fun n => parabolicDyadicCheckpointAverage d n
        (Gamma.indicator (fun _ => (1 : ℝ))) z)
      atTop (nhds 1) := by
    simpa only [Set.indicator_of_mem hzGamma] using hzconverges
  have hdensity : ∀ᶠ n in atTop,
      xi < parabolicDyadicCheckpointAverage d n
        (Gamma.indicator (fun _ => (1 : ℝ))) z :=
    hzconvergesOne.eventually_const_lt hxi.2
  filter_upwards [hdensity] with n hn
  intro index hzindex
  rw [parabolicDyadicCheckpointAverage_eq_cellAverage _ index z hzindex,
    parabolicDyadicCellAverage_indicator_one Gamma hGamma index] at hn
  exact (lt_inv_mul_iff₀'
    (parabolicDyadicReferenceMeasure_restrictedCell_real_pos index)).mp hn

/-- Almost every point of a measurable set lies in an addressed generation cell on which
that set has density strictly above the fixed threshold. -/
theorem ae_exists_parabolicDyadicRestrictedCell_density_gt
    (d : ℕ) (Gamma : Set (ParabolicDyadicReferenceSpace d))
    (hGamma : MeasurableSet Gamma) (xi : ℝ)
    (hxi : xi ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ᵐ z ∂parabolicDyadicReferenceMeasure d,
      z ∈ Gamma →
        ∃ n, ∃ index : ParabolicDyadicIndex d n,
          z ∈ parabolicDyadicRestrictedCell index ∧
            xi * (parabolicDyadicReferenceMeasure d).real
                (parabolicDyadicRestrictedCell index) <
              (parabolicDyadicReferenceMeasure d).real
                (parabolicDyadicRestrictedCell index ∩ Gamma) := by
  have heventually := ae_eventually_parabolicDyadicRestrictedCell_density_gt
    d Gamma hGamma xi hxi
  filter_upwards [heventually] with z hzEventually
  intro hzGamma
  obtain ⟨n, hn⟩ := (hzEventually hzGamma).exists
  have hzcover : (z : TimeVelocity d) ∈
      ⋃ index : ParabolicDyadicIndex d n,
        parabolicDyadicHalfOpenCell index := by
    rw [iUnion_parabolicDyadicHalfOpenCell_eq_reference]
    exact z.property
  obtain ⟨index, hzindex⟩ := Set.mem_iUnion.mp hzcover
  have hzindex' : z ∈ parabolicDyadicRestrictedCell index := by
    change (z : TimeVelocity d) ∈ parabolicDyadicHalfOpenCell index
    exact hzindex
  exact ⟨n, index, hzindex', hn index hzindex'⟩

end

end HypoellipticAleksandrov.Parabolic
