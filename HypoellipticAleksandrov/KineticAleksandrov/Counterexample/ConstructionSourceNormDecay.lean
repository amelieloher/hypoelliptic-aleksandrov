module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionSourceRecovery
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionStationaryNorm
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionScales

/-! # Vanishing positive source norms before the spatial smoothing diagonal -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory Filter Set
open scoped Topology ENNReal

/-- Shell domination lifts to the literal spacetime source norm, with the finite time
factor and no change to the selected profile witnesses. -/
theorem construction_indicatorSource_norm_le {d : ℕ} (hd : 1 ≤ d)
    {alpha : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1)
    (h : CounterProfileStatement d alpha) (r mu R m T S : ℝ)
    (hr : 0 < r) (hmu : 0 < mu) (hR : 0 < R) (hm : m < R ^ 2) (hS : 0 < S)
    (hrate : mu = (d : ℝ) * profileLowerEllipticity h / R ^ 2)
    (hscale : 2 * Real.rpow r alpha ≤ 1)
    (hmargin : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 < m)
    (p : ℝ≥0∞) (hp0 : p ≠ 0) (hpTop : p ≠ ∞) :
    eLpNorm (fun P : KineticPoint d =>
      max (constructionIndicatorSource h r mu R (KineticPoint.equivProd d P)) 0) p
      (volume.restrict (backwardCylinder (⟨T, 0, 0⟩ : KineticPoint d) S)) ≤
      (volume (Ioo (T - S ^ 2) T)) ^ (1 / p.toReal) *
        eLpNorm (flatSource (profileMatrix h) (profileFunction h) flatteningPsi alpha r)
          p (volume.restrict {q | profileFunction h q < 1}) := by
  obtain ⟨_, _, _, _, hAm, _, hH, _, _, _, _, hgv, _⟩ := selectedProfile_spec h
  let f := flatSourceWithJet (profileMatrix h) (profileFunction h)
    (profileVelocityJet h) alpha r
  let D := {q | profileFunction h q < 1}
  have hD : MeasurableSet D := (isOpen_lt hH continuous_const).measurableSet
  have hf : Measurable f := measurable_flatSourceWithJet _ _ _ _ _ hAm hH.measurable hgv
  have hbound := construction_fixed_time_le_ae_spacetime
    (fun z => max (constructionIndicatorSource h r mu R z) 0)
    (fun z => D.indicator f z.2)
    ((construction_indicatorSource_measurable h r mu R).max measurable_const)
    ((hf.indicator hD).comp measurable_snd) ?_
  · have hm := ((construction_indicatorSource_measurable h r mu R).comp
        (KineticPoint.measurable_equivProd d)).max (measurable_const (a := (0 : ℝ)))
    have hn := eLpNorm_mono_ae_real (p := p)
      (g := fun P : KineticPoint d => D.indicator f (P.position, P.velocity))
      (μ := volume.restrict (backwardCylinder (⟨T, 0, 0⟩ : KineticPoint d) S))
      hm.aestronglyMeasurable.restrict
      (ae_restrict_of_ae (hbound.mono (fun P hP => by
        simpa only [Real.norm_of_nonneg (le_max_right _ _)] using! hP)))
    apply hn.trans
    have he : eLpNorm f p (volume.restrict D) =
        eLpNorm (flatSource (profileMatrix h) (profileFunction h) flatteningPsi alpha r)
          p (volume.restrict D) :=
      eLpNorm_congr_ae (ae_restrict_of_ae
        (flatSource_ae_eq_jet_of_profile h r).symm)
    simpa only [he] using construction_stationary_indicator_norm_le T S hS D hD f hf p hp0 hpTop
  · intro t
    filter_upwards [construction_extended_positive_source_le_shell_ae hd ha ha1 h
      r mu R m hr hmu hR hm hrate hscale hmargin t,
      construction_extendedSource_eq_indicator_ae hd ha ha1 h r mu R m hr hmu hR hm
        hscale hmargin t, flatSource_ae_eq_jet_of_profile h r] with q hb he hjet
    rw [constructionIndicatorSource_apply, ← he]
    by_cases hq : q ∈ D
    · rw [indicator_of_mem hq]
      have hb' := hb
      rw [indicator_of_mem hq, hjet] at hb'
      exact hb'
    · rw [indicator_of_notMem hq]
      change q ∉ {y | profileFunction h y < 1} at hq
      simpa only [indicator_of_notMem hq] using hb

/-- Positive selected sources tend to zero on the fixed cylinder as the flattening
scales tend to zero in the full subcritical range. -/
theorem construction_indicatorSource_norm_tendsto {d : ℕ} (hd : 1 ≤ d)
    {alpha : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1)
    (h : CounterProfileStatement d alpha) (mu R m T S p : ℝ)
    (hmu : 0 < mu) (hR : 0 < R) (hm : m < R ^ 2) (hS : 0 < S)
    (hrate : mu = (d : ℝ) * profileLowerEllipticity h / R ^ 2)
    (hmargin : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 < m)
    (hp : 1 ≤ p) (he : 0 < alpha - 2 + 4 * (d : ℝ) / p)
    (r : ℕ → ℝ) (hr : ∀ j, 0 < r j) (hs : ∀ j, 2 * Real.rpow (r j) alpha ≤ 1)
    (hlim : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun j => eLpNorm (fun P : KineticPoint d =>
      max (constructionIndicatorSource h (r j) mu R (KineticPoint.equivProd d P)) 0)
      (ENNReal.ofReal p)
      (volume.restrict (backwardCylinder (⟨T, 0, 0⟩ : KineticPoint d) S)))
      atTop (𝓝 0) := by
  have hp0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr (zero_lt_one.trans_le hp)).ne'
  have hpTop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  let C := (volume (Ioo (T - S ^ 2) T)) ^ (1 / (ENNReal.ofReal p).toReal)
  have hC : C ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg
    (by positivity) (measure_Ioo_lt_top.ne)
  have hu := (ENNReal.continuous_const_mul hC).tendsto (0 : ℝ≥0∞) |>.comp
    (construction_flat_source_decay_of_profile h p ha ha1 hp he r hr hlim)
  have hu0 : Tendsto (fun j => C * eLpNorm
      (flatSource (profileMatrix h) (profileFunction h) flatteningPsi alpha (r j))
      (ENNReal.ofReal p) (volume.restrict {q | profileFunction h q < 1}))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using! hu
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu0
    (fun _ => bot_le) (fun j => construction_indicatorSource_norm_le hd ha ha1 h
      (r j) mu R m T S (hr j) hmu hR hm hS hrate (hs j) hmargin _ hp0 hpTop)

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
