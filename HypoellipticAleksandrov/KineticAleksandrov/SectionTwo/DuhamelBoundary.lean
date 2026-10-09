module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.DuhamelSlice

/-! # Continuous zero traces for the kinetic Duhamel potential -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set Filter
open scoped Topology
variable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}

/-- Dominated convergence gives continuity of the kinetic potential up to the past boundary. -/
theorem continuousWithinAt_duhamelPotential (hΩa : IsAdmissibleEvolutionDomain Ω)
    (hΩ : MeasurableSet Ω) (hγ : Continuous γ)
    (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    (S : TerminalOperatorFamily Ω γ) (K : MovingFiberKernel Ω γ)
    (hreal : RealizesTerminalEvolution Ω γ hΩ B b S K)
    (g : KineticPoint d → ℝ) (hgn : ∀ p, 0 ≤ g p) (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (hgs : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × EvolutionAmbientState d =>
      g ⟨q.1, q.2.1, q.2.2⟩)) (T : ℝ)
    (hgU : tsupport g ⊆ evolutionPastOpenCylinder Ω γ T)
    (p₀ : KineticPoint d) (hp₀ : p₀ ∈ evolutionPastClosedCylinder Ω γ T) :
    ContinuousWithinAt (duhamelPotential K T g)
      (evolutionPastClosedCylinder Ω γ T) p₀ := by
  obtain ⟨a, btime, -, hab⟩ := exists_time_window_of_hasCompactSupport g hgc
  obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hgc
  have hgb : ∀ p, g p ≤ C := fun p => (le_abs_self _).trans (by simpa using hC p)
  have hC0 : 0 ≤ C := (hgn ⟨0, 0, 0⟩).trans (hgb _)
  have hgm : Measurable g := hg.measurable
  have hmeas := measurable_duhamelIntegrand K hΩ hγ g hgm
  let F : KineticPoint d → ℝ → ℝ := fun p r =>
    (Ioc p.time T).indicator (duhamelIntegrand K g p) r
  have hW : duhamelPotential K T g = fun p => ∫ r, F p r :=
    funext fun p => (integral_indicator measurableSet_Ioc).symm
  have hFm : ∀ p, Measurable (F p) := fun p =>
    (hmeas.comp (measurable_const.prodMk measurable_id)).indicator measurableSet_Ioc
  have hF0 : ∀ p r, r ∉ Icc a btime → F p r = 0 := by
    intro p r hr
    by_cases h : r ∈ Ioc p.time T
    · exact (indicator_of_mem h _).trans
        (duhamelIntegrand_eq_zero_of_time_not_mem K g a btime hab p r hr)
    · exact indicator_of_notMem h _
  have hbd : ∀ p r, ‖F p r‖ ≤ (Icc a btime).indicator (fun _ => C) r := by
    intro p r
    by_cases hr : r ∈ Icc a btime
    · rw [indicator_of_mem hr, Real.norm_eq_abs]
      by_cases h : r ∈ Ioc p.time T
      · change |(Ioc p.time T).indicator (duhamelIntegrand K g p) r| ≤ C
        rw [indicator_of_mem h,
          abs_of_nonneg (duhamelIntegrand_nonneg K g hgn p r)]
        exact duhamelIntegrand_le K g hgn C hC0 hgb p r
      · change |(Ioc p.time T).indicator (duhamelIntegrand K g p) r| ≤ C
        rw [indicator_of_notMem h, abs_zero]
        exact hC0
    · rw [indicator_of_notMem hr, hF0 p r hr, norm_zero]
  have hint : Integrable ((Icc a btime).indicator (fun _ => C)) :=
    (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp))
  have hne : ∀ᵐ r ∂(volume : Measure ℝ), r ∉ ({p₀.time} : Set ℝ) :=
    measure_eq_zero_iff_ae_notMem.1 (measure_singleton _)
  have hcont : ∀ᵐ r ∂(volume : Measure ℝ),
      ContinuousWithinAt (fun p => F p r) (evolutionPastClosedCylinder Ω γ T) p₀ := by
    filter_upwards [hne] with r hr
    rcases lt_trichotomy r p₀.time with h | h | h
    · have hopen : {p : KineticPoint d | r < p.time} ∈ 𝓝 p₀ :=
        (isOpen_lt continuous_const continuous_time).mem_nhds h
      have hev : (fun p => F p r) =ᶠ[𝓝[evolutionPastClosedCylinder Ω γ T] p₀] fun _ => (0 : ℝ) := by
        filter_upwards [mem_nhdsWithin_of_mem_nhds hopen] with p hp
        exact indicator_of_notMem (fun hh => absurd hh.1 (not_lt.2 hp.le)) _
      have h0 : F p₀ r = 0 := indicator_of_notMem (fun hh => absurd hh.1 (not_lt.2 h.le)) _
      exact continuousWithinAt_const.congr_of_eventuallyEq hev h0
    · exact absurd h (by simpa using hr)
    · by_cases hrT : r ≤ T
      · have hc1 := continuousOn_duhamelIntegrand hΩa hΩ B b S K hreal
          g hg hgc hgs T hgU r
        have hp₀r : p₀ ∈ evolutionPastClosedCylinder Ω γ r := ⟨h.le, hp₀.2⟩
        have hnh : evolutionPastClosedCylinder Ω γ r ∈ 𝓝[evolutionPastClosedCylinder Ω γ T] p₀ :=
          mem_nhdsWithin.2 ⟨{p | p.time < r}, isOpen_lt continuous_time continuous_const, h,
            fun p hp => ⟨hp.1.le, hp.2.2⟩⟩
        have hc2 := (hc1 p₀ hp₀r).mono_of_mem_nhdsWithin hnh
        have hev : (fun p => F p r) =ᶠ[𝓝[evolutionPastClosedCylinder Ω γ T] p₀]
            fun p => duhamelIntegrand K g p r := by
          have hopen : {p : KineticPoint d | p.time < r} ∈ 𝓝 p₀ :=
            (isOpen_lt continuous_time continuous_const).mem_nhds h
          filter_upwards [mem_nhdsWithin_of_mem_nhds hopen] with p hp
          exact indicator_of_mem (show r ∈ Ioc p.time T from ⟨hp, hrT⟩) _
        exact hc2.congr_of_eventuallyEq hev
          (indicator_of_mem (show r ∈ Ioc p₀.time T from ⟨h, hrT⟩) _)
      · have hz : ∀ p, F p r = 0 := fun p =>
          indicator_of_notMem (fun hh => hrT hh.2) _
        simp only [hz]
        exact continuousWithinAt_const
  rw [hW]
  exact continuousWithinAt_of_dominated
    (Eventually.of_forall fun p => (hFm p).aestronglyMeasurable)
    (Eventually.of_forall fun p => Eventually.of_forall fun r => hbd p r) hint hcont

/-- The kinetic Duhamel potential is continuous on the entire closed past cylinder. -/
theorem continuousOn_duhamelPotential (hΩa : IsAdmissibleEvolutionDomain Ω)
    (hΩ : MeasurableSet Ω) (hγ : Continuous γ)
    (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    (S : TerminalOperatorFamily Ω γ) (K : MovingFiberKernel Ω γ)
    (hreal : RealizesTerminalEvolution Ω γ hΩ B b S K)
    (g : KineticPoint d → ℝ) (hgn : ∀ p, 0 ≤ g p) (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (hgs : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × EvolutionAmbientState d =>
      g ⟨q.1, q.2.1, q.2.2⟩)) (T : ℝ)
    (hgU : tsupport g ⊆ evolutionPastOpenCylinder Ω γ T) :
    ContinuousOn (duhamelPotential K T g) (evolutionPastClosedCylinder Ω γ T) :=
  fun p hp => continuousWithinAt_duhamelPotential hΩa hΩ hγ B b S K hreal
    g hgn hg hgc hgs T hgU p hp

/-- The Duhamel potential has zero values on the terminal closure. -/
theorem duhamelPotential_terminal (K : MovingFiberKernel Ω γ) (T : ℝ)
    (g : KineticPoint d → ℝ) (p : KineticPoint d)
    (hp : p ∈ evolutionTerminalClosure Ω γ T) : duhamelPotential K T g p = 0 :=
  duhamelPotential_eq_zero_of_terminal_le K T g p hp.1.ge

/-- The Duhamel potential has zero values on the lateral frontier. -/
theorem duhamelPotential_lateral (hΩa : IsAdmissibleEvolutionDomain Ω)
    (K : MovingFiberKernel Ω γ) (T : ℝ) (g : KineticPoint d → ℝ)
    (p : KineticPoint d) (hp : p ∈ evolutionLateralFrontier Ω γ T) :
    duhamelPotential K T g p = 0 := by
  apply duhamelPotential_eq_zero_of_not_mem K T g p
  have hf := hp.2
  rw [(isOpen_movingDomain_of_isAdmissibleEvolutionDomain γ hΩa p.time).frontier_eq] at hf
  exact hf.2

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
