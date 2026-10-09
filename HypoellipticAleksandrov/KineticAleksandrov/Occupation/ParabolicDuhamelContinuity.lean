module

public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelSlice

/-!
# Continuity of the parabolic Duhamel potential and its traces

Each source slice integrand `p ↦ integrand p r` is continuous on the closed cylinder at time `r`
(it is the classical solution `V_r`), vanishes on the lateral frontier, and equals `g(r,·)` on
the terminal face.  Dominated convergence in the source time `r` then gives continuity of the
potential on the closed region `{s ≤ T, v ∈ closure Ω_s}`, hence the continuous zero terminal
and lateral traces, without any barrier estimate.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open MeasureTheory Set Filter
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open scoped ENNReal ProbabilityTheory Topology

variable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}
variable (K : MovingFiberKernel Ω γ)

/-- On the closed cylinder the integrand is the classical slice solution. -/
theorem integrand_eq_slice_solution (hΩa : IsAdmissibleEvolutionDomain Ω)
    (hΩ : MeasurableSet Ω) (g : TimeVelocity d → ℝ) (r : ℝ) (V : TimeVelocity d → ℝ)
    (hlat : ∀ p ∈ ParabolicProbe.scalarLateralFrontier Ω γ r, V p = 0)
    (hV : ∀ (s : ℝ) (hsr : s ≤ r) (y : EvolutionPosition Ω γ s),
      V (s, y.1) = parabolicSourceIntegral K hΩ g s r hsr y)
    (p : TimeVelocity d) (hp : p ∈ sliceClosedCylinder Ω γ r) :
    parabolicDuhamelIntegrand K hΩ g p r = V p := by
  by_cases hmem : p.2 ∈ movingDomain Ω γ p.1
  · rw [parabolicDuhamelIntegrand_of_valid K hΩ g p r ⟨hp.1, hmem⟩]
    exact (hV p.1 hp.1 ⟨p.2, hmem⟩).symm
  · rw [parabolicDuhamelIntegrand_of_not_valid K hΩ g p r (fun h => hmem h.2)]
    have hfr : p.2 ∈ frontier (movingDomain Ω γ p.1) := by
      rw [(isOpen_movingDomain_of_isAdmissibleEvolutionDomain γ hΩa p.1).frontier_eq]
      exact ⟨hp.2, hmem⟩
    exact (hlat p ⟨hp.1, hfr⟩).symm

/-- The slice integrand is continuous on the closed cylinder, and equals the classical
solution there, which is smooth in the open cylinder and has the stated trace data. -/
theorem slice_regularity {B : CoefficientField d} (hΩa : IsAdmissibleEvolutionDomain Ω)
    (hP : SectionTwo.HasParabolicMarginalBundle Ω γ
      (measurableSet_of_isAdmissibleEvolutionDomain hΩa) (zIndependentCoefficient B) K)
    (g : TimeVelocity d → ℝ) (hgs : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) (T : ℝ)
    (hgU : tsupport g ⊆ duhamelFiber Ω γ T) (r : ℝ) :
    ∃ V : TimeVelocity d → ℝ,
      (∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ sliceClosedCylinder Ω γ r, |V p| ≤ C) ∧
      ContinuousOn V (sliceClosedCylinder Ω γ r) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) V (sliceOpenCylinder Ω γ r) ∧
      (∀ p ∈ sliceOpenCylinder Ω γ r,
        scalarParabolicOperator B (fun _ _ => 0) V p = 0) ∧
      (∀ v ∈ closure (movingDomain Ω γ r), V (r, v) = g (r, v)) ∧
      ∀ p ∈ sliceClosedCylinder Ω γ r,
        parabolicDuhamelIntegrand K (measurableSet_of_isAdmissibleEvolutionDomain hΩa) g p r
          = V p := by
  obtain ⟨V, ⟨hbd, hcont, hsm, heq, hterm, hlat⟩, hVs⟩ :=
    exists_slice_solution K (measurableSet_of_isAdmissibleEvolutionDomain hΩa) hP g hgs hgc T
      hgU r
  refine ⟨V, hbd, hcont, hsm, heq, fun v hv => ?_,
    integrand_eq_slice_solution K hΩa _ g r V hlat hVs⟩
  exact hterm (r, v) ⟨rfl, hv⟩

/-- A compactly supported source vanishes at all times outside a bounded interval. -/
theorem exists_time_range (g : TimeVelocity d → ℝ) (hgc : HasCompactSupport g) :
    ∃ a b : ℝ, ∀ r, r ∉ Icc a b → ∀ v, g (r, v) = 0 := by
  have hK : IsCompact (Prod.fst '' tsupport g) := hgc.image continuous_fst
  obtain ⟨b, hb⟩ := hK.bddAbove
  obtain ⟨a, ha⟩ := hK.bddBelow
  refine ⟨a, b, fun r hr v => ?_⟩
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  exact hr ⟨ha ⟨_, hmem, rfl⟩, hb ⟨_, hmem, rfl⟩⟩

/-- **Continuity of the Duhamel potential** on the closed region
`{s ≤ T, v ∈ closure Ω_s}`, by dominated convergence in the source time. -/
theorem continuousWithinAt_duhamelPotential {B : CoefficientField d}
    (hΩa : IsAdmissibleEvolutionDomain Ω) (hγ : Continuous γ)
    (hP : SectionTwo.HasParabolicMarginalBundle Ω γ
      (measurableSet_of_isAdmissibleEvolutionDomain hΩa) (zIndependentCoefficient B) K)
    (g : TimeVelocity d → ℝ) (hgn : ∀ p, 0 ≤ g p) (hgs : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g) (T : ℝ) (hgU : tsupport g ⊆ duhamelFiber Ω γ T)
    (p₀ : TimeVelocity d) (hp₀ : p₀ ∈ duhamelClosedFiber Ω γ T) :
    ContinuousWithinAt
      (parabolicDuhamelPotential K (measurableSet_of_isAdmissibleEvolutionDomain hΩa) T g)
      (duhamelClosedFiber Ω γ T) p₀ := by
  have hΩ := measurableSet_of_isAdmissibleEvolutionDomain hΩa
  obtain ⟨a, b, hab⟩ := exists_time_range g hgc
  obtain ⟨C, hC⟩ := hgs.continuous.bounded_above_of_compact_support hgc
  have hgb : ∀ p, g p ≤ C := fun p => (le_abs_self _).trans (by simpa using hC p)
  have hC0 : 0 ≤ C := (hgn (0, 0)).trans (hgb _)
  have hgm : Measurable g := hgs.continuous.measurable
  have hg : ∀ r, Measurable (fun v : PDE.Vec d => g (r, v)) := fun r =>
    hgm.comp (measurable_const.prodMk measurable_id)
  have hmeas := measurable_parabolicDuhamelIntegrand K hΩ hγ g hgm
  let F : TimeVelocity d → ℝ → ℝ := fun p r =>
    (Ioc p.1 T).indicator (parabolicDuhamelIntegrand K hΩ g p) r
  have hW : parabolicDuhamelPotential K hΩ T g = fun p => ∫ r, F p r :=
    funext fun p => (integral_indicator measurableSet_Ioc).symm
  have hFm : ∀ p, Measurable (F p) := fun p =>
    (hmeas.comp (measurable_const.prodMk measurable_id)).indicator measurableSet_Ioc
  have hF0 : ∀ p r, r ∉ Icc a b → F p r = 0 := by
    intro p r hr
    by_cases h : r ∈ Ioc p.1 T
    · exact (indicator_of_mem h _).trans
        (parabolicDuhamelIntegrand_eq_zero_of_slice K hΩ g hg p r (hab r hr))
    · exact indicator_of_notMem h _
  have hbd : ∀ p r, ‖F p r‖ ≤ (Icc a b).indicator (fun _ => C) r := by
    intro p r
    by_cases hr : r ∈ Icc a b
    · rw [indicator_of_mem hr, Real.norm_eq_abs]
      by_cases h : r ∈ Ioc p.1 T
      · change |(Ioc p.1 T).indicator (parabolicDuhamelIntegrand K hΩ g p) r| ≤ C
        rw [indicator_of_mem h,
          abs_of_nonneg (parabolicDuhamelIntegrand_nonneg K hΩ g hg hgn p r)]
        exact parabolicDuhamelIntegrand_le K hΩ g hg hgn C hgb p r
      · change |(Ioc p.1 T).indicator (parabolicDuhamelIntegrand K hΩ g p) r| ≤ C
        rw [indicator_of_notMem h, abs_zero]
        exact hC0
    · rw [indicator_of_notMem hr, hF0 p r hr, norm_zero]
  have hint : Integrable ((Icc a b).indicator (fun _ => C)) :=
    (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp))
  have hne : ∀ᵐ r ∂(volume : Measure ℝ), r ∉ ({p₀.1} : Set ℝ) :=
    measure_eq_zero_iff_ae_notMem.1 (measure_singleton _)
  have hcont : ∀ᵐ r ∂(volume : Measure ℝ),
      ContinuousWithinAt (fun p => F p r) (duhamelClosedFiber Ω γ T) p₀ := by
    filter_upwards [hne] with r hr
    rcases lt_trichotomy r p₀.1 with h | h | h
    · have hopen : {p : TimeVelocity d | r < p.1} ∈ 𝓝 p₀ :=
        (isOpen_lt continuous_const continuous_fst).mem_nhds h
      have hev : (fun p => F p r) =ᶠ[𝓝[duhamelClosedFiber Ω γ T] p₀] fun _ => (0 : ℝ) := by
        filter_upwards [mem_nhdsWithin_of_mem_nhds hopen] with p hp
        exact indicator_of_notMem (fun hh => absurd hh.1 (not_lt.2 hp.le)) _
      have h0 : F p₀ r = 0 := indicator_of_notMem (fun hh => absurd hh.1 (not_lt.2 h.le)) _
      exact continuousWithinAt_const.congr_of_eventuallyEq hev h0
    · exact absurd h (by simpa using hr)
    · by_cases hrT : r ≤ T
      · obtain ⟨V, -, hVc, -, -, -, hVeq⟩ := slice_regularity K hΩa hP g hgs hgc T hgU r
        have hc1 : ContinuousOn (fun p => parabolicDuhamelIntegrand K hΩ g p r)
            (sliceClosedCylinder Ω γ r) := hVc.congr (fun p hp => hVeq p hp)
        have hp₀r : p₀ ∈ sliceClosedCylinder Ω γ r := ⟨h.le, hp₀.2⟩
        have hnh : sliceClosedCylinder Ω γ r ∈ 𝓝[duhamelClosedFiber Ω γ T] p₀ :=
          mem_nhdsWithin.2 ⟨{p | p.1 < r}, isOpen_lt continuous_fst continuous_const, h,
            fun p hp => ⟨hp.1.le, hp.2.2⟩⟩
        have hc2 := (hc1 p₀ hp₀r).mono_of_mem_nhdsWithin hnh
        have hev : (fun p => F p r) =ᶠ[𝓝[duhamelClosedFiber Ω γ T] p₀]
            fun p => parabolicDuhamelIntegrand K hΩ g p r := by
          have hopen : {p : TimeVelocity d | p.1 < r} ∈ 𝓝 p₀ :=
            (isOpen_lt continuous_fst continuous_const).mem_nhds h
          filter_upwards [mem_nhdsWithin_of_mem_nhds hopen] with p hp
          exact indicator_of_mem (show r ∈ Ioc p.1 T from ⟨hp, hrT⟩) _
        exact hc2.congr_of_eventuallyEq hev (indicator_of_mem (show r ∈ Ioc p₀.1 T from ⟨h, hrT⟩) _)
      · have hz : ∀ p, F p r = 0 := fun p =>
          indicator_of_notMem (fun hh => hrT hh.2) _
        simp only [hz]
        exact continuousWithinAt_const
  rw [hW]
  exact continuousWithinAt_of_dominated
    (Eventually.of_forall fun p => (hFm p).aestronglyMeasurable)
    (Eventually.of_forall fun p => Eventually.of_forall fun r => hbd p r) hint hcont

/-- Continuity of the Duhamel potential on the closed region. -/
theorem continuousOn_duhamelPotential {B : CoefficientField d}
    (hΩa : IsAdmissibleEvolutionDomain Ω) (hγ : Continuous γ)
    (hP : SectionTwo.HasParabolicMarginalBundle Ω γ
      (measurableSet_of_isAdmissibleEvolutionDomain hΩa) (zIndependentCoefficient B) K)
    (g : TimeVelocity d → ℝ) (hgn : ∀ p, 0 ≤ g p) (hgs : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g) (T : ℝ) (hgU : tsupport g ⊆ duhamelFiber Ω γ T) :
    ContinuousOn
      (parabolicDuhamelPotential K (measurableSet_of_isAdmissibleEvolutionDomain hΩa) T g)
      (duhamelClosedFiber Ω γ T) :=
  fun p₀ hp₀ => continuousWithinAt_duhamelPotential K hΩa hγ hP g hgn hgs hgc T hgU p₀ hp₀

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
