module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.DuhamelEvolution
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.DuhamelBounded

/-! # Classical kinetic source slices for the Duhamel formula -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set

variable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}

/-- A continuous compactly supported kinetic source as bounded Borel data. -/
def duhamelSourceBorel (g : KineticPoint d → ℝ) (hg : Continuous g)
    (hc : HasCompactSupport g) : BoundedBorel (KineticPoint d) :=
  ⟨g, hg.measurable, by
    obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hc
    refine ⟨max C 0, le_max_right _ _, fun p => ?_⟩
    simpa only [Real.norm_eq_abs] using (hC p).trans (le_max_left _ _)⟩

/-- A smooth source supported in the past cylinder gives smooth compact terminal slices. -/
theorem isSmoothCompactTerminalDatum_duhamelSlice (g : KineticPoint d → ℝ)
    (hg : Continuous g) (hc : HasCompactSupport g)
    (hs : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × EvolutionAmbientState d =>
      g ⟨q.1, q.2.1, q.2.2⟩)) (T : ℝ)
    (hU : tsupport g ⊆ evolutionPastOpenCylinder Ω γ T) (r : ℝ) :
    IsSmoothCompactTerminalDatum Ω γ r (duhamelSlice (duhamelSourceBorel g hg hc) r) := by
  let f : EvolutionAmbientState d → ℝ := fun w => g ⟨r, w.1, w.2⟩
  let P : KineticPoint d → EvolutionAmbientState d := fun p => (p.position, p.velocity)
  have hP : Continuous P := continuous_position.prodMk continuous_velocity
  have hsub : tsupport f ⊆ P '' (tsupport g ∩ KineticPoint.time ⁻¹' {r}) := by
    apply closure_minimal
    · intro w hw
      exact ⟨⟨r, w.1, w.2⟩, ⟨subset_closure hw, rfl⟩, rfl⟩
    · exact ((hc.inter_right (isClosed_eq continuous_time continuous_const)).image hP).isClosed
  refine ⟨hs.comp (contDiff_const.prodMk contDiff_id), ?_, ?_⟩
  · exact ((hc.inter_right (isClosed_eq continuous_time continuous_const)).image hP
      ).of_isClosed_subset (isClosed_tsupport f) hsub
  · intro w hw
    obtain ⟨p, ⟨hp, hpr⟩, rfl⟩ := hsub hw
    refine ⟨?_, mem_univ _⟩
    have hm := (hU hp).2
    change p.time = r at hpr
    simpa only [hpr] using hm

/-- The supplied terminal evolution identifies every source slice with a classical solution. -/
theorem exists_duhamelSlice_solution (hΩ : MeasurableSet Ω)
    (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    (S : TerminalOperatorFamily Ω γ) (K : MovingFiberKernel Ω γ)
    (hreal : RealizesTerminalEvolution Ω γ hΩ B b S K)
    (g : KineticPoint d → ℝ) (hg : Continuous g) (hc : HasCompactSupport g)
    (hs : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × EvolutionAmbientState d =>
      g ⟨q.1, q.2.1, q.2.2⟩)) (T : ℝ)
    (hU : tsupport g ⊆ evolutionPastOpenCylinder Ω γ T) (r : ℝ) :
    ∃ V : KineticPoint d → ℝ,
      IsClassicalTerminalSolution Ω γ B b r
        (duhamelSlice (duhamelSourceBorel g hg hc) r) V ∧
      ∀ (s : ℝ) (hsr : s ≤ r) (p : EvolutionState Ω γ s),
        V ⟨s, p.1.1, p.1.2⟩ =
          duhamelSourceIntegral K g (evolutionQueryOfState Ω γ s r hsr p) := by
  obtain ⟨V, hV, hVS, -⟩ := hreal.1 r _
    (isSmoothCompactTerminalDatum_duhamelSlice g hg hc hs T hU r)
  refine ⟨V, hV, fun s hsr p => ?_⟩
  rw [hVS s hsr p]
  exact (duhamelSourceIntegral_eq_evolution hΩ B b S K hreal
    (duhamelSourceBorel g hg hc) s r hsr p).symm

/-- On the closed source cylinder the zero-extended integrand is the classical slice solution. -/
theorem duhamelIntegrand_eq_slice_solution (hΩa : IsAdmissibleEvolutionDomain Ω)
    (K : MovingFiberKernel Ω γ) (g : KineticPoint d → ℝ) (r : ℝ)
    (V : KineticPoint d → ℝ)
    (hlat : ∀ p ∈ evolutionLateralFrontier Ω γ r, V p = 0)
    (hV : ∀ (s : ℝ) (hsr : s ≤ r) (p : EvolutionState Ω γ s),
      V ⟨s, p.1.1, p.1.2⟩ =
        duhamelSourceIntegral K g (evolutionQueryOfState Ω γ s r hsr p))
    (p : KineticPoint d) (hp : p ∈ evolutionPastClosedCylinder Ω γ r) :
    duhamelIntegrand K g p r = V p := by
  classical
  by_cases hm : p.position ∈ movingDomain Ω γ p.time
  · rw [duhamelIntegrand, dite_eq_left ⟨hp.1, hm⟩]
    exact (hV p.time hp.1 ⟨(p.position, p.velocity), hm, mem_univ _⟩).symm
  · rw [duhamelIntegrand, dite_eq_right (fun h => hm h.2)]
    have hf : p.position ∈ frontier (movingDomain Ω γ p.time) := by
      rw [(isOpen_movingDomain_of_isAdmissibleEvolutionDomain γ hΩa p.time).frontier_eq]
      exact ⟨hp.2, hm⟩
    exact (hlat p ⟨hp.1, hf⟩).symm

/-- Source slices are continuous on their closed past cylinders. -/
theorem continuousOn_duhamelIntegrand (hΩa : IsAdmissibleEvolutionDomain Ω)
    (hΩ : MeasurableSet Ω) (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    (S : TerminalOperatorFamily Ω γ) (K : MovingFiberKernel Ω γ)
    (hreal : RealizesTerminalEvolution Ω γ hΩ B b S K)
    (g : KineticPoint d → ℝ) (hg : Continuous g) (hc : HasCompactSupport g)
    (hs : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × EvolutionAmbientState d =>
      g ⟨q.1, q.2.1, q.2.2⟩)) (T : ℝ)
    (hU : tsupport g ⊆ evolutionPastOpenCylinder Ω γ T) (r : ℝ) :
    ContinuousOn (fun p => duhamelIntegrand K g p r)
      (evolutionPastClosedCylinder Ω γ r) := by
  obtain ⟨V, hV, hVe⟩ := exists_duhamelSlice_solution hΩ B b S K hreal g hg hc hs T hU r
  exact hV.2.1.congr (fun p hp =>
    duhamelIntegrand_eq_slice_solution hΩa K g r V hV.2.2.2.2.2 hVe p hp)

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
