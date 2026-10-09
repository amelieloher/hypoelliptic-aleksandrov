module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripBoundary
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoundedSourceWeakAssembly

/-! # Literal Green representation of the actual compact-source potential -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo TheoremA Evolution

/-- A compact physical probe is bounded Borel data on the existing physical point carrier. -/
def nestedProbeDatum {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    (f : exitProbeSubmodule) : BoundedBorel Point :=
  ⟨exitProbePhysical f, (exitProbePhysical_continuous_compact f).1.measurable, by
    obtain ⟨M, hM⟩ := exitProbePhysical_bounded_source A f
    exact ⟨max M 0, le_max_right _ _, fun p => (hM p).1.trans (le_max_left _ _)⟩⟩

/-- Every valid pole has the same actual Green integral as its compact-source Duhamel value. -/
theorem nestedSourcePotential_eq_green {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    (H : Interval) (E : StripEvolution H) (T : ℝ) (f : exitProbeSubmodule)
    (e : StripPole H (T : WithTop ℝ)) :
    nestedSourcePotential H E T f e.1 =
      ∫ p, exitProbePhysical f p ∂stripGreenOfKernel H E.2 T e :=
  stripSourcePotential_eq_green H E.2 T (nestedProbeDatum A f) e

/-- The actual compact-source potential is globally Borel before any regularity argument. -/
theorem nestedSourcePotential_measurable (H : Interval) (E : StripEvolution H) (T : ℝ)
    (f : exitProbeSubmodule) : Measurable (nestedSourcePotential H E T f) := by
  exact (measurable_duhamelPotential E.2 (intervalDomain_measurable H) continuous_const T
    (exitProbePhysical f ∘ sectionTwoPoint)
    ((exitProbePhysical_continuous_compact f).1.measurable.comp
      (continuous_sectionTwoPoint 1).measurable)).comp
        (continuous_sectionTwoPoint 1).measurable

/-- Compact probes are integrable for every finite physical measure used in decomposition. -/
theorem nestedProbe_integrable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    (f : exitProbeSubmodule) (μ : Measure Point) [IsFiniteMeasure μ] :
    Integrable (exitProbePhysical f) μ := by
  obtain ⟨M, hM⟩ := exitProbePhysical_bounded_source A f
  apply Integrable.mono' (integrable_const M)
    (exitProbePhysical_continuous_compact f).1.measurable.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun p => by rw [Real.norm_eq_abs]; exact (hM p).1)

/-- Smaller-strip interior points lie in the physical closed past of the larger interval. -/
theorem nested_strip_union_exit_subset_closed (H1 H2 : Interval)
    (hsub : H1.carrier ⊆ H2.carrier) (sMinus T : ℝ) :
    reconstructionStrip H1 sMinus T ∪ reconstructionExit H1 sMinus T ⊆
      {p | p.time ≤ T ∧ p.velocity 0 ∈ Icc H2.lo H2.hi} := by
  have hcl : Icc H1.lo H1.hi ⊆ Icc H2.lo H2.hi := by
    have hc := closure_mono hsub
    change closure (Ioo H1.lo H1.hi) ⊆ closure (Ioo H2.lo H2.hi) at hc
    rwa [closure_Ioo H1.ordered.ne, closure_Ioo H2.ordered.ne] at hc
  intro p hp
  rcases hp with hp | hp
  · have hv := hsub hp.2.2
    exact ⟨hp.2.1.le, hv.1.le, hv.2.le⟩
  · rcases hp with hp | hp
    · exact ⟨hp.1.le, hcl hp.2⟩
    · refine ⟨hp.2.1.le, hcl ?_⟩
      rcases hp.2.2 with hv | hv <;> rw [hv]
      · exact ⟨le_rfl, H1.ordered.le⟩
      · exact ⟨H1.ordered.le, le_rfl⟩

/-- A valid smaller-interval pole is a valid larger-interval pole at the same physical point. -/
def nestedPoleInclusion (H1 H2 : Interval) (hsub : H1.carrier ⊆ H2.carrier)
    (T : WithTop ℝ) (e : StripPole H1 T) : StripPole H2 T :=
  ⟨e.1, e.2.1, hsub e.2.2⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
