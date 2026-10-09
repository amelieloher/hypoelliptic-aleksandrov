module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonMeasure
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.DomainDominationMeasure

/-! # Exact finite-time restrictions of the unique infinite-horizon exit measure -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo TheoremA Evolution

/-- Compact smooth physical probes determine finite measures on each open past half-space. -/
theorem physical_restrict_eq_of_early_probes {μ ν : Measure Point}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (R : ℝ)
    (hprobe : ∀ f : exitProbeSubmodule, tsupport f.1 ⊆ {x | timeCoord 1 x < R} →
      (∫ p, exitProbePhysical f p ∂μ) = ∫ p, exitProbePhysical f p ∂ν) :
    μ.restrict {p | p.time < R} = ν.restrict {p | p.time < R} := by
  let U : Set (EvolutionVec 1) := {x | timeCoord 1 x < R}
  have hU : IsOpen U := isOpen_lt (timeCoord 1).continuous continuous_const
  let a := (μ.map reconstructionPhysicalHomeomorph.symm).restrict U
  let b := (ν.map reconstructionPhysicalHomeomorph.symm).restrict U
  have hin (ρ : Measure Point) [IsFiniteMeasure ρ] (f : exitProbeSubmodule)
      (hs : tsupport f.1 ⊆ U) :
      (∫ x, f.1 x ∂(ρ.map reconstructionPhysicalHomeomorph.symm).restrict U) =
        ∫ p, exitProbePhysical f p ∂ρ := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))),
      integral_map reconstructionPhysicalHomeomorph.symm.continuous.measurable.aemeasurable
        f.2.1.continuous.measurable.aestronglyMeasurable]
    rfl
  have heq : a = b := by
    have htest (f : EvolutionVec 1 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
        (hc : HasCompactSupport f) (hs : tsupport f ⊆ U) :
        (∫ x, f x ∂a) = ∫ x, f x ∂b := by
      let F : exitProbeSubmodule := ⟨f, hf, hc⟩
      change (∫ x, F.1 x ∂a) = ∫ x, F.1 x ∂b
      rw [hin μ F hs, hin ν F hs]
      exact hprobe F hs
    apply le_antisymm
    · apply measure_le_of_smooth_integral_le hU
        (by simp only [a, Measure.restrict_restrict hU.measurableSet, inter_self])
      intro f hf hc hs _
      exact (htest f hf hc hs).le
    · apply measure_le_of_smooth_integral_le hU
        (by simp only [b, Measure.restrict_restrict hU.measurableSet, inter_self])
      intro f hf hc hs _
      exact (htest f hf hc hs).symm.le
  have hmap (ρ : Measure Point) :
      ((ρ.map reconstructionPhysicalHomeomorph.symm).restrict U).map
        reconstructionPhysicalHomeomorph = ρ.restrict {p | p.time < R} := by
    rw [Measure.restrict_map reconstructionPhysicalHomeomorph.symm.continuous.measurable
      hU.measurableSet, Measure.map_map reconstructionPhysicalHomeomorph.continuous.measurable
        reconstructionPhysicalHomeomorph.symm.continuous.measurable]
    have hid : reconstructionPhysicalHomeomorph ∘ reconstructionPhysicalHomeomorph.symm =
        (id : Point → Point) := funext reconstructionPhysicalHomeomorph.apply_symm_apply
    rw [hid, Measure.map_id]
    rfl
  have hh := congrArg (fun ρ : Measure (EvolutionVec 1) =>
    ρ.map reconstructionPhysicalHomeomorph) heq
  change a.map reconstructionPhysicalHomeomorph = b.map reconstructionPhysicalHomeomorph at hh
  rw [hmap μ, hmap ν] at hh
  exact hh

/-- The unique infinite exit measure has exactly the consistent finite early restrictions. -/
theorem stripInfiniteExit_restrict_finite
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (e : StripPole H ⊤)
    (T : ℝ) (ht : e.1.time < T) (R : ℝ) (hRT : R ≤ T) :
    (stripInfiniteExit hH hLE hlam hLam A H e).restrict {p | p.time < R} =
      (stripExit hH hLE hlam hLam A H T (stripPoleFinite H e T ht)).restrict
        {p | p.time < R} := by
  apply physical_restrict_eq_of_early_probes
  intro f hs
  rw [stripInfiniteExit_probe_integral]
  have hfinite := stripExitOfRealization_probe_integral hH hlam hLam A H _
    (stripEvolution_spec hH hLE hlam hLam A H) T (stripPoleFinite H e T ht) f
  change (∫ p, exitProbePhysical f p
    ∂stripExit hH hLE hlam hLam A H T (stripPoleFinite H e T ht)) =
      exitProbePhysical f e.1 + ∫ p, forwardScalarOperator A.a (exitProbePhysical f) p
        ∂stripGreen hH hLE hlam hLam A H T (stripPoleFinite H e T ht) at hfinite
  rw [hfinite, infinite_probe_source_integral hH hLE hlam hLam A H e T ht R hRT f hs]
  rfl

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
