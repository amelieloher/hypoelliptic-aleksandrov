module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonGreen
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GreenTestExtensionCanonical
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.DomainDominationMeasure

/-! # Exact consistency of finite exit measures before their terminal horizons -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo TheoremA Evolution

/-- A compact probe supported before R has zero operator at every time at least R. -/
theorem infinite_probe_operator_zero_after {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    (f : exitProbeSubmodule) (R : ℝ)
    (hs : tsupport f.1 ⊆ {x | timeCoord 1 x < R}) (p : Point) (hp : R ≤ p.time) :
    forwardScalarOperator A.a (exitProbePhysical f) p = 0 := by
  rw [exitProbePhysical_operator]
  apply reconstruction_operator_zero_off_tsupport
  intro hx
  have ht := hs hx
  change p.time < R at ht
  exact (not_lt_of_ge hp) ht

/-- The source integral of an early supported probe is independent of any later horizon. -/
theorem infinite_probe_source_integral
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (e : StripPole H ⊤)
    (T : ℝ) (hT : e.1.time < T) (R : ℝ) (hRT : R ≤ T)
    (f : exitProbeSubmodule) (hs : tsupport f.1 ⊆ {x | timeCoord 1 x < R}) :
    (∫ p, forwardScalarOperator A.a (exitProbePhysical f) p
      ∂stripGreen hH hLE hlam hLam A H T (stripPoleFinite H e T hT)) =
    ∫ p, forwardScalarOperator A.a (exitProbePhysical f) p
      ∂stripGreen hH hLE hlam hLam A H ⊤ e := by
  rw [stripGreen_finite_restrict_infinite]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp =>
    infinite_probe_operator_zero_after A f R hs p (hRT.trans (not_lt.mp hp)))

/-- Finite exit measures have the same compact probe integrals before both horizons. -/
theorem infinite_exit_probe_consistency
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (e : StripPole H ⊤)
    (T1 T2 : ℝ) (hT1 : e.1.time < T1) (hT2 : e.1.time < T2)
    (R : ℝ) (hR1 : R ≤ T1) (hR2 : R ≤ T2)
    (f : exitProbeSubmodule) (hs : tsupport f.1 ⊆ {x | timeCoord 1 x < R}) :
    (∫ p, exitProbePhysical f p
      ∂stripExit hH hLE hlam hLam A H T1 (stripPoleFinite H e T1 hT1)) =
    ∫ p, exitProbePhysical f p
      ∂stripExit hH hLE hlam hLam A H T2 (stripPoleFinite H e T2 hT2) := by
  have hi (T : ℝ) (ht : e.1.time < T) :
      (∫ p, exitProbePhysical f p
        ∂stripExit hH hLE hlam hLam A H T (stripPoleFinite H e T ht)) =
      exitProbePhysical f e.1 + ∫ p, forwardScalarOperator A.a (exitProbePhysical f) p
        ∂stripGreen hH hLE hlam hLam A H T (stripPoleFinite H e T ht) :=
    stripExitOfRealization_probe_integral hH hlam hLam A H _
      (stripEvolution_spec hH hLE hlam hLam A H) T (stripPoleFinite H e T ht) f
  rw [hi T1 hT1, hi T2 hT2,
    infinite_probe_source_integral hH hLE hlam hLam A H e T1 hT1 R hR1 f hs,
    infinite_probe_source_integral hH hLE hlam hLam A H e T2 hT2 R hR2 f hs]

/-- Equality of early probe integrals gives exact equality of the restricted physical exits. -/
theorem stripExit_horizon_consistency
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (e : StripPole H ⊤)
    (T1 T2 : ℝ) (hT1 : e.1.time < T1) (hT2 : e.1.time < T2)
    (R : ℝ) (hR1 : R ≤ T1) (hR2 : R ≤ T2) :
    (stripExit hH hLE hlam hLam A H T1 (stripPoleFinite H e T1 hT1)).restrict
      {p | p.time < R} =
    (stripExit hH hLE hlam hLam A H T2 (stripPoleFinite H e T2 hT2)).restrict
      {p | p.time < R} := by
  let Ω (T : ℝ) (ht : e.1.time < T) :=
    stripExit hH hLE hlam hLam A H T (stripPoleFinite H e T ht)
  let U : Set (EvolutionVec 1) := {x | timeCoord 1 x < R}
  have hU : IsOpen U := isOpen_lt (timeCoord 1).continuous continuous_const
  let ν (T : ℝ) (ht : e.1.time < T) :=
    ((Ω T ht).map reconstructionPhysicalHomeomorph.symm).restrict U
  have hν (T : ℝ) (ht : e.1.time < T) : IsFiniteMeasure (ν T ht) := by
    dsimp only [ν, Ω]
    infer_instance
  let (T : ℝ) (ht : e.1.time < T) : IsFiniteMeasure (ν T ht) := hν T ht
  have hin (T : ℝ) (ht : e.1.time < T) (f : exitProbeSubmodule)
      (hs : tsupport f.1 ⊆ U) :
      (∫ x, f.1 x ∂ν T ht) = ∫ p, exitProbePhysical f p ∂Ω T ht := by
    dsimp only [ν]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))),
      integral_map reconstructionPhysicalHomeomorph.symm.continuous.measurable.aemeasurable
        f.2.1.continuous.measurable.aestronglyMeasurable]
    rfl
  have htest (f : EvolutionVec 1 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
      (hc : HasCompactSupport f) (hs : tsupport f ⊆ U) :
      (∫ x, f x ∂ν T1 hT1) = ∫ x, f x ∂ν T2 hT2 := by
    let F : exitProbeSubmodule := ⟨f, hf, hc⟩
    rw [hin T1 hT1 F hs, hin T2 hT2 F hs]
    exact infinite_exit_probe_consistency hH hLE hlam hLam A H e
      T1 T2 hT1 hT2 R hR1 hR2 F hs
  have heq : ν T1 hT1 = ν T2 hT2 := by
    apply le_antisymm
    · apply measure_le_of_smooth_integral_le hU
        (by simp only [ν, Measure.restrict_restrict hU.measurableSet, inter_self])
      intro f hf hc hs _
      exact (htest f hf hc hs).le
    · apply measure_le_of_smooth_integral_le hU
        (by simp only [ν, Measure.restrict_restrict hU.measurableSet, inter_self])
      intro f hf hc hs _
      exact (htest f hf hc hs).symm.le
  have hmap (T : ℝ) (ht : e.1.time < T) :
      (ν T ht).map reconstructionPhysicalHomeomorph = (Ω T ht).restrict {p | p.time < R} := by
    dsimp only [ν]
    rw [Measure.restrict_map reconstructionPhysicalHomeomorph.symm.continuous.measurable
      hU.measurableSet, Measure.map_map reconstructionPhysicalHomeomorph.continuous.measurable
        reconstructionPhysicalHomeomorph.symm.continuous.measurable]
    have hid : reconstructionPhysicalHomeomorph ∘ reconstructionPhysicalHomeomorph.symm =
        (id : Point → Point) := funext reconstructionPhysicalHomeomorph.apply_symm_apply
    rw [hid, Measure.map_id]
    rfl
  have hh := congrArg (fun μ : Measure (EvolutionVec 1) =>
    μ.map reconstructionPhysicalHomeomorph) heq
  rw [hmap T1 hT1, hmap T2 hT2] at hh
  exact hh

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
