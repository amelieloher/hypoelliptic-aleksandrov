module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitMeasureCanonical
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.DomainDominationMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Exit times cannot precede the pole time -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo TheoremA Evolution

/-- Every derivative term in the packed operator vanishes outside the test's support. -/
theorem reconstruction_operator_zero_off_tsupport
    (B : FullKineticCoefficient 1) (b : PDE.Vec 1 → PDE.Vec 1)
    (f : EvolutionVec 1 → ℝ) (x : EvolutionVec 1) (hx : x ∉ tsupport f) :
    transportedOperator B b f x = 0 := by
  have hd := fderiv_of_notMem_tsupport (𝕜 := ℝ) hx
  have hh (j : Fin 1) :
      fderiv ℝ (fun y => fderiv ℝ f y (basisV j)) x = 0 :=
    fderiv_of_notMem_tsupport (𝕜 := ℝ)
      (fun h => hx (tsupport_fderiv_apply_subset ℝ (basisV j) h))
  simp only [transportedOperator, hd, hh, zero_apply,
    mul_zero, Finset.sum_const_zero, add_zero]

/-- The actual unique exit measure charges no point strictly before its pole. -/
theorem stripExitOfRealization_before_pole
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ)) :
    stripExitOfRealization hH hlam hLam A H E hE T e {p | p.time < e.1.time} = 0 := by
  let Ω := stripExitOfRealization hH hlam hLam A H E hE T e
  let ν : Measure (EvolutionVec 1) := Ω.map reconstructionPhysicalHomeomorph.symm
  let U : Set (EvolutionVec 1) := {x | timeCoord 1 x < e.1.time}
  have hU : IsOpen U := isOpen_lt (timeCoord 1).continuous continuous_const
  have hle : ν.restrict U ≤ 0 := by
    apply measure_le_of_smooth_integral_le hU (by rw [Measure.restrict_restrict
      hU.measurableSet, inter_self])
    intro f hf hc hs _
    let F : exitProbeSubmodule := ⟨f, hf, hc⟩
    have he : f (reconstructionPhysicalHomeomorph.symm e.1) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hx
      have ht := hs hx
      change e.1.time < e.1.time at ht
      exact lt_irrefl _ ht
    have hg : (fun p => forwardScalarOperator A.a (exitProbePhysical F) p) =ᵐ[
        stripGreenOfKernel H E.2 T e] 0 := by
      filter_upwards [reconstruction_green_ae_time_gt H E.2 T e] with p hp
      rw [exitProbePhysical_operator]
      apply reconstruction_operator_zero_off_tsupport
      intro hx
      have ht := hs hx
      change p.time < e.1.time at ht
      exact (not_lt_of_ge hp.le) ht
    have hi := stripExitOfRealization_probe_integral hH hlam hLam A H E hE T e F
    have hz : exitProbeValue A H E T e F = 0 := by
      change f (reconstructionPhysicalHomeomorph.symm e.1) +
        (∫ p, forwardScalarOperator A.a (exitProbePhysical F) p
          ∂stripGreenOfKernel H E.2 T e) = 0
      rw [he, integral_congr_ae hg]
      simp only [Pi.zero_apply, integral_zero, zero_add]
    have hm : (∫ x, f x ∂ν) = 0 := by
      dsimp only [ν]
      rw [integral_map reconstructionPhysicalHomeomorph.symm.continuous.measurable.aemeasurable
        hf.continuous.measurable.aestronglyMeasurable]
      exact hi.trans hz
    rw [integral_zero_measure,
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht))), hm]
  have hz : ν U = 0 := by
    have hh := Measure.le_iff.mp hle univ MeasurableSet.univ
    simpa using hh
  have hm : ν U = Ω {p | p.time < e.1.time} := by
    dsimp only [ν]
    rw [Measure.map_apply reconstructionPhysicalHomeomorph.symm.continuous.measurable
      hU.measurableSet]
    rfl
  exact hm.symm.trans hz

/-- Almost every actual exit point has future time and velocity in the closed interval. -/
theorem stripExitOfRealization_ae_closed_future
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ)) :
    ∀ᵐ p ∂stripExitOfRealization hH hlam hLam A H E hE T e,
      e.1.time ≤ p.time ∧ p.time ≤ T ∧ p.velocity 0 ∈ Icc H.lo H.hi := by
  have hb : ∀ᵐ p ∂stripExitOfRealization hH hlam hLam A H E hE T e,
      p ∈ stripClosedExit H T := by
    rw [ae_iff]
    exact stripExitOfRealization_compl_closedExit hH hlam hLam A H E hE T e
  have ht : ∀ᵐ p ∂stripExitOfRealization hH hlam hLam A H E hE T e,
      e.1.time ≤ p.time := by
    rw [ae_iff]
    simpa only [not_le] using
      stripExitOfRealization_before_pole hH hlam hLam A H E hE T e
  filter_upwards [hb, ht] with p hp ht
  refine ⟨ht, ?_⟩
  rcases hp with hp | hp
  · exact ⟨hp.1.le, hp.2⟩
  · refine ⟨hp.1, ?_⟩
    rcases hp.2 with hv | hv <;> rw [hv]
    · exact ⟨le_rfl, H.ordered.le⟩
    · exact ⟨H.ordered.le, le_rfl⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
