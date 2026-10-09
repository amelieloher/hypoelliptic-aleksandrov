module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitMeasure
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripGreenBorel
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.JointQueryBorelDense
import Mathlib.MeasureTheory.Measure.GiryMonad

/-! # Borel pole dependence of the actual unique exit family -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo TheoremA Evolution
open scoped CompactlySupported ENNReal

/-- Fixed bounded Borel sources have Borel Green potentials as functions of the pole. -/
theorem reconstruction_green_potential_measurable (H : Interval)
    (K : MovingFiberKernel (intervalDomain H) (fun _ => 0)) (T : ℝ) (g : BoundedBorel Point) :
    Measurable (fun e : StripPole H (T : WithTop ℝ) => stripPotentialOfKernel H K T g e) := by
  have hΓ : Measurable (fun e : StripPole H (T : WithTop ℝ) => stripGreenOfKernel H K T e) :=
    Measure.measurable_measure.mpr (stripGreenOfKernel_measurable_apply H K T)
  have hp := (Measure.measurable_lintegral g.measurable.ennreal_ofReal).comp hΓ
  have hn := (Measure.measurable_lintegral g.measurable.neg.ennreal_ofReal).comp hΓ
  have heq : (fun e : StripPole H (T : WithTop ℝ) => stripPotentialOfKernel H K T g e) =
      fun e => (∫⁻ p, ENNReal.ofReal (g p) ∂stripGreenOfKernel H K T e).toReal -
        (∫⁻ p, ENNReal.ofReal (-g p) ∂stripGreenOfKernel H K T e).toReal := by
    funext e
    exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part
      (stripGreen_integrable_boundedBorel H K T e g)
  rw [heq]
  exact hp.ennreal_toReal.sub hn.ennreal_toReal

/-- The unique homogeneous value of any fixed smooth exit probe depends measurably on its pole. -/
theorem exitProbeValue_measurable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    (H : Interval) (E : StripEvolution H) (T : ℝ) (f : exitProbeSubmodule) :
    Measurable (fun e : StripPole H (T : WithTop ℝ) => exitProbeValue A H E T e f) :=
  ((exitProbePhysical_continuous_compact f).1.measurable.comp measurable_subtype_coe).add
    (reconstruction_green_potential_measurable H E.2 T (exitProbeOperatorDatum A f))

/-- The unique physical exit family is a Borel measure family. -/
theorem stripExitOfRealization_measurable
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) :
    Measurable (fun e : StripPole H (T : WithTop ℝ) =>
      stripExitOfRealization hH hlam hLam A H E hE T e) := by
  let Ω := stripExitOfRealization hH hlam hLam A H E hE T
  let ν (e : StripPole H (T : WithTop ℝ)) : Measure (EvolutionVec 1) :=
    (Ω e).map reconstructionPhysicalHomeomorph.symm
  have hν : ∀ e, IsFiniteMeasure (ν e) := fun e => by dsimp [ν, Ω]; infer_instance
  let (e : StripPole H (T : WithTop ℝ)) : IsFiniteMeasure (ν e) := hν e
  have hm (e : StripPole H (T : WithTop ℝ)) : ν e univ ≤ 1 := by
    dsimp only [ν]
    rw [Measure.map_apply reconstructionPhysicalHomeomorph.symm.continuous.measurable
      MeasurableSet.univ, preimage_univ]
    exact stripExitOfRealization_mass_le_one hH hlam hLam A H E hE T e
  have htest (f : C_c(EvolutionVec 1, ℝ)) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
      Measurable (fun e => ∫ x, f x ∂ν e) := by
    let F : exitProbeSubmodule := ⟨f, hf, f.hasCompactSupport⟩
    have heq : (fun e => ∫ x, f x ∂ν e) = fun e => exitProbeValue A H E T e F := by
      funext e
      dsimp only [ν]
      rw [integral_map reconstructionPhysicalHomeomorph.symm.continuous.measurable.aemeasurable
        (show AEStronglyMeasurable (fun x => f x) _ from
          f.continuous.measurable.aestronglyMeasurable)]
      exact stripExitOfRealization_probe_integral hH hlam hLam A H E hE T e F
    rw [heq]
    exact exitProbeValue_measurable A H E T F
  have hv := measurable_measure_family_of_smooth_tests ν hm htest
  have hh := (Measure.measurable_map reconstructionPhysicalHomeomorph
    reconstructionPhysicalHomeomorph.continuous.measurable).comp hv
  have heq : (fun e => (ν e).map reconstructionPhysicalHomeomorph) = Ω := by
    funext e
    dsimp only [ν]
    rw [Measure.map_map reconstructionPhysicalHomeomorph.continuous.measurable
      reconstructionPhysicalHomeomorph.symm.continuous.measurable]
    have hid : reconstructionPhysicalHomeomorph ∘ reconstructionPhysicalHomeomorph.symm =
        (id : Point → Point) := funext reconstructionPhysicalHomeomorph.apply_symm_apply
    rw [hid, Measure.map_id]
  change Measurable (fun e => (ν e).map reconstructionPhysicalHomeomorph) at hh
  rwa [heq] at hh

/-- Every measurable set has Borel exit mass as a function of the valid pole. -/
theorem stripExitOfRealization_measurable_apply
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (B : Set Point) (hB : MeasurableSet B) :
    Measurable (fun e : StripPole H (T : WithTop ℝ) =>
      stripExitOfRealization hH hlam hLam A H E hE T e B) :=
  (Measure.measurable_measure.mp (stripExitOfRealization_measurable hH hlam hLam A H E hE T)) B hB

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
