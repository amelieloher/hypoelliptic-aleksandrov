module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonRestriction
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.JointQueryBorelDense

/-! # Borel dependence of the unique infinite-horizon exit family -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo TheoremA Evolution
open scoped CompactlySupported ENNReal

/-- Bounded Borel sources have measurable potentials for the actual infinite Green family. -/
theorem infinite_green_potential_measurable
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (g : BoundedBorel Point) :
    Measurable (fun e : StripPole H ⊤ => ∫ p, g p ∂stripGreen hH hLE hlam hLam A H ⊤ e) := by
  have hΓ : Measurable (stripGreen hH hLE hlam hLam A H ⊤) :=
    Measure.measurable_measure.mpr (stripGreen_measurable_apply hH hLE hlam hLam A H ⊤)
  have hp := (Measure.measurable_lintegral g.measurable.ennreal_ofReal).comp hΓ
  have hn := (Measure.measurable_lintegral g.measurable.neg.ennreal_ofReal).comp hΓ
  have heq : (fun e : StripPole H ⊤ => ∫ p, g p ∂stripGreen hH hLE hlam hLam A H ⊤ e) =
      fun e => (∫⁻ p, ENNReal.ofReal (g p) ∂stripGreen hH hLE hlam hLam A H ⊤ e).toReal -
        (∫⁻ p, ENNReal.ofReal (-g p) ∂stripGreen hH hLE hlam hLam A H ⊤ e).toReal := by
    funext e
    exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part
      (stripGreen_integrable hH hLE hlam hLam A H ⊤ e g)
  rw [heq]
  exact hp.ennreal_toReal.sub hn.ennreal_toReal

/-- Infinite probe values depend measurably on the physical pole. -/
theorem infiniteExitProbeValue_measurable
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (f : exitProbeSubmodule) :
    Measurable (fun e : StripPole H ⊤ => infiniteExitProbeValue hH hLE hlam hLam A H e f) :=
  ((exitProbePhysical_continuous_compact f).1.measurable.comp measurable_subtype_coe).add
    (infinite_green_potential_measurable hH hLE hlam hLam A H (exitProbeOperatorDatum A f))

/-- The unique physical exit family is a Borel measure family. -/
theorem stripInfiniteExit_measurable
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) :
    Measurable (fun e : StripPole H ⊤ =>
      stripInfiniteExit hH hLE hlam hLam A H e) := by
  let Ω := stripInfiniteExit hH hLE hlam hLam A H
  let ν (e : StripPole H ⊤) : Measure (EvolutionVec 1) :=
    (Ω e).map reconstructionPhysicalHomeomorph.symm
  have hν : ∀ e, IsFiniteMeasure (ν e) := fun e => by dsimp [ν, Ω]; infer_instance
  let (e : StripPole H ⊤) : IsFiniteMeasure (ν e) := hν e
  have hm (e : StripPole H ⊤) : ν e univ ≤ 1 := by
    dsimp only [ν]
    rw [Measure.map_apply reconstructionPhysicalHomeomorph.symm.continuous.measurable
      MeasurableSet.univ, preimage_univ]
    exact stripInfiniteExit_mass_le_one hH hLE hlam hLam A H e
  have htest (f : C_c(EvolutionVec 1, ℝ)) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
      Measurable (fun e => ∫ x, f x ∂ν e) := by
    let F : exitProbeSubmodule := ⟨f, hf, f.hasCompactSupport⟩
    have heq : (fun e => ∫ x, f x ∂ν e) = fun e => infiniteExitProbeValue hH hLE hlam hLam A H e
      F := by
      funext e
      dsimp only [ν]
      rw [integral_map reconstructionPhysicalHomeomorph.symm.continuous.measurable.aemeasurable
        (show AEStronglyMeasurable (fun x => f x) _ from
          f.continuous.measurable.aestronglyMeasurable)]
      exact stripInfiniteExit_probe_integral hH hLE hlam hLam A H e F
    rw [heq]
    exact infiniteExitProbeValue_measurable hH hLE hlam hLam A H F
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
theorem stripInfiniteExit_measurable_apply
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (B : Set Point) (hB : MeasurableSet B) :
    Measurable (fun e : StripPole H ⊤ =>
      stripInfiniteExit hH hLE hlam hLam A H e B) :=
  (Measure.measurable_measure.mp (stripInfiniteExit_measurable hH hLE hlam hLam A H)) B hB

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
