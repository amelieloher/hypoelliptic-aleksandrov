module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisits
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PoleDensity
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SurvivalHalfMass
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.MixtureDensityRadonNikodym

/-! # Finite mixtures of the actual all-time active Green family

Source: companion paper, Corollary 8.4 (mixture density). This module proves finite mass,
absolute continuity and density existence. The quantitative Lq norm estimate is
a separate step, not a premise or a conclusion of these measure lemmas.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory
open scoped ENNReal

/-- The all-time active Green kernel is uniformly finite by the quadratic occupation bound. -/
theorem mixtureActiveGreenKernel_isFiniteKernel
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) :
    IsFiniteKernel (enlargedActiveGreenKernel hH hLE hlam hLam A c) := by
  classical
  refine ⟨ENNReal.ofReal (activeHalfMassTime lam c / 2), ENNReal.ofReal_lt_top, ?_⟩
  intro e
  change (if he : e.velocity 0 ∈ c.active then
    stripGreen hH hLE hlam hLam A c.activeInterval ⊤ (densityClockPole c e he)
      else 0) univ ≤ _
  split
  · rename_i he
    exact (stripGreen_quadratic_mass hH hLE hlam hLam A c.activeInterval ⊤
      (densityClockPole c e he)).trans
        (ENNReal.ofReal_le_ofReal (active_quadratic_occupation_le hlam c (e.velocity 0)))
  · exact zero_le

/-- A finite starting measure gives a finite all-time Green mixture. -/
theorem enlargedActiveGreen_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (nu : Measure Point) [IsFiniteMeasure nu] :
    IsFiniteMeasure (enlargedActiveGreen hH hLE hlam hLam A c nu) := by
  unfold enlargedActiveGreen
  have := mixtureActiveGreenKernel_isFiniteKernel hH hLE hlam hLam A c
  infer_instance

/-- Every actual pole Green measure is absolutely continuous with respect to active volume. -/
theorem mixtureActiveGreenKernel_absolutelyContinuous
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) :
    enlargedActiveGreenKernel hH hLE hlam hLam A c e ≪
      volume.restrict {p : Point | p.velocity 0 ∈ c.active} := by
  classical
  by_cases he : e.velocity 0 ∈ c.active
  · obtain ⟨_, _, hd⟩ := one_sign_pole_density hH hLE hlam hLam (6 / 5)
      (by norm_num) (by norm_num)
    obtain ⟨g, _, _, hgd, _, hgs⟩ := hd A c e he
    change stripGreen hH hLE hlam hLam A c.activeInterval ⊤
      (densityClockPole c e he) = volume.withDensity (fun p => ENNReal.ofReal (g p)) at hgd
    have hD : MeasurableSet {p : Point | p.velocity 0 ∈ c.active} :=
      isOpen_Ioo.measurableSet.preimage
        ((continuous_apply 0).comp continuous_velocity).measurable
    have hs : ∀ᵐ p ∂stripGreen hH hLE hlam hLam A c.activeInterval ⊤
        (densityClockPole c e he), p.velocity 0 ∈ c.active := hgs.mono (fun _ h => h.2)
    have hrestrict := Measure.restrict_eq_self_of_ae_mem hs
    change (if hv : e.velocity 0 ∈ c.active then
      stripGreen hH hLE hlam hLam A c.activeInterval ⊤ (densityClockPole c e hv)
        else 0) ≪ _
    rw [dite_eq_left he]
    have heq : stripGreen hH hLE hlam hLam A c.activeInterval ⊤
        (densityClockPole c e he) =
          (volume.restrict {p : Point | p.velocity 0 ∈ c.active}).withDensity
            (fun p => ENNReal.ofReal (g p)) :=
      hrestrict.symm.trans ((congrArg (fun mu : Measure Point =>
        mu.restrict {p : Point | p.velocity 0 ∈ c.active}) hgd).trans
          (restrict_withDensity hD _))
    exact heq.symm ▸ withDensity_absolutelyContinuous _ _
  · change (if hv : e.velocity 0 ∈ c.active then
      stripGreen hH hLE hlam hLam A c.activeInterval ⊤ (densityClockPole c e hv)
        else 0) ≪ _
    rw [dite_eq_right he]
    exact Measure.AbsolutelyContinuous.zero _

/-- Integrating the actual Borel pole family preserves absolute continuity on the active strip. -/
theorem enlargedActiveGreen_absolutelyContinuous
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (nu : Measure Point) :
    enlargedActiveGreen hH hLE hlam hLam A c nu ≪
      volume.restrict {p : Point | p.velocity 0 ∈ c.active} := by
  let K := enlargedActiveGreenKernel hH hLE hlam hLam A c
  change K ∘ₘ nu ≪ _
  apply Measure.AbsolutelyContinuous.mk
  intro B hB hnull
  rw [Measure.bind_apply hB K.aemeasurable]
  have hz : ∀ e, K e B = 0 :=
    fun e => mixtureActiveGreenKernel_absolutelyContinuous hH hLE hlam hLam A c e hnull
  simp only [hz, lintegral_zero]

/-- The mixture has a measurable nonnegative real density on the actual all-time active strip. -/
theorem enlargedActiveGreen_has_density
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (nu : Measure Point) [IsFiniteMeasure nu] :
    ∃ g : Point → ℝ, Measurable g ∧ (∀ p, 0 ≤ g p) ∧
      enlargedActiveGreen hH hLE hlam hLam A c nu =
        (volume.restrict {p : Point | p.velocity 0 ∈ c.active}).withDensity
          (fun p => ENNReal.ofReal (g p)) := by
  have : SigmaFinite (volume : Measure Point) := by
    change SigmaFinite (Measure.map (KineticPoint.equivProd 1).symm volume)
    exact (KineticPoint.homeomorphProd 1).symm.measurableEmbedding.sigmaFinite_map
  let mu := enlargedActiveGreen hH hLE hlam hLam A c nu
  have : IsFiniteMeasure mu := enlargedActiveGreen_isFiniteMeasure hH hLE hlam hLam A c nu
  let m : Measure Point := volume.restrict {p : Point | p.velocity 0 ∈ c.active}
  have : SigmaFinite m := inferInstance
  have hac : mu ≪ m := enlargedActiveGreen_absolutelyContinuous hH hLE hlam hLam A c nu
  exact mixture_real_density_of_absolutelyContinuous mu m hac

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
