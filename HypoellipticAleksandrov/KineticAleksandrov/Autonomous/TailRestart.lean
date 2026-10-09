module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TailRestartGreen
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.MixtureDensity
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripTimeMarginal

/-! # Physical restart identity for the actual active all-time Green family -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov SectionTwo ProbabilityTheory
open scoped ENNReal

/-- The strict one-pole tail is exactly the enlarged Green mixture of surviving terminal mass. -/
theorem active_tail_restart_identity_strict
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point)
    (he : e.velocity 0 ∈ c.active) (t : ℝ) (ht : 0 ≤ t) :
    (stripGreen hH hLE hlam hLam A c.activeInterval ⊤ (densityClockPole c e he)).restrict
      {p | e.time + t < p.time} =
        enlargedActiveGreen hH hLE hlam hLam A c
          (activeRestartMeasure hH hLE hlam hLam A c e he t ht) := by
  classical
  let H := c.activeInterval
  let E := stripEvolution hH hLE hlam hLam A H
  let ep := densityClockPole c e he
  let nu := E.2.fiberKernel (intervalDomain_measurable H) e.time (e.time + t)
    (le_add_of_nonneg_right ht) (stripPoleState H ⊤ ep)
  let K := enlargedActiveGreenKernel hH hLE hlam hLam A c
  have hh := tailRestart_green_identity A H E
    (stripEvolution_spec hH hLE hlam hLam A H) ep t ht
  change (stripGreenOfKernel H E.2 ⊤ ep).restrict {p | e.time + t < p.time} =
    nu.bind (fun a => stripGreenOfKernel H E.2 ⊤
      (tailRestartPole H (e.time + t) a)) at hh
  change (stripGreenOfKernel H E.2 ⊤ ep).restrict {p | e.time + t < p.time} =
    (nu.map (activeRestartPoint H (e.time + t))).bind K
  rw [nested_bind_map nu _ (measurable_activeRestartPoint H (e.time + t)) K K.measurable]
  refine hh.trans ?_
  congr 1
  funext a
  have ha : (activeRestartPoint H (e.time + t) a).velocity 0 ∈ c.active :=
    (tailRestartPole H (e.time + t) a).2.2
  change _ = (if hv : (activeRestartPoint H (e.time + t) a).velocity 0 ∈ c.active then
    stripGreen hH hLE hlam hLam A H ⊤
      (densityClockPole c (activeRestartPoint H (e.time + t) a) hv) else 0)
  split
  · rfl
  · rename_i hn
    exact (hn ha).elim

/-- A one-pole Green measure assigns zero mass to each exact physical time slice. -/
theorem active_green_time_slice_null
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point)
    (he : e.velocity 0 ∈ c.active) (s : ℝ) :
    stripGreen hH hLE hlam hLam A c.activeInterval ⊤ (densityClockPole c e he)
      {p | p.time = s} = 0 := by
  have hh := stripGreen_timeMarginal hH hLE hlam hLam A c.activeInterval ⊤
    (densityClockPole c e he) {s} (measurableSet_singleton s)
  simpa only [mem_singleton_iff, Real.volume_singleton, nonpos_iff_eq_zero] using hh

/-- Including the restart-time endpoint does not change the Green restart identity. -/
theorem active_tail_restart_identity
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point)
    (he : e.velocity 0 ∈ c.active) (t : ℝ) (ht : 0 ≤ t) :
    (stripGreen hH hLE hlam hLam A c.activeInterval ⊤ (densityClockPole c e he)).restrict
      {p | e.time + t ≤ p.time} =
        enlargedActiveGreen hH hLE hlam hLam A c
          (activeRestartMeasure hH hLE hlam hLam A c e he t ht) := by
  rw [← active_tail_restart_identity_strict hH hLE hlam hLam A c e he t ht]
  apply Measure.restrict_congr_set
  have hn : ∀ᵐ p ∂stripGreen hH hLE hlam hLam A c.activeInterval ⊤
      (densityClockPole c e he), p.time ≠ e.time + t := by
    rw [ae_iff]
    simpa only [not_not] using
      active_green_time_slice_null hH hLE hlam hLam A c e he (e.time + t)
  filter_upwards [hn] with p hp
  exact propext (le_iff_lt_or_eq.trans (or_iff_left hp.symm))

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
