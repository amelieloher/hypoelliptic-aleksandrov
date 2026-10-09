module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.Survival
import Mathlib.Tactic

/-! # The actual remaining terminal measure for a tail restart

Source: companion paper, Corollary 8.4 (restarted tail). The measure is placed on
the absolute restart-time slice and retains every interior active velocity.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo

/-- Put a native terminal state on its physical absolute-time slice. -/
def activeRestartPoint (H : Interval) (s : ℝ)
    (w : EvolutionState (intervalDomain H) (fun _ => 0) s) : Point :=
  ⟨s, w.1.2, w.1.1⟩

/-- Restoring physical coordinates on a fixed time slice is measurable. -/
theorem measurable_activeRestartPoint (H : Interval) (s : ℝ) :
    Measurable (activeRestartPoint H s) := by
  exact (KineticPoint.measurable_equivProd_symm 1).comp
    (measurable_const.prodMk
      ((measurable_snd.comp measurable_subtype_coe).prodMk
        (measurable_fst.comp measurable_subtype_coe)))

/-- The surviving terminal measure, restored to the source's physical spacetime coordinates. -/
def activeRestartMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point)
    (he : e.velocity 0 ∈ c.active) (t : ℝ) (ht : 0 ≤ t) : Measure Point :=
  ((stripEvolution hH hLE hlam hLam A c.activeInterval).2.fiberKernel
    (intervalDomain_measurable c.activeInterval) e.time (e.time + t)
    (le_add_of_nonneg_right ht)
    (stripPoleState c.activeInterval ⊤ ⟨e, WithTop.coe_lt_top _, he⟩)).map
      (activeRestartPoint c.activeInterval (e.time + t))

/-- The mass of the remaining terminal measure is exactly the surviving killed mass. -/
theorem activeRestartMeasure_mass
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point)
    (he : e.velocity 0 ∈ c.active) (t : ℝ) (ht : 0 ≤ t) :
    activeRestartMeasure hH hLE hlam hLam A c e he t ht univ =
      ENNReal.ofReal (activeSurvivingMass hH hLE hlam hLam A c e he t ht) := by
  let E := stripEvolution hH hLE hlam hLam A c.activeInterval
  let z := stripPoleState c.activeInterval ⊤ ⟨e, WithTop.coe_lt_top _, he⟩
  have hmass := stripSurvivingMass_eq_kernel_mass A c.activeInterval E
    (stripEvolution_spec hH hLE hlam hLam A c.activeInterval)
    e.time (e.time + t) (le_add_of_nonneg_right ht) z
  change (Measure.map (activeRestartPoint c.activeInterval (e.time + t))
    (E.2.fiberKernel (intervalDomain_measurable c.activeInterval)
      e.time (e.time + t) (le_add_of_nonneg_right ht) z)) univ =
    ENNReal.ofReal (stripSurvivingMass c.activeInterval E
      e.time (e.time + t) (le_add_of_nonneg_right ht) z)
  rw [Measure.map_apply (measurable_activeRestartPoint _ _) MeasurableSet.univ,
    preimage_univ, hmass]
  exact (ENNReal.ofReal_toReal
    ((E.2.fiberKernel_mass_le_one (intervalDomain_measurable c.activeInterval)
      e.time (e.time + t) (le_add_of_nonneg_right ht) z).trans_lt
        ENNReal.one_lt_top).ne).symm

/-- All remaining terminal mass lies on the restart-time slice inside the whole active interval. -/
theorem activeRestartMeasure_ae_time_active
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point)
    (he : e.velocity 0 ∈ c.active) (t : ℝ) (ht : 0 ≤ t) :
    ∀ᵐ p ∂activeRestartMeasure hH hLE hlam hLam A c e he t ht,
      p.time = e.time + t ∧ p.velocity 0 ∈ c.active := by
  have hm : MeasurableSet {p : Point | p.time = e.time + t ∧
      p.velocity 0 ∈ c.active} :=
    (isClosed_eq continuous_time continuous_const).measurableSet.inter
      (isOpen_Ioo.measurableSet.preimage
        ((continuous_apply 0).comp continuous_velocity).measurable)
  change ∀ᵐ p ∂Measure.map (activeRestartPoint c.activeInterval (e.time + t)) _, _
  apply (ae_map_iff (measurable_activeRestartPoint _ _).aemeasurable hm).mpr
  apply Filter.Eventually.of_forall
  intro w
  refine ⟨rfl, ?_⟩
  have hw := PDE.mem_translateSet_iff_sub_mem.mp w.2.1
  simpa only [activeRestartPoint, sub_zero, intervalDomain,
    PDE.mem_oneDimensionalAxisBox_iff, PDE.vecOneCoordinate,
    Clock.activeInterval, Clock.active] using hw

/-- Remaining terminal mass obeys the source uniform exponential decay. -/
theorem activeRestartMeasure_mass_exp
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ C c₀ : ℝ, 0 < C ∧ 0 < c₀ ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock)
      (e : Point) (he : e.velocity 0 ∈ c.active) (t : ℝ) (ht : 0 ≤ t),
      activeRestartMeasure hH hLE hlam hLam A c e he t ht univ ≤
        ENNReal.ofReal (C * Real.exp (-c₀ * t / c.r ^ 2)) := by
  obtain ⟨C, c₀, hC, hc₀, hb⟩ := active_survival_exp hH hLE hlam hLam
  refine ⟨C, c₀, hC, hc₀, ?_⟩
  intro A c e he t ht
  rw [activeRestartMeasure_mass]
  exact ENNReal.ofReal_le_ofReal (hb A c e he t ht)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
