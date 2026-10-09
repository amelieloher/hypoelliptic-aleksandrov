module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TailRestartKernel
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripGreenBorel
import Mathlib.MeasureTheory.Measure.Prod

/-! # Native-state Green restart action -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov SectionTwo ProbabilityTheory
open scoped ENNReal

/-- Restore a native state as a valid infinite-horizon pole. -/
def tailRestartPole (H : Interval) (r : ℝ)
    (a : EvolutionState (intervalDomain H) (fun _ => 0) r) : StripPole H ⊤ :=
  ⟨activeRestartPoint H r a, WithTop.coe_lt_top _, by
    have ha := PDE.mem_translateSet_iff_sub_mem.mp a.2.1
    simpa only [activeRestartPoint, sub_zero, intervalDomain,
      PDE.mem_oneDimensionalAxisBox_iff, PDE.vecOneCoordinate, Interval.carrier] using ha⟩

/-- The physical restarted pole is Borel in its native state. -/
theorem measurable_tailRestartPole (H : Interval) (r : ℝ) :
    Measurable (tailRestartPole H r) :=
  (measurable_activeRestartPoint H r).subtype_mk

/-- Native terminal states recover their unchanged coordinates as physical poles. -/
theorem tailRestartPole_state (H : Interval) (r : ℝ)
    (a : EvolutionState (intervalDomain H) (fun _ => 0) r) :
    stripPoleState H ⊤ (tailRestartPole H r a) = a := by
  apply Subtype.ext
  rfl

/-- The restarted master query is jointly measurable in elapsed time and state. -/
def tailRestartQuery (H : Interval) (r : ℝ)
    (q : ElapsedTime ⊤ × EvolutionState (intervalDomain H) (fun _ => 0) r) :
    EvolutionQuery (intervalDomain H) (fun _ => 0) :=
  ⟨(r, r + q.1.1, q.2.1), le_add_of_nonneg_right q.1.2.1.le, q.2.2⟩

/-- The jointly varying restart query uses the already fixed Borel master kernel. -/
theorem measurable_tailRestartQuery (H : Interval) (r : ℝ) :
    Measurable (tailRestartQuery H r) := by
  apply Measurable.subtype_mk
  exact measurable_const.prodMk
    ((measurable_const.add (measurable_subtype_coe.comp measurable_fst)).prodMk
      (measurable_subtype_coe.comp measurable_snd))

/-- Fubini for the actual restarted master action requires no selected density family. -/
theorem tailRestart_action_swap (H : Interval)
    (K : MovingFiberKernel (intervalDomain H) (fun _ => 0)) (r : ℝ)
    (nu : Measure (EvolutionState (intervalDomain H) (fun _ => 0) r))
    [IsFiniteMeasure nu] (F : Point → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ tau, ∫⁻ a, ∫⁻ w, F ⟨r + tau.1, w.2, w.1⟩
      ∂K.master (tailRestartQuery H r (tau, a)) ∂nu ∂elapsedVolume ⊤) =
      ∫⁻ a, ∫⁻ p, F p ∂stripGreenOfKernel H K ⊤ (tailRestartPole H r a) ∂nu := by
  let k := K.master.comap (tailRestartQuery H r) (measurable_tailRestartQuery H r)
  have : IsFiniteKernel k := by dsimp [k]; infer_instance
  have hm : Measurable (fun q :
      (ElapsedTime ⊤ × EvolutionState (intervalDomain H) (fun _ => 0) r) ×
        EvolutionAmbientState 1 => F ⟨r + q.1.1.1, q.2.2, q.2.1⟩) :=
    hF.comp ((KineticPoint.measurable_equivProd_symm 1).comp
      ((measurable_const.add
        (measurable_subtype_coe.comp measurable_fst.fst)).prodMk
        (measurable_snd.snd.prodMk measurable_snd.fst)))
  have hi := hm.lintegral_kernel_prod_right' (κ := k)
  rw [lintegral_lintegral_swap hi.aemeasurable]
  apply lintegral_congr
  intro a
  rw [stripGreenOfKernel_spec H K ⊤ (tailRestartPole H r a) F hF,
    tailRestartPole_state]
  rfl

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
