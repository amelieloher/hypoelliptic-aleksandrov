module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TailRestartMeasure
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TailRestartTime
import Mathlib.Probability.Kernel.Composition.Comp

/-! # Restart of the actual physical transition action -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov SectionTwo ProbabilityTheory
open scoped ENNReal

/-- Killed-kernel composition restarts every measurable nonnegative physical terminal test. -/
theorem tailRestart_master_lintegral {lam Lam : ℝ}
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (s r u : ℝ) (hsr : s ≤ r) (hru : r ≤ u)
    (z : EvolutionState (intervalDomain H) (fun _ => 0) s)
    (F : Point → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ w, F ⟨u, w.2, w.1⟩ ∂E.2.master ⟨(s, u, z.1), hsr.trans hru, z.2⟩) =
      ∫⁻ a, ∫⁻ w, F ⟨u, w.2, w.1⟩
        ∂E.2.master ⟨(r, u, a.1), hru, a.2⟩
        ∂E.2.fiberKernel (intervalDomain_measurable H) s r hsr z := by
  have hG : Measurable (fun w : EvolutionAmbientState 1 => F ⟨u, w.2, w.1⟩) :=
    hF.comp ((KineticPoint.measurable_equivProd_symm 1).comp
      (measurable_const.prodMk (measurable_snd.prodMk measurable_fst)))
  have hmap := E.2.map_fiberKernel_eq_master (intervalDomain_measurable H)
    s u (hsr.trans hru) z
  change (∫⁻ w, F ⟨u, w.2, w.1⟩ ∂E.2.master
    (evolutionQueryOfState (intervalDomain H) (fun _ => 0) s u (hsr.trans hru) z)) = _
  rw [← hmap, lintegral_map hG measurable_subtype_coe,
    hE.2.2.2 s r u hsr hru]
  refine (Kernel.lintegral_comp _ _ z
    (g := fun a : EvolutionState (intervalDomain H) (fun _ => 0) u =>
      F ⟨u, a.1.2, a.1.1⟩)
    (hG.comp measurable_subtype_coe)).trans ?_
  apply lintegral_congr
  intro a
  have hm := E.2.map_fiberKernel_eq_master (intervalDomain_measurable H) r u hru a
  change _ = (∫⁻ w, F ⟨u, w.2, w.1⟩ ∂E.2.master
    (evolutionQueryOfState (intervalDomain H) (fun _ => 0) r u hru a))
  rw [← hm, lintegral_map hG measurable_subtype_coe]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
