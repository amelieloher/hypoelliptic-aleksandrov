module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SurvivalKernel
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripMassInfinite
import Mathlib.Tactic

/-! # Occupation controls the remaining killed mass

Source: companion paper, Corollary 8.4. The estimate is derived by integrating the actual
nonincreasing remaining mass; no survival or restart estimate is assumed.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo
open scoped ENNReal

/-- Green occupation over a finite interval dominates its length times the final mass. -/
theorem stripSurvivingMass_mul_time_le_green {lam Lam : ℝ}
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ)) :
    ENNReal.ofReal (T - e.1.time) *
      ENNReal.ofReal (stripSurvivingMass H E e.1.time T
        (WithTop.coe_lt_coe.mp e.2.1).le (stripPoleState H T e)) ≤
      stripGreenOfKernel H E.2 T e univ := by
  let dt := T - e.1.time
  have hdt : 0 < dt := sub_pos.mpr (WithTop.coe_lt_coe.mp e.2.1)
  let z := stripPoleState H T e
  let m := stripSurvivingMass H E e.1.time T (WithTop.coe_lt_coe.mp e.2.1).le z
  have hact := stripGreenOfKernel_spec H E.2 T e (fun _ => 1) measurable_const
  simp only [lintegral_one] at hact
  change stripGreenOfKernel H E.2 T e univ =
    ∫⁻ tau, E.2.master (elapsedQuery e.1.time z tau) univ
      ∂elapsedVolume (ENNReal.ofReal dt) at hact
  rw [hact]
  have hc : ENNReal.ofReal dt * ENNReal.ofReal m =
      ∫⁻ _tau : ElapsedTime (ENNReal.ofReal dt), ENNReal.ofReal m
        ∂elapsedVolume (ENNReal.ofReal dt) := by
    rw [lintegral_const, elapsedVolume_univ dt hdt, mul_comm]
  change ENNReal.ofReal dt * ENNReal.ofReal m ≤ _
  rw [hc]
  apply lintegral_mono
  intro tau
  have htau : tau.1 < dt := (ENNReal.ofReal_lt_ofReal_iff hdt).mp tau.2.2
  have hst : e.1.time ≤ e.1.time + tau.1 := le_add_of_nonneg_right tau.2.1.le
  have htu : e.1.time + tau.1 ≤ T := by dsimp [dt] at htau; linarith
  have hm := stripSurvivingMass_antitone A H E hE e.1.time
    (e.1.time + tau.1) T hst htu z
  have hmap := E.2.map_fiberKernel_eq_master (intervalDomain_measurable H)
    e.1.time (e.1.time + tau.1) hst z
  have hun := congrArg (fun mu => mu univ) hmap
  rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ, preimage_univ] at hun
  have hmass := stripSurvivingMass_eq_kernel_mass A H E hE e.1.time
    (e.1.time + tau.1) hst z
  apply (ENNReal.ofReal_le_ofReal hm).trans
  rw [hmass, ENNReal.ofReal_toReal
    ((E.2.fiberKernel_mass_le_one (intervalDomain_measurable H)
      e.1.time (e.1.time + tau.1) hst z).trans_lt ENNReal.one_lt_top).ne]
  exact hun.le

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
