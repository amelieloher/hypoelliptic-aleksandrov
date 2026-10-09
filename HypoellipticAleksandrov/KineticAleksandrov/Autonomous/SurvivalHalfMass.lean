module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SurvivalOccupation
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockPushforwardCone
import Mathlib.Tactic

/-! # Uniform half-mass time for the actual active killed evolution

Source: companion paper, Corollary 8.4 (survival decay). The time is twice the uniform
quadratic occupation bound, independently of coefficient derivatives and poles.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo
open scoped ENNReal

/-- Twice the uniform quadratic occupation time of the clock's active interval. -/
def activeHalfMassTime (lam : ℝ) (c : Clock) : ℝ := 9 * c.r ^ 2 / (16 * lam)

/-- Positive ellipticity and radius give a strictly positive half-mass time. -/
theorem activeHalfMassTime_pos {lam : ℝ} (hlam : 0 < lam) (c : Clock) :
    0 < activeHalfMassTime lam c := by
  unfold activeHalfMassTime
  have hr := c.positive
  positivity

/-- Every active pole has the same uniform upper bound on quadratic occupation. -/
theorem active_quadratic_occupation_le {lam : ℝ} (hlam : 0 < lam) (c : Clock)
    (v : ℝ) :
    (v - c.activeInterval.lo) * (c.activeInterval.hi - v) / (2 * lam) ≤
      activeHalfMassTime lam c / 2 := by
  apply (div_le_iff₀ (by positivity : 0 < 2 * lam)).mpr
  have he : activeHalfMassTime lam c / 2 * (2 * lam) = 9 * c.r ^ 2 / 16 := by
    unfold activeHalfMassTime
    field_simp
  rw [he]
  change (v - (c.vbar - 3 * c.r / 4)) * (c.vbar + 3 * c.r / 4 - v) ≤ _
  nlinarith only [sq_nonneg (v - c.vbar)]

/-- The actual killed kernel has lost at least half its mass at this common elapsed time. -/
theorem active_survival_half_mass
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (s : ℝ)
    (z : EvolutionState (intervalDomain c.activeInterval) (fun _ => 0) s) :
    let D := activeHalfMassTime lam c
    stripSurvivingMass c.activeInterval (stripEvolution hH hLE hlam hLam A c.activeInterval)
      s (s + D) (le_add_of_nonneg_right (activeHalfMassTime_pos hlam c).le) z ≤ 1 / 2 := by
  let D := activeHalfMassTime lam c
  have hD : 0 < D := activeHalfMassTime_pos hlam c
  let E := stripEvolution hH hLE hlam hLam A c.activeInterval
  have hE := stripEvolution_spec hH hLE hlam hLam A c.activeInterval
  let p : Point := ⟨s, z.1.2, z.1.1⟩
  have hv : p.velocity 0 ∈ c.activeInterval.carrier := by
    have hh := z.2.1
    apply PDE.mem_translateSet_iff_sub_mem.mp at hh
    simpa only [p, sub_zero, intervalDomain, PDE.mem_oneDimensionalAxisBox_iff,
      PDE.vecOneCoordinate, Interval.carrier] using hh
  let e : StripPole c.activeInterval ((s + D : ℝ) : WithTop ℝ) :=
    ⟨p, WithTop.coe_lt_coe.mpr (lt_add_of_pos_right s hD), hv⟩
  have hz : stripPoleState c.activeInterval (s + D) e = z := Subtype.ext rfl
  have hlo := stripSurvivingMass_mul_time_le_green A c.activeInterval E hE (s + D) e
  have hhi := stripGreen_finite_quadratic_mass hH hLE hlam hLam A c.activeInterval
    (s + D) e
  have hb := hlo.trans (hhi.trans
    (ENNReal.ofReal_le_ofReal (active_quadratic_occupation_le hlam c (p.velocity 0))))
  change ENNReal.ofReal ((s + D) - s) *
      ENNReal.ofReal (stripSurvivingMass c.activeInterval E s (s + D) _
        (stripPoleState c.activeInterval (s + D) e)) ≤ ENNReal.ofReal (D / 2) at hb
  rw [hz, add_sub_cancel_left] at hb
  have hm := (stripSurvivingMass_bounds A c.activeInterval E hE s (s + D)
    (le_add_of_nonneg_right hD.le) z).1
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hD.le,
    ENNReal.toReal_ofReal hm, ENNReal.toReal_ofReal (by positivity)] at hr
  dsimp only
  nlinarith only [hr, hD]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
