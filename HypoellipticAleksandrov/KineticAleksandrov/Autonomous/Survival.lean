module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SurvivalHalfMass
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SurvivalIteration
import Mathlib.Tactic

/-! # Exponential survival decay in the active velocity interval

Source: companion paper, Corollary 8.4 (survival decay). Constants precede coefficients,
clocks and poles. Only the evolution existence hypotheses remain.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo

/-- The literal remaining killed mass from an interior active pole at nonnegative elapsed time. -/
def activeSurvivingMass
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point)
    (he : e.velocity 0 ∈ c.active) (t : ℝ) (ht : 0 ≤ t) : ℝ :=
  stripSurvivingMass c.activeInterval (stripEvolution hH hLE hlam hLam A c.activeInterval)
    e.time (e.time + t) (le_add_of_nonneg_right ht)
    (stripPoleState c.activeInterval ⊤ ⟨e, WithTop.coe_lt_top _, he⟩)

/-- Uniform exponential decay of surviving killed mass, with constants depending only on
ellipticity and with every pole in the whole active interval allowed. -/
theorem active_survival_exp
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ C c₀ : ℝ, 0 < C ∧ 0 < c₀ ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock)
      (e : Point) (he : e.velocity 0 ∈ c.active) (t : ℝ) (ht : 0 ≤ t),
      activeSurvivingMass hH hLE hlam hLam A c e he t ht ≤
        C * Real.exp (-c₀ * t / c.r ^ 2) := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  refine ⟨2, 16 * lam * Real.log 2 / 9, by norm_num, by positivity, ?_⟩
  intro A c e he t ht
  let E := stripEvolution hH hLE hlam hLam A c.activeInterval
  have hE := stripEvolution_spec hH hLE hlam hLam A c.activeInterval
  have hb := stripSurvivingMass_exp_of_half_mass A c.activeInterval E hE
    (activeHalfMassTime lam c) (activeHalfMassTime_pos hlam c)
    (active_survival_half_mass hH hLE hlam hLam A c) e.time t ht
    (stripPoleState c.activeInterval ⊤ ⟨e, WithTop.coe_lt_top _, he⟩)
  have heq : -Real.log 2 * t / activeHalfMassTime lam c =
      -(16 * lam * Real.log 2 / 9) * t / c.r ^ 2 := by
    unfold activeHalfMassTime
    field_simp [hlam.ne', c.positive.ne']
  rw [heq] at hb
  exact hb

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
