module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionCellCount
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionVisitSumHorizon

/-! # Source position visit counts and q-power sum

The exact source start identity and time-bin count remain named conditional
inputs until their assigned results are present. No mass or domination
premise is used: canonical finiteness is proved by the enlarged recursion.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- The position-visits statement, given the smooth autonomous estimates and a start time. -/
theorem positionVisitsStatement_holds_of_start_time
    (hp6 : ∀ (lam Lam : ℝ), 0 < lam → lam ≤ Lam → SmoothAutonomousP6Statement lam Lam)
    (hTime : ∀ (hH : HormanderHypoellipticityStatement)
      (hLE : LiebermanEllipsoidDirichletStatement)
      (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam),
      ∃ Ct : ℝ, 0 < Ct ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock)
      (J : Interval) (T : ℝ) (P : Point),
      |c.vbar| = 2 * c.r → closure c.active ⊆ J.carrier → 0 < T →
      P.velocity 0 ∈ closure c.entrance → ∀ j : ℕ,
        enlargedTimeVisitMass (visitsFromZero hH hLE hlam hLam A c J T P) c P.time j ≤
          Ct * (1 + (j : ℝ)) ^ (-1 / 2 : ℝ))
    (hStart : ∀ (hH : HormanderHypoellipticityStatement)
      (hLE : LiebermanEllipsoidDirichletStatement)
      (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam),
      ∃ A0 Cs : ℝ, 0 < A0 ∧ 0 < Cs ∧
      ∀ (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (T : ℝ) (P : Point),
      |c.vbar| = 2 * c.r → closure c.active ⊆ J.carrier → 0 < T →
      P.velocity 0 ∈ closure c.entrance → ∀ (a b : ℝ) (k : ℤ),
      0 ≤ a → a < b → b - a ≤ c.r ^ 2 → b ≤ T →
      enlargedPositionSlabMass (visitsFromZero hH hLE hlam hLam A c J T P)
        c P.time 0 a b k ≤ Cs *
          ((kernelXV (fullSpaceEvolution hH hLE hlam hLam A) (Real.toNNReal b)
            (P.position 0, P.velocity 0)
              (box A0 c.r (((k : ℝ) + 1 / 2) * c.r ^ 3))).toReal +
           c.r ^ (-2 : ℤ) * ∫ t in Ioc a b,
             (kernelXV (fullSpaceEvolution hH hLE hlam hLam A) (Real.toNNReal t)
               (P.position 0, P.velocity 0)
                 (box A0 c.r (((k : ℝ) + 1 / 2) * c.r ^ 3))).toReal)) :
    PositionVisitsStatement := by
  intro hH hLE lam Lam hlam hLam alpha ha
  have ht := hTime hH hLE lam Lam hlam hLam
  have hstart := hStart hH hLE lam Lam hlam hLam
  obtain ⟨Cp, hCp, hcell⟩ := position_cell_count_of_start_time
    hH hLE hlam hLam alpha ha (hp6 lam Lam hlam hLam) ht hstart
  obtain ⟨Ct, hCt, htime⟩ := ht
  have hg := enlargedAdmissibleAlpha_gamma_range hlam hLam alpha ha
  constructor
  · refine ⟨Ct + Cp, add_pos hCt hCp, ?_⟩
    intro A c J T P hbar hJ hT hvel j
    constructor
    · apply (htime A c J T P hbar hJ hT hvel j).trans
      exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCp.le)
        (Real.rpow_nonneg (by positivity) _)
    · intro k
      apply (hcell A c J T P hbar hJ hT hvel j k).trans
      exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCt.le)
        (Real.rpow_nonneg (by positivity) _)
  · intro q hq
    let g := 2 - alpha
    let F := (1 + 1 / (1 - (1 + g * (q - 1)) / 2)) *
      (3 : ℝ) ^ (1 - (1 + g * (q - 1)) / 2)
    have hprod : g * (q - 1) < 1 := by
      have hh := mul_lt_mul_of_pos_right hg.2 (by linarith [hq.1] : 0 < q - 1)
      change (2 - alpha) * (q - 1) < 1
      linarith [hq.2]
    have hb : 0 < 1 - (1 + g * (q - 1)) / 2 := by linarith
    have hF : 0 < F := by dsimp only [F]; positivity
    refine ⟨Cp ^ (q - 1) * Ct * F, by positivity, ?_⟩
    intro A c J R T P hR hT hTR hbar hJ hvel
    have : IsFiniteMeasure (visitsFromZero hH hLE hlam hLam A c J T P) :=
      visitsFromZero_isFiniteMeasure hH hLE hlam hLam A c J T P hbar hJ hT hvel
    apply enlargedPositionVisitMass_power_sum_horizon_le
      (visitsFromZero hH hLE hlam hLam A c J T P) c P.time 0 R T hR hT hTR
    · exact (enlargedVisitStarts_ae_support hH hLE hlam hLam A c J P.time (P.time + T)
        P le_rfl (by linarith)).mono fun _ hp => hp.2.1
    · exact hCt.le
    · exact hCp.le
    · exact hg
    · exact hq
    · exact htime A c J T P hbar hJ hT hvel
    · exact hcell A c J T P hbar hJ hT hvel

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
