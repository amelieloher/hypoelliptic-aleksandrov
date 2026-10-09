module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionCellCountBounds
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionCellsSlab
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitMassCanonical
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ReturnTime
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TimeBinCountReturnBridge
import Mathlib.Tactic

/-! # Position-cell concentration from the literal source start and time-count conclusions

The two conditional inputs are exactly the source slab start inequality and
the source time-bin count assigned to AU-14a. Box concentration is derived
from the return-time chain relative to its explicit preliminary P6 input.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- Every canonical observed visit count is finite, with an arbitrary positive horizon. -/
theorem visitsFromZero_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (T : ℝ) (P : Point)
    (hbar : |c.vbar| = 2 * c.r) (hJ : closure c.active ⊆ J.carrier)
    (hT : 0 < T) (hvel : P.velocity 0 ∈ closure c.entrance) :
    IsFiniteMeasure (visitsFromZero hH hLE hlam hLam A c J T P) :=
  enlargedVisitStarts_isFiniteMeasure hH hLE hlam hLam A c J (1 + T) T P
    (by linarith) hT (by nlinarith) hbar hJ hvel

/-- Source position concentration, including the initial atom and the truncated final bin. -/
theorem position_cell_count_of_start_time
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (alpha : ℝ)
    (ha : enlargedAdmissibleAlpha lam Lam hlam hLam alpha)
    (hp6 : SmoothAutonomousP6Statement lam Lam)
    (hTime : ∃ Ct : ℝ, 0 < Ct ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock)
      (J : Interval) (T : ℝ) (P : Point),
      |c.vbar| = 2 * c.r → closure c.active ⊆ J.carrier → 0 < T →
      P.velocity 0 ∈ closure c.entrance → ∀ j : ℕ,
        enlargedTimeVisitMass (visitsFromZero hH hLE hlam hLam A c J T P) c P.time j ≤
          Ct * (1 + (j : ℝ)) ^ (-1 / 2 : ℝ))
    (hStart : ∃ A0 Cs : ℝ, 0 < A0 ∧ 0 < Cs ∧
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
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock)
      (J : Interval) (T : ℝ) (P : Point),
      |c.vbar| = 2 * c.r → closure c.active ⊆ J.carrier → 0 < T →
      P.velocity 0 ∈ closure c.entrance → ∀ (j : ℕ) (k : ℤ),
        enlargedPositionVisitMass (visitsFromZero hH hLE hlam hLam A c J T P)
          c P.time 0 j k ≤ C * (1 + (j : ℝ)) ^ (-(2 - alpha) / 2) := by
  obtain ⟨Ct, hCt, htime⟩ := hTime
  obtain ⟨A0, Cs, hA0, hCs, hstart⟩ := hStart
  obtain ⟨B, hB, hbox⟩ := box_concentration_of_return_time hH hLE lam Lam hlam hLam
    alpha ha.1 ha.2 A0 hA0 (return_time_ambient_of_scalar hH hLE hlam hLam
      (return_time hH hLE lam Lam hlam hLam hp6))
  refine ⟨Ct + 2 * Cs * B, by positivity, ?_⟩
  intro A c J T P hbar hJ hT hvel j k
  let nu := visitsFromZero hH hLE hlam hLam A c J T P
  have : IsFiniteMeasure nu :=
    visitsFromZero_isFiniteMeasure hH hLE hlam hLam A c J T P hbar hJ hT hvel
  have hs : ∀ᵐ p ∂nu, p.time < P.time + T :=
    (enlargedVisitStarts_ae_support hH hLE hlam hLam A c J P.time (P.time + T)
      P le_rfl (by linarith)).mono fun _ hp => hp.2.1
  have hdecay : 0 ≤ (1 + (j : ℝ)) ^ (-(2 - alpha) / 2) :=
    Real.rpow_nonneg (by positivity) _
  by_cases hj : j = 0
  · subst j
    have hm := (enlargedPositionVisitMass_le_timeVisitMass nu c P.time 0 0 k).trans
      (htime A c J T P hbar hJ hT hvel 0)
    simp only [Nat.cast_zero, add_zero, Real.one_rpow, mul_one] at hm ⊢
    exact hm.trans (le_add_of_nonneg_right (by positivity))
  · by_cases hlate : T ≤ (j : ℝ) * c.r ^ 2
    · rw [enlargedPositionVisitMass_eq_zero_of_horizon nu c P.time 0 T j k hs hlate]
      exact mul_nonneg (by positivity) hdecay
    · let a := (j : ℝ) * c.r ^ 2
      let b := min (((j : ℝ) + 1) * c.r ^ 2) T
      have hr2 : 0 < c.r ^ 2 := sq_pos_of_pos c.positive
      have ha0 : 0 ≤ a := mul_nonneg (Nat.cast_nonneg j) hr2.le
      have hab : a < b := lt_min (by dsimp [a]; nlinarith) (lt_of_not_ge hlate)
      have hlen : b - a ≤ c.r ^ 2 := by
        have h := min_le_left (((j : ℝ) + 1) * c.r ^ 2) T
        dsimp only [a, b]
        nlinarith
      let E := fullSpaceEvolution hH hLE hlam hLam A
      let Y := ((k : ℝ) + 1 / 2) * c.r ^ 3
      let f := fun t => (kernelXV E (Real.toNNReal t)
        (P.position 0, P.velocity 0) (box A0 c.r Y)).toReal
      have hz : |P.velocity 0| ≤ 3 * c.r := by
        have h := (c.active_abs_bounds (enlarged_closedEntrance_subset_active c hvel)).2
        rw [hbar] at h
        linarith
      have hf (t : ℝ) (ht : 0 ≤ t) : f t ≤ B * (1 + t / c.r ^ 2) ^ (-gamma alpha / 2) := by
        simpa only [Real.coe_toNNReal t ht] using
          hbox A (P.position 0, P.velocity 0) Y c.r (Real.toNNReal t) c.positive hz
      have hslab := position_concentration_slab_le f B (gamma alpha) c.r b j hB.le
        (by dsimp only [gamma]; linarith [ha.2]) c.positive hab.le hlen
        (position_box_probability_integrable E (P.position 0, P.velocity 0) A0 c.r Y a b) hf
      have hsource := hstart A c J T P hbar hJ hT hvel a b k ha0 hab hlen (min_le_right _ _)
      rw [enlargedPositionVisitMass_eq_truncated_slab nu c P.time 0 T j k hj hs]
      have h := hsource.trans (mul_le_mul_of_nonneg_left hslab hCs.le)
      apply h.trans
      dsimp only [gamma]
      rw [← mul_assoc]
      apply mul_le_mul_of_nonneg_right _ hdecay
      nlinarith

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
