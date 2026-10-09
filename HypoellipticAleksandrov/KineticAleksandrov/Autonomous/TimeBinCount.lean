module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TimeBinCountSlab
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TimeBinCountSupport
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitMassCanonical

/-! # The exact enlarged time-bin count, conditional on the source return-time theorem -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- The actual canonical visits satisfy the exact uniform time-bin count from the source. -/
theorem timeBinCount_holds_of_return_time
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hReturn : ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (F : BoundedBorel Z),
      (∀ z, 0 ≤ F z) → ∀ t s X v : ℝ,
      0 < t → 2 * t ≤ s → s ≤ 3 * t → |v| ≤ Real.sqrt t →
      S hH hLE hlam hLam A t F (X, v) ≤ C * S hH hLE hlam hLam A s F (X, v)) :
    ∃ Ct : ℝ, 0 < Ct ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval)
      (T : ℝ) (P : Point), |c.vbar| = 2 * c.r → closure c.active ⊆ J.carrier → 0 < T →
      P.velocity 0 ∈ closure c.entrance → ∀ j : ℕ,
      enlargedTimeVisitMass (visitsFromZero hH hLE hlam hLam A c J T P) c P.time j ≤
        Ct * (1 + (j : ℝ)) ^ (-1 / 2 : ℝ) := by
  obtain ⟨C, hC, hDecay⟩ := timeBinCount_velocity_decay_of_return_time
    hH hLE hlam hLam hReturn
  let D := 2 * entranceSlabConstant Lam * C
  have hD : 0 < D := by
    dsimp only [D]
    exact mul_pos (mul_pos (by norm_num) (entranceSlabConstant_pos hlam hLam)) hC
  refine ⟨1 + D, by positivity, ?_⟩
  intro A c J T P hbar hJ hT hvel j
  let nu := visitsFromZero hH hLE hlam hLam A c J T P
  have : IsFiniteMeasure nu := enlargedVisitStarts_isFiniteMeasure
    hH hLE hlam hLam A c J (1 + T) T P (by linarith) hT
      (by nlinarith [sq_nonneg T]) hbar hJ hvel
  have hnu : ∀ᵐ p ∂nu, p.time < P.time + T :=
    (enlargedVisitStarts_ae_support hH hLE hlam hLam A c J P.time (P.time + T)
      P le_rfl (by linarith)).mono fun _ hp => hp.2.1
  have hslab (a b : ℝ) (hja : (j : ℝ) * c.r ^ 2 ≤ a) (hab : a ≤ b)
      (hbT : b ≤ T) (hlen : b - a ≤ c.r ^ 2) :
      (nu {p | p.time ∈ Ioc (P.time + a) (P.time + b)}).toReal ≤
        D * (1 + (j : ℝ)) ^ (-1 / 2 : ℝ) :=
    timeBinCount_slab_le hH hLE hlam hLam C hC hDecay A c J T P
      hbar hJ hT hvel j a b hja hab hbT hlen
  by_cases hj : j = 0
  · subst j
    have hb : 0 < min (c.r ^ 2) T := lt_min (sq_pos_of_pos c.positive) hT
    have hs := hslab 0 (min (c.r ^ 2) T) (by simp) hb.le (min_le_right _ _)
      (by linarith [min_le_left (c.r ^ 2) T])
    have hm := timeBinCount_initial_mass_le_atom_add_slab nu c P.time T hnu
    have he := timeBinCount_initial_slice hH hLE hlam hLam A c J T P hvel
    have hs' : (nu {p | p.time ∈ Ioc P.time (P.time + min (c.r ^ 2) T)}).toReal ≤ D := by
      simpa only [Nat.cast_zero, zero_add, add_zero, Real.one_rpow, mul_one] using hs
    have he' : (nu {p | p.time = P.time}).toReal = 1 := by
      exact congrArg ENNReal.toReal he
    simpa only [Nat.cast_zero, add_zero, Real.one_rpow, mul_one] using
      hm.trans (by rw [he']; linarith only [hs'])
  · by_cases hlate : T ≤ (j : ℝ) * c.r ^ 2
    · rw [timeBinCount_mass_eq_zero_of_horizon_le hH hLE hlam hLam A c J T P hT j hj hlate]
      positivity
    · have haT : (j : ℝ) * c.r ^ 2 < T := lt_of_not_ge hlate
      let a := (j : ℝ) * c.r ^ 2
      let b := min (((j : ℝ) + 1) * c.r ^ 2) T
      have hab : a ≤ b := le_min (by
        dsimp only [a]
        nlinarith [sq_pos_of_pos c.positive]) haT.le
      have hs := hslab a b le_rfl hab (min_le_right _ _)
        (by dsimp only [a, b]; nlinarith [min_le_left (((j : ℝ) + 1) * c.r ^ 2) T])
      have hm := timeBinCount_mass_le_truncated_slab nu c P.time T j hj hnu
      exact (hm.trans hs).trans (mul_le_mul_of_nonneg_right (by linarith)
        (by positivity))

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
