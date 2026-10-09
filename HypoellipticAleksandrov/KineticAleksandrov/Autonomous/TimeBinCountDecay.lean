module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VelocityReturnAction
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitMassSupport

/-! # Uniform velocity decay throughout an elapsed-time bin

This is the velocity-return input to time-bin counting, rather than a bound
on the visit-counting measure itself.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Set MeasureTheory

/-- Elapsed time after the start of bin `j` has at least its dimensionless bin index. -/
theorem timeBinCount_scaled_time_le (c : Clock) (j : ℕ) (t : ℝ)
    (ht : (j : ℝ) * c.r ^ 2 ≤ t) :
    1 + (j : ℝ) ≤ 1 + t / c.r ^ 2 := by
  have h := (le_div_iff₀ (sq_pos_of_pos c.positive)).mpr ht
  linarith only [h]

/-- The source square-root decay is bounded by its value at the bin's left endpoint. -/
theorem timeBinCount_decay_le (c : Clock) (j : ℕ) (t : ℝ)
    (ht : (j : ℝ) * c.r ^ 2 ≤ t) :
    (1 + t / c.r ^ 2) ^ (-1 / 2 : ℝ) ≤ (1 + (j : ℝ)) ^ (-1 / 2 : ℝ) :=
  Real.rpow_le_rpow_of_nonpos (by positivity) (timeBinCount_scaled_time_le c j t ht)
    (by norm_num)

/-- The actual active-velocity action has a uniform square-root bound throughout each bin. -/
theorem timeBinCount_velocity_decay_of_return_time
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hReturn : ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (F : BoundedBorel Z),
      (∀ z, 0 ≤ F z) → ∀ t s X v : ℝ,
      0 < t → 2 * t ≤ s → s ≤ 3 * t → |v| ≤ Real.sqrt t →
      S hH hLE hlam hLam A t F (X, v) ≤ C * S hH hLE hlam hLam A s F (X, v)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock) (P : Point),
      |c.vbar| = 2 * c.r → P.velocity 0 ∈ closure c.entrance →
      ∀ (j : ℕ) (t : ℝ), (j : ℝ) * c.r ^ 2 ≤ t →
      S hH hLE hlam hLam A t (activeVelocityDatum c) (P.position 0, P.velocity 0) ≤
        C * (1 + (j : ℝ)) ^ (-1 / 2 : ℝ) := by
  obtain ⟨C, hC, h⟩ := velocity_return_action_of_return_time hH hLE hlam hLam hReturn
  refine ⟨C, hC, ?_⟩
  intro A c P hbar hv j t ht
  have hb := (c.active_abs_bounds (enlarged_closedEntrance_subset_active c hv)).2
  rw [hbar] at hb
  have hp : |P.velocity 0| ≤ 3 * c.r := by linarith only [hb, c.positive]
  have ht0 : 0 ≤ t := (mul_nonneg (Nat.cast_nonneg j) (sq_nonneg c.r)).trans ht
  exact (h A c (P.position 0, P.velocity 0) t hbar hp ht0).trans
    (mul_le_mul_of_nonneg_left (timeBinCount_decay_le c j t ht) hC.le)

/-- A uniform probability bound on a bin gives radius-squared times that bound in occupation. -/
theorem timeBinCount_integral_le {r a b D : ℝ} {f : ℝ → ℝ}
    (hab : a ≤ b) (hlen : b - a ≤ r ^ 2) (hD : 0 ≤ D)
    (hi : IntegrableOn f (Ioc a b)) (hb : ∀ t ∈ Ioc a b, f t ≤ D) :
    (∫ t in Ioc a b, f t) ≤ r ^ 2 * D := by
  have hm := setIntegral_mono_on hi
    (integrableOn_const (C := D) (by simp : volume (Ioc a b) ≠ ⊤)) measurableSet_Ioc hb
  have hv : volume.real (Ioc a b) = b - a := by
    rw [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  rw [setIntegral_const, hv, smul_eq_mul] at hm
  exact hm.trans (mul_le_mul_of_nonneg_right hlen hD)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
