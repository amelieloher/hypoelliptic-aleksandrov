module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ReturnIteration
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ReturnTimeScaling
import Mathlib.Tactic

/-! # The canonical full-space return-time comparison

The only conditional analytic input beyond the classical inputs is the preliminary p-six
admissibility statement. The constant is chosen before coefficients, data, times and points.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Parabolic Set MeasureTheory

/-- Smooth terminal data satisfy the return comparison at every kinetic scale. -/
theorem return_time_smooth
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hp6 : SmoothAutonomousP6Statement lam Lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (F : BoundedBorel Z),
      (∀ z, 0 ≤ F z) → ContDiff ℝ (⊤ : ℕ∞) F →
      ∀ t s X v : ℝ, 0 < t → 2 * t ≤ s → s ≤ 3 * t → |v| ≤ Real.sqrt t →
      S hH hLE hlam hLam A t F (X, v) ≤ C * S hH hLE hlam hLam A s F (X, v) := by
  obtain ⟨C, hC, hunit⟩ := return_time_unit_solution lam Lam hlam hLam hp6
  refine ⟨C, hC, ?_⟩
  intro A F hF0 hF t s X v ht hs hs1 hv
  let r := Real.sqrt t
  have hr : 0 < r := Real.sqrt_pos.mpr ht
  have hr2 : r ^ 2 = t := Real.sq_sqrt ht.le
  have hvn : |v / r| ≤ 1 := by
    rw [abs_div, abs_of_pos hr]
    exact (div_le_one hr).mpr hv
  have hslo : 2 ≤ s / t := (le_div_iff₀ ht).mpr (by linarith)
  have hshi : s / t ≤ 3 := (div_le_iff₀ ht).mpr hs1
  have hspos : 0 < s / t := by linarith
  obtain ⟨U, hu, hrep⟩ := exists_return_scaled_solution hH hLE hlam hLam A F hF0 hF r hr X
  have hstar : point (s / t) 0 (v / r) ∈ returnFutureRegion :=
    ⟨⟨hslo, hshi⟩, by simp [point, return_norm_one],
      by simpa only [point, return_norm_one] using hvn.trans (by norm_num : (1 : ℝ) ≤ 2)⟩
  have h := hunit _ U hu (v / r) hvn _ hstar
  rw [hrep _ (by norm_num [point]), hrep _ hspos] at h
  have hrv : r * (v / r) = v := by field_simp
  have hst : t * (s / t) = s := by field_simp
  simpa only [point, hr2, mul_one, mul_zero, sub_zero, hrv, hst] using h

/-- Bounded nonnegative Borel data satisfy the same full-space return comparison. -/
theorem return_time
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hp6 : SmoothAutonomousP6Statement lam Lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (F : BoundedBorel Z),
      (∀ z, 0 ≤ F z) → ∀ t s X v : ℝ,
      0 < t → 2 * t ≤ s → s ≤ 3 * t → |v| ≤ Real.sqrt t →
      S hH hLE hlam hLam A t F (X, v) ≤ C * S hH hLE hlam hLam A s F (X, v) := by
  obtain ⟨C, hC, hsmooth⟩ := return_time_smooth hH hLE lam Lam hlam hLam hp6
  refine ⟨C, hC, ?_⟩
  intro A F hF0 t s X v ht hs hs1 hv
  apply return_time_borel_of_smooth_tests hH hLE hlam hLam C hC.le A t s ht.le
    (by linarith) (X, v) ?_ F hF0
  intro G hG0 hG
  exact hsmooth A G hG0 hG t s X v ht hs hs1 hv

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
