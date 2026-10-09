module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.Setting
import Mathlib.Tactic

/-! # The numerical consequence of the source's quadratic visit estimate -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous

/-- Cancel the positive quadratic scale in the exact source estimate. -/
theorem visit_mass_quadratic_bound {lam Lam R r M : ℝ} (hlam : 0 < lam)
    (hr : 0 < r)
    (h : 5 / 16 * r ^ 2 * M ≤ 9 / 16 * r ^ 2 + 6 * Lam / lam * R * r) :
    M ≤ 9 / 5 + 96 * Lam / (5 * lam) * (R / r) := by
  have hp : 0 < 5 / 16 * r ^ 2 := by positivity
  have he : (5 / 16 * r ^ 2) * (9 / 5 + 96 * Lam / (5 * lam) * (R / r)) =
      9 / 16 * r ^ 2 + 6 * Lam / lam * R * r := by
    field_simp
    ring
  rw [← he] at h
  nlinarith only [h, hp]

/-- A uniform constant depending only on ellipticity controls the resulting count bound. -/
theorem exists_visit_mass_arithmetic_constant {lam Lam : ℝ}
    (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R r M : ℝ), 0 < R → 0 < r →
      (5 / 16 * r ^ 2 * M ≤ 9 / 16 * r ^ 2 + 6 * Lam / lam * R * r) →
      M ≤ C * (1 + R / r) := by
  let K := 96 * Lam / (5 * lam)
  have hK : 0 < K := div_pos (mul_pos (by norm_num) (hlam.trans_le hLam)) (by positivity)
  refine ⟨9 / 5 + K, by linarith, ?_⟩
  intro R r M hR hr h
  have hb := visit_mass_quadratic_bound hlam hr h
  change M ≤ 9 / 5 + K * (R / r) at hb
  have hp : 0 < R / r := div_pos hR hr
  nlinarith only [hb, hp, hK]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
