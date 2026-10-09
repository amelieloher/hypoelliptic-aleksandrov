module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitTimeCalculus
import Mathlib.Tactic

/-! # Uniform bounds for the actual short-time quadratic operator -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- One universal cutoff constant bounds every actual localized quadratic operator. -/
theorem visitTimeQuadratic_uniform_operator_bound : ∃ D : ℝ, 0 ≤ D ∧
    ∀ (c : Clock) (b lam Lam : ℝ) (_hlam : 0 < lam) (A : SmoothAutonomous lam Lam)
      (p : Point), p.velocity 0 ∈ closure c.active →
      |forwardScalarOperator A.a
        (fun q => visitTimeCutoff b c.r c.positive q.time *
          visitQuadratic c (q.velocity 0)) p| ≤ 9 * D / 16 + 2 * Lam := by
  obtain ⟨D, hD, hd⟩ := visitTimeCutoff_deriv_bound
  refine ⟨D, hD, ?_⟩
  intro c b lam Lam hlam A p hp
  let eta := visitTimeCutoff b c.r c.positive
  have he := (visitTimeCutoff_properties b c.r c.positive).2 p.time
  have hf := visitQuadratic_nonneg c hp
  have ha := A.bounds (p.position 0) (p.velocity 0)
  have han : 0 ≤ A.a (p.position 0) (p.velocity 0) := hlam.le.trans ha.1
  have hfirst : |deriv eta p.time * visitQuadratic c (p.velocity 0)| ≤ 9 * D / 16 := by
    rw [abs_mul, abs_of_nonneg hf]
    have hm := mul_le_mul (hd b c.r c.positive p.time) (visitQuadratic_le c _)
      hf (by positivity : 0 ≤ D / c.r ^ 2)
    have hc : D / c.r ^ 2 * (9 * c.r ^ 2 / 16) = 9 * D / 16 := by
      field_simp [c.positive.ne']
    exact hm.trans_eq hc
  have hsecond : |2 * A.a (p.position 0) (p.velocity 0) * eta p.time| ≤ 2 * Lam := by
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) han) he.1)]
    exact (mul_le_mul_of_nonneg_left he.2 (mul_nonneg (by norm_num) han)).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left ha.2 (by norm_num : 0 ≤ (2 : ℝ)))
  rw [visitTimeQuadratic_operator c eta (visitTimeCutoff_properties b c.r c.positive).1]
  simpa only [sub_zero, zero_sub, abs_neg] using
    (abs_sub_le (deriv eta p.time * visitQuadratic c (p.velocity 0)) 0
      (2 * A.a (p.position 0) (p.velocity 0) * eta p.time)).trans
        (by simpa only [sub_zero, zero_sub, abs_neg] using add_le_add hfirst hsecond)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
