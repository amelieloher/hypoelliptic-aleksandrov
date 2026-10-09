module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionStartCalculus
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoxConcentrationSetting
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockGeometry
import Mathlib.Tactic

/-! # Uniform localized generator bound for the position-start test -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov MeasureTheory Set

/-- The source localized quadratic has a uniform generator bound on the active interval. -/
theorem positionStartQuadratic_operator_bound {lam Lam : ℝ}
    (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock) (Y : ℝ) (p : Point),
      |c.vbar| = 2 * c.r → p.velocity 0 ∈ c.active →
      |forwardScalarOperator A.a
        (fun q => positionStartCutoff Y c.r c.positive (q.position 0) *
          visitQuadratic c (q.velocity 0)) p| ≤
        C * (box 4 c.r Y).indicator (fun _ => (1 : ℝ)) (p.position 0, p.velocity 0) := by
  obtain ⟨D, hD, hd⟩ := positionStartCutoff_deriv_bound
  refine ⟨2 * Lam + 27 * D / 16, by linarith, ?_⟩
  intro A c Y p hc hv
  have hr := c.positive
  let chi := positionStartCutoff Y c.r c.positive
  have hchi := (positionStartCutoff_properties Y c.r c.positive).1
  have h01 := (positionStartCutoff_properties Y c.r c.positive).2 (p.position 0)
  have hq0 := visitQuadratic_nonneg c (subset_closure hv)
  have hq := visitQuadratic_le c (p.velocity 0)
  have hva : |p.velocity 0| ≤ 3 * c.r := by
    have hh := (c.active_abs_bounds hv).2
    rw [hc] at hh
    linarith only [hh]
  have ha0 : 0 ≤ A.a (p.position 0) (p.velocity 0) :=
    hlam.le.trans (A.bounds _ _).1
  have ha := (A.bounds (p.position 0) (p.velocity 0)).2
  rw [positionStartQuadratic_operator c chi hchi]
  by_cases hp : (p.position 0, p.velocity 0) ∈ box 4 c.r Y
  · rw [indicator_of_mem hp, mul_one]
    apply (abs_sub _ _).trans
    rw [abs_mul, abs_mul, abs_of_nonneg hq0, abs_mul, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg ha0,
      abs_of_nonneg h01.1]
    have hfirst : |p.velocity 0| * |deriv chi (p.position 0)| *
        visitQuadratic c (p.velocity 0) ≤
        (3 * c.r) * (D / c.r ^ 3) * (9 * c.r ^ 2 / 16) := by
      apply mul_le_mul (mul_le_mul hva (hd Y c.r c.positive (p.position 0))
        (abs_nonneg _) (by positivity)) hq hq0 (by positivity)
    have hsecond : 2 * A.a (p.position 0) (p.velocity 0) * chi (p.position 0) ≤
        2 * Lam := by
      have h := mul_le_mul_of_nonneg_left h01.2 (by positivity :
        0 ≤ 2 * A.a (p.position 0) (p.velocity 0))
      simp only [mul_one] at h
      exact h.trans (mul_le_mul_of_nonneg_left ha (by norm_num))
    have he : (3 * c.r) * (D / c.r ^ 3) * (9 * c.r ^ 2 / 16) = 27 * D / 16 := by
      field_simp [c.positive.ne']
      ring
    rw [he] at hfirst
    linarith only [hfirst, hsecond]
  · rw [indicator_of_notMem hp, mul_zero]
    have hnot : p.position 0 ∉ tsupport chi := by
      intro hx
      have hh := positionStartCutoff_tsupport Y c.r c.positive hx
      apply hp
      change |p.position 0 - Y| ≤ 4 * c.r ^ 3 ∧ |p.velocity 0| ≤ 4 * c.r
      constructor
      · apply abs_le.mpr
        constructor <;> linarith [hh.1, hh.2, pow_pos c.positive 3]
      · linarith [c.positive]
    rw [image_eq_zero_of_notMem_tsupport hnot, deriv_of_notMem_tsupport hnot]
    simp only [mul_zero, zero_mul, sub_zero, abs_zero, le_refl]

/-- A concrete cutoff realizes the source localized position-visit test for every cell. -/
theorem exists_position_visit_test {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (c : Clock) (hc : |c.vbar| = 2 * c.r) :
    ∃ A0 C : ℝ, 0 < A0 ∧ 0 < C ∧ ∀ k : ℤ, ∃ chi : ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) chi ∧ (∀ X, 0 ≤ chi X ∧ chi X ≤ 1) ∧
      (∀ X ∈ enlargedPositionCell c.r 0 k, chi X = 1) ∧
      ∀ (A : SmoothAutonomous lam Lam) (p : Point), p.velocity 0 ∈ c.active →
        |forwardScalarOperator A.a (fun q => chi (q.position 0) *
          visitQuadratic c (q.velocity 0)) p| ≤
          C * (box A0 c.r (((k : ℝ) + 1 / 2) * c.r ^ 3)).indicator
            (fun _ => (1 : ℝ)) (p.position 0, p.velocity 0) := by
  obtain ⟨C, hC, hb⟩ := positionStartQuadratic_operator_bound hlam hLam
  refine ⟨4, C, by norm_num, hC, ?_⟩
  intro k
  let Y := ((k : ℝ) + 1 / 2) * c.r ^ 3
  refine ⟨positionStartCutoff Y c.r c.positive,
    (positionStartCutoff_properties Y c.r c.positive).1,
    (positionStartCutoff_properties Y c.r c.positive).2, ?_, ?_⟩
  · intro X hX
    simpa only [zero_add] using positionStartCutoff_eq_one_on_cell c.r 0 c.positive k hX
  · intro A p hv
    exact hb A c Y p hc hv

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
