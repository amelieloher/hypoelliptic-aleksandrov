module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitTimeCalculus

/-! # The localized quadratic and its operator vanish off the same short time window -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- Both localized test terms vanish outside the closed window of length three r squared. -/
theorem visitTimeQuadratic_zero_off_window (c : Clock) (b : ℝ) (a : ℝ → ℝ → ℝ)
    (p : Point) (ht : p.time ∉ Icc (b - c.r ^ 2) (b + 2 * c.r ^ 2)) :
    visitTimeCutoff b c.r c.positive p.time * visitQuadratic c (p.velocity 0) = 0 ∧
      forwardScalarOperator a
        (fun q => visitTimeCutoff b c.r c.positive q.time *
          visitQuadratic c (q.velocity 0)) p = 0 := by
  have he : visitTimeCutoff b c.r c.positive p.time = 0 := by
    by_contra hn
    exact ht (visitTimeCutoff_tsupport b c.r c.positive (subset_closure hn))
  have hd : deriv (visitTimeCutoff b c.r c.positive) p.time = 0 := by
    by_contra hn
    exact ht (visitTimeCutoff_deriv_tsupport b c.r c.positive (subset_closure hn))
  constructor
  · rw [he, zero_mul]
  · rw [visitTimeQuadratic_operator c _
      (visitTimeCutoff_properties b c.r c.positive).1, he, hd]
    simp only [zero_mul, mul_zero, sub_zero]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
