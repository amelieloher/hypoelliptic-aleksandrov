module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.IntegratedVelocityProfile
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TerminalMomentBoundsKernel
import Mathlib.Tactic

/-! # Bounded convex-difference occupation barrier

The difference cancels the linear growth of the two regularized absolute values.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open SectionTwo

/-- Time-dependent regularized absolute value in physical coordinates. -/
def velocityHeatProfile (R Lam T : ℝ) (p : Point) : ℝ :=
  velocityConvexProfile (R + 2 * Lam * (T - p.time)) (p.velocity 0)

/-- Bounded cancellation of two convex profiles, in evolution coordinates. -/
def velocityOccupationBarrier (r Lam T : ℝ) (p : Point) : ℝ :=
  velocityHeatProfile (r ^ 2) Lam T (terminalPhysicalPoint p) -
    velocityHeatProfile (r ^ 2) 0 T (terminalPhysicalPoint p)

/-- The cancellation barrier is continuous, including the terminal slice. -/
theorem velocityOccupationBarrier_continuous (r Lam T : ℝ) :
    Continuous (velocityOccupationBarrier r Lam T) := by
  unfold velocityOccupationBarrier velocityHeatProfile velocityConvexProfile
  apply Continuous.sub <;> apply Real.continuous_sqrt.comp <;>
    exact (continuous_const.add (continuous_const.mul
      (continuous_const.sub continuous_time))).add
        ((continuous_apply 0).comp continuous_position |>.pow 2)

/-- Slice regularity holds throughout the past when the regularization is positive. -/
theorem velocityOccupationBarrier_regular {r Lam : ℝ} (hr : 0 < r) (hLam : 0 ≤ Lam)
    (T : ℝ) (p : Point) (hp : p.time ≤ T) :
    IsSliceRegularAt (velocityOccupationBarrier r Lam T) p := by
  apply IsSliceRegularAt.of_contDiffAt
  change ContDiffAt ℝ 2 (fun q : ℝ × (PDE.Vec 1 × PDE.Vec 1) =>
    Real.sqrt (r ^ 2 + 2 * Lam * (T - q.1) + (q.2.1 0) ^ 2) -
      Real.sqrt (r ^ 2 + 2 * 0 * (T - q.1) + (q.2.1 0) ^ 2)) _
  apply ContDiffAt.sub
  · apply ContDiffAt.sqrt (by fun_prop)
    have hh := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hLam)
      (sub_nonneg.mpr hp)
    exact ne_of_gt (by nlinarith [sq_pos_of_pos hr, sq_nonneg (p.position 0)])
  · apply ContDiffAt.sqrt (by fun_prop)
    exact ne_of_gt (by nlinarith [sq_pos_of_pos hr, sq_nonneg (p.position 0)])

/-- The cancellation is nonnegative and uniformly bounded by the square-root time scale. -/
theorem velocityOccupationBarrier_bounds {r Lam : ℝ} (_hr : 0 < r) (hLam : 0 ≤ Lam)
    (T : ℝ) (p : Point) (hp : p.time ≤ T) :
    0 ≤ velocityOccupationBarrier r Lam T p ∧
      velocityOccupationBarrier r Lam T p ≤ Real.sqrt (2 * Lam * (T - p.time)) := by
  have h := velocityConvexProfile_increment (sq_nonneg r)
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hLam)
      (sub_nonneg.mpr hp)) (p.position 0)
  simpa only [velocityOccupationBarrier, velocityHeatProfile, terminalPhysicalPoint,
    mul_zero, zero_mul, add_zero] using h

/-- Exact operator of the expanding regularized absolute value. -/
theorem velocityHeatProfile_operator {R Lam T : ℝ} (p : Point)
    (hR : 0 < R + 2 * Lam * (T - p.time)) (a : ℝ → ℝ → ℝ) :
    forwardScalarOperator a (velocityHeatProfile R Lam T) p =
      -Lam / Real.sqrt (R + 2 * Lam * (T - p.time) + (p.velocity 0) ^ 2) +
        a (p.position 0) (p.velocity 0) *
          (R + 2 * Lam * (T - p.time)) /
            Real.sqrt (R + 2 * Lam * (T - p.time) + (p.velocity 0) ^ 2) ^ 3 := by
  have hp : 0 < R + 2 * Lam * (T - p.time) + (p.velocity 0) ^ 2 :=
    add_pos_of_pos_of_nonneg hR (sq_nonneg _)
  have ht : kineticTimeDerivative (velocityHeatProfile R Lam T) p =
      -Lam / Real.sqrt (R + 2 * Lam * (T - p.time) + (p.velocity 0) ^ 2) := by
    have hd : HasDerivAt (fun t : ℝ => R + 2 * Lam * (T - t) + (p.velocity 0) ^ 2)
        (-2 * Lam) p.time := by
      convert (((hasDerivAt_const p.time T).sub (hasDerivAt_id p.time)).const_mul
        (2 * Lam) |>.const_add R |>.add_const ((p.velocity 0) ^ 2)) using 1
      · funext t
        rfl
      · ring
    have hh := hd.sqrt (ne_of_gt hp)
    unfold kineticTimeDerivative velocityHeatProfile velocityConvexProfile
    rw [hh.deriv]
    field_simp
  have hx : kineticPositionGradient (velocityHeatProfile R Lam T) p 0 = 0 := by
    rw [kineticPositionGradient_scalar]
    change deriv (fun _ : ℝ => velocityHeatProfile R Lam T p) (p.position 0) = 0
    exact deriv_const _ _
  have hv : kineticVelocityHessian (velocityHeatProfile R Lam T) p 0 0 =
      (R + 2 * Lam * (T - p.time)) /
        Real.sqrt (R + 2 * Lam * (T - p.time) + (p.velocity 0) ^ 2) ^ 3 := by
    rw [kineticVelocityHessian_scalar]
    exact velocityConvexProfile_second_deriv hR _
  rw [forwardScalarOperator, ht, hx, hv]
  ring

/-- Each expanding profile is slice regular on its positive-parameter region. -/
theorem velocityHeatProfile_native_regular (R Lam T : ℝ) (p : Point)
    (hR : 0 < R + 2 * Lam * (T - p.time)) :
    IsSliceRegularAt (velocityHeatProfile R Lam T ∘ terminalPhysicalPoint) p := by
  apply IsSliceRegularAt.of_contDiffAt
  change ContDiffAt ℝ 2 (fun q : ℝ × (PDE.Vec 1 × PDE.Vec 1) =>
    Real.sqrt (R + 2 * Lam * (T - q.1) + (q.2.1 0) ^ 2)) _
  apply ContDiffAt.sqrt (by fun_prop)
  exact ne_of_gt (add_pos_of_pos_of_nonneg hR (sq_nonneg _))

/-- The expanding convex profile is a supersolution under the coefficient upper bound. -/
theorem velocityHeatProfile_operator_nonpos {R Lam T : ℝ} (p : Point)
    (hR : 0 < R + 2 * Lam * (T - p.time)) (hLam : 0 ≤ Lam)
    (a : ℝ → ℝ → ℝ) (ha : a (p.position 0) (p.velocity 0) ≤ Lam) :
    forwardScalarOperator a (velocityHeatProfile R Lam T) p ≤ 0 := by
  rw [velocityHeatProfile_operator p hR]
  let Q := R + 2 * Lam * (T - p.time)
  have hp : 0 < Q + (p.velocity 0) ^ 2 := add_pos_of_pos_of_nonneg hR (sq_nonneg _)
  have hs : 0 < Real.sqrt (Q + (p.velocity 0) ^ 2) := Real.sqrt_pos.2 hp
  have hsq := Real.sq_sqrt hp.le
  have he : -Lam / Real.sqrt (Q + (p.velocity 0) ^ 2) +
      a (p.position 0) (p.velocity 0) * Q /
        Real.sqrt (Q + (p.velocity 0) ^ 2) ^ 3 =
      (a (p.position 0) (p.velocity 0) * Q - Lam * (Q + (p.velocity 0) ^ 2)) /
        Real.sqrt (Q + (p.velocity 0) ^ 2) ^ 3 := by
    field_simp
    nlinarith
  change -Lam / Real.sqrt (Q + (p.velocity 0) ^ 2) +
    a (p.position 0) (p.velocity 0) * Q /
      Real.sqrt (Q + (p.velocity 0) ^ 2) ^ 3 ≤ 0
  rw [he]
  apply div_nonpos_of_nonpos_of_nonneg
  · have hh := mul_le_mul_of_nonneg_right ha hR.le
    nlinarith [mul_nonneg hLam (sq_nonneg (p.velocity 0))]
  · positivity

/-- The bounded cancellation has a strictly negative forcing on the velocity band. -/
theorem velocityOccupationBarrier_operator {lam Lam r : ℝ} (hlam : 0 < lam)
    (A : SmoothAutonomous lam Lam) (hr : 0 < r) (T : ℝ) (p : Point)
    (hp : p.time ≤ T) :
    transportedForwardOperator (evolutionCoefficient A.a) (identityDrift 1)
      (velocityOccupationBarrier r Lam T) p ≤
        -lam * (r ^ 2 / Real.sqrt (r ^ 2 + (p.position 0) ^ 2) ^ 3) := by
  have hLam : 0 ≤ Lam := (hlam.le.trans (A.bounds 0 0).1).trans (A.bounds 0 0).2
  have hR : 0 < r ^ 2 + 2 * Lam * (T - p.time) :=
    add_pos_of_pos_of_nonneg (sq_pos_of_pos hr)
      (mul_nonneg (mul_nonneg (by norm_num) hLam) (sub_nonneg.mpr hp))
  have h0 : 0 < r ^ 2 + 2 * 0 * (T - p.time) := by simpa using sq_pos_of_pos hr
  have he : velocityOccupationBarrier r Lam T =
      (fun p => (velocityHeatProfile (r ^ 2) Lam T ∘ terminalPhysicalPoint) p -
        (velocityHeatProfile (r ^ 2) 0 T ∘ terminalPhysicalPoint) p) := rfl
  rw [← viscousTransportedOperator_zero, he,
    viscousTransportedOperator_sub (velocityHeatProfile_native_regular _ _ _ p hR)
      (velocityHeatProfile_native_regular _ _ _ p h0),
    viscousTransportedOperator_zero, viscousTransportedOperator_zero,
    terminalPhysicalPoint_operator, terminalPhysicalPoint_operator,
    velocityHeatProfile_operator (terminalPhysicalPoint p) h0 A.a]
  have hh := velocityHeatProfile_operator_nonpos (terminalPhysicalPoint p) hR hLam
    A.a (A.bounds _ _).2
  have hl := (A.bounds (p.velocity 0) (p.position 0)).1
  have hd : 0 ≤ r ^ 2 / Real.sqrt (r ^ 2 + (p.position 0) ^ 2) ^ 3 := by positivity
  dsimp only [terminalPhysicalPoint] at hh ⊢
  simp only [mul_zero, zero_mul, add_zero, neg_zero, zero_div, zero_add]
  rw [mul_div_assoc]
  have hm := mul_le_mul_of_nonneg_right hl hd
  linarith

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
