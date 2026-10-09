module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TerminalMomentBoundsPolynomials
import Mathlib.Tactic

/-! # Fourth-order polynomial supersolutions for terminal moments

The source upper ellipticity bound suffices; no derivatives of the coefficient
or full-space construction are used.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov.Parabolic

/-- Quartic velocity moment with its quadratic and constant diffusion corrections. -/
def velocityFourthBarrier (Lam v0 tau : ℝ) (p : Point) : ℝ :=
  (p.velocity 0-v0)^4+12*Lam*(tau-p.time)*(p.velocity 0-v0)^2+
    12*Lam^2*(tau-p.time)^2

/-- Quartic transported position moment with its integrated diffusion corrections. -/
def positionFourthBarrier (Lam X0 tau : ℝ) (p : Point) : ℝ :=
  (p.position 0-X0+(tau-p.time)*p.velocity 0)^4+
    4*Lam*(tau-p.time)^3*(p.position 0-X0+(tau-p.time)*p.velocity 0)^2+
    (4/3 : ℝ)*Lam^2*(tau-p.time)^6

/-- Terminal velocity data are exactly the fourth displacement power. -/
theorem velocityFourthBarrier_terminal (Lam v0 : ℝ) (p : Point) :
    velocityFourthBarrier Lam v0 p.time p = (p.velocity 0-v0)^4 := by
  simp only [velocityFourthBarrier, sub_self, mul_zero, zero_mul, add_zero,
    zero_pow (by norm_num : (2 : ℕ) ≠ 0)]

/-- Terminal position data are exactly the fourth displacement power. -/
theorem positionFourthBarrier_terminal (Lam X0 : ℝ) (p : Point) :
    positionFourthBarrier Lam X0 p.time p = (p.position 0-X0)^4 := by
  simp only [positionFourthBarrier, sub_self, zero_mul, add_zero,
    zero_pow (by norm_num : (3 : ℕ) ≠ 0),
    zero_pow (by norm_num : (6 : ℕ) ≠ 0), mul_zero]

/-- First derivative of a quartic with its quadratic correction. -/
theorem quartic_correction_deriv (u b c d v : ℝ) :
    deriv (fun w => (u+b*w)^4+c*(u+b*w)^2+d) v =
      b*(4*(u+b*v)^3+2*c*(u+b*v)) := by
  have hy := ((hasDerivAt_id v).const_mul b).const_add u
  apply HasDerivAt.deriv
  convert ((hy.fun_pow 4).add ((hy.fun_pow 2).const_mul c)).add_const d using 1 <;>
    ((try funext w); (try dsimp); all_goals ring)

/-- Second derivative of the same polynomial, including all correction terms. -/
theorem quartic_correction_second_deriv (u b c d v : ℝ) :
    deriv (deriv (fun w => (u+b*w)^4+c*(u+b*w)^2+d)) v =
      b^2*(12*(u+b*v)^2+2*c) := by
  have he : deriv (fun w => (u+b*w)^4+c*(u+b*w)^2+d) =
      fun w => b*(4*(u+b*w)^3+2*c*(u+b*w)) := by
    funext w
    exact quartic_correction_deriv u b c d w
  rw [he]
  have hy := ((hasDerivAt_id v).const_mul b).const_add u
  apply HasDerivAt.deriv
  convert (((hy.fun_pow 3).const_mul 4).add (hy.const_mul (2*c))).const_mul b
    using 1 <;> ((try funext w); (try dsimp); all_goals ring)

/-- Exact quartic velocity computation for the physical operator. -/
theorem velocityFourthBarrier_operator (a : ℝ → ℝ → ℝ) (Lam v0 tau : ℝ)
    (p : Point) :
    forwardScalarOperator a (velocityFourthBarrier Lam v0 tau) p =
      -12*(Lam-a (p.position 0) (p.velocity 0))*
        ((p.velocity 0-v0)^2+2*Lam*(tau-p.time)) := by
  rw [forwardScalarOperator, kineticPositionGradient_scalar, kineticVelocityHessian_scalar]
  have ht : deriv (fun t => velocityFourthBarrier Lam v0 tau
      ⟨t, p.position, p.velocity⟩) p.time =
      -12*Lam*(p.velocity 0-v0)^2-24*Lam^2*(tau-p.time) := by
    have hs := (hasDerivAt_const p.time tau).sub (hasDerivAt_id p.time)
    apply HasDerivAt.deriv
    convert ((hasDerivAt_const p.time ((p.velocity 0-v0)^4)).add
      ((hs.const_mul (12*Lam)).mul_const ((p.velocity 0-v0)^2))).add
        ((hs.fun_pow 2).const_mul (12*Lam^2)) using 1 <;>
      ((try funext t); (try dsimp [velocityFourthBarrier]); all_goals ring)
  have hx : deriv (fun x => velocityFourthBarrier Lam v0 tau
      ⟨p.time, fun _ => x, p.velocity⟩) (p.position 0) = 0 := by
    change deriv (fun _ : ℝ => (p.velocity 0-v0)^4+
      12*Lam*(tau-p.time)*(p.velocity 0-v0)^2+12*Lam^2*(tau-p.time)^2) _ = 0
    exact deriv_const _ _
  have he : (fun v => velocityFourthBarrier Lam v0 tau
      ⟨p.time, p.position, fun _ => v⟩) =
      fun v => (-v0+1*v)^4+(12*Lam*(tau-p.time))*(-v0+1*v)^2+
        12*Lam^2*(tau-p.time)^2 := by
    funext v
    dsimp [velocityFourthBarrier]
    ring
  rw [kineticTimeDerivative, ht, hx, he, quartic_correction_second_deriv]
  ring

/-- Exact quartic position computation with cancellation of transport terms. -/
theorem positionFourthBarrier_operator (a : ℝ → ℝ → ℝ) (Lam X0 tau : ℝ)
    (p : Point) :
    forwardScalarOperator a (positionFourthBarrier Lam X0 tau) p =
      -(Lam-a (p.position 0) (p.velocity 0))*
        (12*(tau-p.time)^2*(p.position 0-X0+(tau-p.time)*p.velocity 0)^2+
          8*Lam*(tau-p.time)^5) := by
  rw [forwardScalarOperator, kineticPositionGradient_scalar, kineticVelocityHessian_scalar]
  let y := p.position 0-X0+(tau-p.time)*p.velocity 0
  have ht : deriv (fun t => positionFourthBarrier Lam X0 tau
      ⟨t, p.position, p.velocity⟩) p.time =
      -4*y^3*p.velocity 0-12*Lam*(tau-p.time)^2*y^2-
        8*Lam*(tau-p.time)^3*y*p.velocity 0-8*Lam^2*(tau-p.time)^5 := by
    have hs := (hasDerivAt_const p.time tau).sub (hasDerivAt_id p.time)
    have hy := (hs.mul_const (p.velocity 0)).const_add (p.position 0-X0)
    apply HasDerivAt.deriv
    convert ((hy.fun_pow 4).add
      (((hs.fun_pow 3).const_mul (4*Lam)).mul (hy.fun_pow 2))).add
        ((hs.fun_pow 6).const_mul ((4/3 : ℝ)*Lam^2)) using 1 <;>
      ((try funext t); (try dsimp [positionFourthBarrier, y]); all_goals ring)
  have hx : deriv (fun x => positionFourthBarrier Lam X0 tau
      ⟨p.time, fun _ => x, p.velocity⟩) (p.position 0) =
      4*y^3+8*Lam*(tau-p.time)^3*y := by
    have hy := ((hasDerivAt_id (p.position 0)).sub_const X0).add_const
      ((tau-p.time)*p.velocity 0)
    apply HasDerivAt.deriv
    convert ((hy.fun_pow 4).add ((hy.fun_pow 2).const_mul
      (4*Lam*(tau-p.time)^3))).add_const ((4/3 : ℝ)*Lam^2*(tau-p.time)^6)
        using 1 <;> ((try funext x); (try dsimp [positionFourthBarrier, y]); all_goals ring)
  have he : (fun v => positionFourthBarrier Lam X0 tau
      ⟨p.time, p.position, fun _ => v⟩) =
      fun v => (p.position 0-X0+(tau-p.time)*v)^4+
        (4*Lam*(tau-p.time)^3)*(p.position 0-X0+(tau-p.time)*v)^2+
          (4/3 : ℝ)*Lam^2*(tau-p.time)^6 := rfl
  rw [kineticTimeDerivative, ht, hx, he, quartic_correction_second_deriv]
  dsimp [y]
  ring

/-- Quartic velocity is a supersolution on the past of its terminal time. -/
theorem velocityFourthBarrier_operator_nonpos (a : ℝ → ℝ → ℝ)
    {Lam : ℝ} (hLam : 0 ≤ Lam) (v0 tau : ℝ) (p : Point)
    (ht : p.time ≤ tau) (ha : a (p.position 0) (p.velocity 0) ≤ Lam) :
    forwardScalarOperator a (velocityFourthBarrier Lam v0 tau) p ≤ 0 := by
  rw [velocityFourthBarrier_operator]
  apply mul_nonpos_of_nonpos_of_nonneg
  · linarith
  · exact add_nonneg (sq_nonneg _) (mul_nonneg (by positivity) (sub_nonneg.mpr ht))

/-- Quartic position is a supersolution on the same past domain. -/
theorem positionFourthBarrier_operator_nonpos (a : ℝ → ℝ → ℝ)
    {Lam : ℝ} (hLam : 0 ≤ Lam) (X0 tau : ℝ) (p : Point)
    (ht : p.time ≤ tau) (ha : a (p.position 0) (p.velocity 0) ≤ Lam) :
    forwardScalarOperator a (positionFourthBarrier Lam X0 tau) p ≤ 0 := by
  rw [positionFourthBarrier_operator]
  apply mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sub_nonneg.mpr ha))
  have hs := sub_nonneg.mpr ht
  positivity

/-- Exact starting-point fourth velocity value. -/
theorem velocityFourthBarrier_start (Lam X0 v0 T : ℝ) :
    velocityFourthBarrier Lam v0 T ⟨0, fun _ => X0, fun _ => v0⟩ = 12*Lam^2*T^2 := by
  simp only [velocityFourthBarrier, sub_self, sub_zero,
    zero_pow (by norm_num : (4 : ℕ) ≠ 0),
    zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_add]

/-- The fourth position start value has the required source time powers. -/
theorem positionFourthBarrier_start (Lam X0 v0 T : ℝ) :
    positionFourthBarrier Lam X0 T ⟨0, fun _ => X0, fun _ => v0⟩ =
      v0^4*T^4+4*Lam*v0^2*T^5+(4/3 : ℝ)*Lam^2*T^6 := by
  simp only [positionFourthBarrier, sub_self, zero_add, sub_zero]
  ring

/-- A uniform numerical constant controls both terms in the fourth position value. -/
theorem positionFourthBarrier_start_le (Lam X0 v0 T : ℝ) :
    positionFourthBarrier Lam X0 T ⟨0, fun _ => X0, fun _ => v0⟩ ≤
      4*(v0^4*T^4+Lam^2*T^6) := by
  rw [positionFourthBarrier_start]
  nlinarith only [sq_nonneg (v0^2*T^2-Lam*T^3),
    sq_nonneg (v0^2*T^2), sq_nonneg (Lam*T^3)]

/-- Velocity fourth-moment barrier is nonnegative on its terminal past. -/
theorem velocityFourthBarrier_nonneg {Lam : ℝ} (hLam : 0 ≤ Lam)
    (v0 tau : ℝ) (p : Point) (ht : p.time ≤ tau) :
    0 ≤ velocityFourthBarrier Lam v0 tau p := by
  dsimp [velocityFourthBarrier]
  have hs := sub_nonneg.mpr ht
  positivity

/-- Position fourth-moment barrier is nonnegative on the same past. -/
theorem positionFourthBarrier_nonneg {Lam : ℝ} (hLam : 0 ≤ Lam)
    (X0 tau : ℝ) (p : Point) (ht : p.time ≤ tau) :
    0 ≤ positionFourthBarrier Lam X0 tau p := by
  dsimp [positionFourthBarrier]
  have hs := sub_nonneg.mpr ht
  positivity

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
