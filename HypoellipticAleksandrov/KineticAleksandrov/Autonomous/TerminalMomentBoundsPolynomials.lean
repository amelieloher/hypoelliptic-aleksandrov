module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.Setting
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ScalarAdaptersCalculus
import Mathlib.Tactic

/-! # Quadratic terminal-moment supersolutions

These are actual polynomials for the physical operator, independent of
full-space kernel construction. They are not terminal-kernel moment estimates.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov.Parabolic

/-- Quadratic velocity moment with its sharp diffusion correction. -/
def velocitySecondBarrier (Lam v0 tau : ℝ) (p : Point) : ℝ :=
  (p.velocity 0-v0)^2+2*Lam*(tau-p.time)

/-- Quadratic transported position moment with its integrated diffusion correction. -/
def positionSecondBarrier (Lam X0 tau : ℝ) (p : Point) : ℝ :=
  (p.position 0-X0+(tau-p.time)*p.velocity 0)^2+
    (2/3 : ℝ)*Lam*(tau-p.time)^3

/-- Terminal velocity data of the quadratic polynomial. -/
theorem velocitySecondBarrier_terminal (Lam v0 : ℝ) (p : Point) :
    velocitySecondBarrier Lam v0 p.time p = (p.velocity 0-v0)^2 := by
  simp only [velocitySecondBarrier, sub_self, mul_zero, add_zero]

/-- Terminal position data of the quadratic polynomial. -/
theorem positionSecondBarrier_terminal (Lam X0 : ℝ) (p : Point) :
    positionSecondBarrier Lam X0 p.time p = (p.position 0-X0)^2 := by
  simp only [positionSecondBarrier, sub_self, zero_mul, add_zero, zero_pow
    (by norm_num : (3 : ℕ) ≠ 0), mul_zero]

/-- Exact quadratic velocity computation for the physical kinetic operator. -/
theorem velocitySecondBarrier_operator (a : ℝ → ℝ → ℝ) (Lam v0 tau : ℝ)
    (p : Point) :
    forwardScalarOperator a (velocitySecondBarrier Lam v0 tau) p =
      -2*(Lam-a (p.position 0) (p.velocity 0)) := by
  rw [forwardScalarOperator, kineticPositionGradient_scalar, kineticVelocityHessian_scalar]
  have ht : deriv (fun s => velocitySecondBarrier Lam v0 tau
      ⟨s, p.position, p.velocity⟩) p.time = -2*Lam := by
    apply HasDerivAt.deriv
    convert (hasDerivAt_const p.time ((p.velocity 0-v0)^2)).add
      (((hasDerivAt_const p.time tau).sub (hasDerivAt_id p.time)).const_mul
        (2*Lam)) using 1 <;>
      ((try funext s); (try dsimp [velocitySecondBarrier, positionSecondBarrier]); all_goals ring)
  have hx : deriv (fun x => velocitySecondBarrier Lam v0 tau
      ⟨p.time, fun _ => x, p.velocity⟩) (p.position 0) = 0 := by
    change deriv (fun _ : ℝ => (p.velocity 0-v0)^2+2*Lam*(tau-p.time)) _ = 0
    exact deriv_const _ _
  have hv : deriv (fun v => velocitySecondBarrier Lam v0 tau
      ⟨p.time, p.position, fun _ => v⟩) = fun v => 2*(v-v0) := by
    funext v
    apply HasDerivAt.deriv
    convert (((hasDerivAt_id v).sub_const v0).fun_pow 2).add_const
      (2*Lam*(tau-p.time)) using 1 <;>
      ((try funext s); (try dsimp [velocitySecondBarrier, positionSecondBarrier]); all_goals ring)
  rw [kineticTimeDerivative, ht, hx, hv]
  have hvv : deriv (fun v : ℝ => 2*(v-v0)) (p.velocity 0) = 2 := by
    simpa only [id_eq, mul_one] using
      (((hasDerivAt_id (p.velocity 0)).sub_const v0).const_mul 2).deriv
  rw [hvv]
  ring

/-- Exact quadratic position computation; transport cancels the time derivative. -/
theorem positionSecondBarrier_operator (a : ℝ → ℝ → ℝ) (Lam X0 tau : ℝ)
    (p : Point) :
    forwardScalarOperator a (positionSecondBarrier Lam X0 tau) p =
      -2*(Lam-a (p.position 0) (p.velocity 0))*(tau-p.time)^2 := by
  rw [forwardScalarOperator, kineticPositionGradient_scalar, kineticVelocityHessian_scalar]
  have ht : deriv (fun s => positionSecondBarrier Lam X0 tau
      ⟨s, p.position, p.velocity⟩) p.time =
      -2*(p.position 0-X0+(tau-p.time)*p.velocity 0)*p.velocity 0-
        2*Lam*(tau-p.time)^2 := by
    have hs := (hasDerivAt_const p.time tau).sub (hasDerivAt_id p.time)
    apply HasDerivAt.deriv
    convert ((hs.mul_const (p.velocity 0)).const_add (p.position 0-X0)).fun_pow 2 |>.add
      ((hs.fun_pow 3).const_mul ((2/3 : ℝ)*Lam)) using 1 <;>
      ((try funext s); (try dsimp [velocitySecondBarrier, positionSecondBarrier]); all_goals ring)
  have hx : deriv (fun x => positionSecondBarrier Lam X0 tau
      ⟨p.time, fun _ => x, p.velocity⟩) (p.position 0) =
      2*(p.position 0-X0+(tau-p.time)*p.velocity 0) := by
    apply HasDerivAt.deriv
    convert (((hasDerivAt_id (p.position 0)).sub_const X0).add_const
      ((tau-p.time)*p.velocity 0)).fun_pow 2 |>.add_const
        ((2/3 : ℝ)*Lam*(tau-p.time)^3) using 1 <;>
      ((try funext s); (try dsimp [velocitySecondBarrier, positionSecondBarrier]); all_goals ring)
  have hv : deriv (fun v => positionSecondBarrier Lam X0 tau
      ⟨p.time, p.position, fun _ => v⟩) =
      fun v => 2*(p.position 0-X0+(tau-p.time)*v)*(tau-p.time) := by
    funext v
    apply HasDerivAt.deriv
    convert (((hasDerivAt_id v).const_mul (tau-p.time)).const_add
      (p.position 0-X0)).fun_pow 2 |>.add_const
        ((2/3 : ℝ)*Lam*(tau-p.time)^3) using 1 <;>
      ((try funext s); (try dsimp [velocitySecondBarrier, positionSecondBarrier]); all_goals ring)
  have hvv : deriv (fun v => 2*(p.position 0-X0+(tau-p.time)*v)*(tau-p.time))
      (p.velocity 0) = 2*(tau-p.time)^2 := by
    apply HasDerivAt.deriv
    convert ((((hasDerivAt_id (p.velocity 0)).const_mul (tau-p.time)).const_add
      (p.position 0-X0)).const_mul 2).mul_const (tau-p.time) using 1 <;>
      ((try funext s); (try dsimp [velocitySecondBarrier, positionSecondBarrier]); all_goals ring)
  rw [kineticTimeDerivative, ht, hx, hv, hvv]
  ring

/-- The velocity polynomial is a supersolution under the pointwise upper bound. -/
theorem velocitySecondBarrier_operator_nonpos (a : ℝ → ℝ → ℝ)
    (Lam v0 tau : ℝ) (p : Point) (ha : a (p.position 0) (p.velocity 0) ≤ Lam) :
    forwardScalarOperator a (velocitySecondBarrier Lam v0 tau) p ≤ 0 := by
  rw [velocitySecondBarrier_operator]
  nlinarith only [ha]

/-- The position polynomial is a supersolution under the same upper bound. -/
theorem positionSecondBarrier_operator_nonpos (a : ℝ → ℝ → ℝ)
    (Lam X0 tau : ℝ) (p : Point) (ha : a (p.position 0) (p.velocity 0) ≤ Lam) :
    forwardScalarOperator a (positionSecondBarrier Lam X0 tau) p ≤ 0 := by
  rw [positionSecondBarrier_operator]
  exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)

/-- Starting-point quadratic velocity value has the exact source constant. -/
theorem velocitySecondBarrier_start (Lam X0 v0 T : ℝ) :
    velocitySecondBarrier Lam v0 T ⟨0, fun _ => X0, fun _ => v0⟩ = 2*Lam*T := by
  simp only [velocitySecondBarrier, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    zero_add, sub_zero]

/-- Starting-point quadratic position value has the integrated diffusion time power. -/
theorem positionSecondBarrier_start (Lam X0 v0 T : ℝ) :
    positionSecondBarrier Lam X0 T ⟨0, fun _ => X0, fun _ => v0⟩ =
      v0^2*T^2+(2/3 : ℝ)*Lam*T^3 := by
  simp only [positionSecondBarrier, sub_self, zero_add, sub_zero]
  ring

/-- Velocity second-moment barrier is nonnegative on its terminal past. -/
theorem velocitySecondBarrier_nonneg {Lam : ℝ} (hLam : 0 ≤ Lam)
    (v0 tau : ℝ) (p : Point) (ht : p.time ≤ tau) :
    0 ≤ velocitySecondBarrier Lam v0 tau p := by
  dsimp [velocitySecondBarrier]
  have hs := sub_nonneg.mpr ht
  positivity

/-- Position second-moment barrier is nonnegative on the same past. -/
theorem positionSecondBarrier_nonneg {Lam : ℝ} (hLam : 0 ≤ Lam)
    (X0 tau : ℝ) (p : Point) (ht : p.time ≤ tau) :
    0 ≤ positionSecondBarrier Lam X0 tau p := by
  dsimp [positionSecondBarrier]
  have hs := sub_nonneg.mpr ht
  positivity

/-- The sharper polynomial value implies the exact proposed position moment constant. -/
theorem positionSecondBarrier_start_le {Lam T : ℝ} (hLam : 0 ≤ Lam) (hT : 0 ≤ T)
    (X0 v0 : ℝ) :
    positionSecondBarrier Lam X0 T ⟨0, fun _ => X0, fun _ => v0⟩ ≤
      2*v0^2*T^2+(4/3 : ℝ)*Lam*T^3 := by
  rw [positionSecondBarrier_start]
  have h : 0 ≤ v0^2*T^2+(2/3 : ℝ)*Lam*T^3 := by positivity
  nlinarith only [h]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
