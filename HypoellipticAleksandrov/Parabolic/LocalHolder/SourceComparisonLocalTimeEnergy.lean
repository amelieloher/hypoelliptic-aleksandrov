module

public import HypoellipticAleksandrov.Parabolic.HarnackUnitCylinder.TimeWeakDerivative
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! # Local value energy for anisotropic classical solutions

The square testing identity uses only the actual continuous time derivative. No mixed
time--space derivative or smoothness of the solution is required.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open MeasureTheory Set

/-- Squaring a classical scalar solution gives its literal weak time derivative. -/
theorem hasWeakTimeDerivOn_square_of_scalarC12 {d : ℕ}
    {U : Set (TimeVelocity d)} {u : TimeVelocity d → ℝ}
    (hu : IsScalarC12On u U) :
    HasWeakTimeDerivOn U (fun z => u z ^ 2)
      (fun z => 2 * u z * scalarTimeDerivative u z) := by
  intro φ hφ hc hsub
  apply setIntegral_mul_directional_test (hu.continuousOn.pow 2)
    ((continuousOn_const.mul hu.continuousOn).mul hu.continuousOn_scalarTimeDerivative)
    (1, 0) ?_ hφ hc hsub
  intro z hz
  unfold HasLineDerivAt
  have hs := ((hu.timeSlice_hasDerivAt hz).pow 2).comp_of_eq 0
    ((hasDerivAt_const 0 z.1).add (hasDerivAt_id 0)) (by simp)
  convert hs using 1
  · funext t
    change u (z + t • (1, 0)) ^ 2 = u (z.1 + t, z.2) ^ 2
    have hp : z + t • ((1, 0) : TimeVelocity d) = (z.1 + t, z.2) := by
      ext <;> simp
    exact congrArg (fun p => u p ^ 2) hp
  · simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, Pi.mul_apply,
      zero_add, mul_one, Prod.mk.eta]

/-- The local quadratic time-energy identity holds against every smooth compact cutoff. -/
theorem integral_square_mul_timeDerivative_eq {d : ℕ}
    {U : Set (TimeVelocity d)} {u : TimeVelocity d → ℝ}
    (hu : IsScalarC12On u U) (χ : TimeVelocity d → ℝ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hsub : tsupport χ ⊆ U) :
    (∫ z in U, u z ^ 2 * timeDerivative χ z) =
      -(∫ z in U, 2 * u z * scalarTimeDerivative u z * χ z) :=
  hasWeakTimeDerivOn_square_of_scalarC12 hu χ hχ hc hsub

end HypoellipticAleksandrov.Parabolic.LocalHolder
