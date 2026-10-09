module

public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyProjection

/-!
# Transported parabolic Morrey projection moments

This module transports the unit forward-box velocity moments to
positive-radius physical forward boxes.  It records only the exact constant,
centered-coordinate, and centered second-moment identities, together with the
physical velocity-slope normalization on centered affine fields.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open scoped BigOperators

/-- The transported average of the constant one on a positive-radius forward box. -/
theorem parabolicMorreyBoxAverage_one
    {d : Nat} (t₀ : Real) (v₀ : PDE.Vec d) {r : Real} (hr : 0 < r) :
    parabolicMorreyBoxAverage t₀ v₀ r
      (fun _ : TimeVelocity d => (1 : Real)) = 1 := by
  have _ : r ≠ 0 := hr.ne'
  simpa only [parabolicMorreyBoxAverage, pullbackScalar, Function.comp_def] using
    parabolicMorreyUnitAverage_one d

/-- Every centered physical velocity coordinate has zero transported average. -/
theorem parabolicMorreyBoxAverage_centeredVelocity
    {d : Nat} (t₀ : Real) (v₀ : PDE.Vec d) {r : Real} (hr : 0 < r)
    (i : Fin d) :
    parabolicMorreyBoxAverage t₀ v₀ r
      (fun z : TimeVelocity d => z.2 i - v₀ i) = 0 := by
  have _ : r ≠ 0 := hr.ne'
  change parabolicMorreyUnitAverage
    (fun z : TimeVelocity d => (v₀ + r • z.2) i - v₀ i) = 0
  have hpullback : (fun z : TimeVelocity d => (v₀ + r • z.2) i - v₀ i) =
      r • (fun z : TimeVelocity d => z.2 i) := by
    funext z
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hpullback, parabolicMorreyUnitAverage_smul,
    parabolicMorreyUnitAverage_velocity]
  simp only [smul_eq_mul, mul_zero]

/-- The centered physical velocity covariance is diagonal with entry `r^2 / 3`. -/
theorem parabolicMorreyBoxAverage_centeredVelocity_mul_centeredVelocity
    {d : Nat} (t₀ : Real) (v₀ : PDE.Vec d) {r : Real} (hr : 0 < r)
    (i j : Fin d) :
    parabolicMorreyBoxAverage t₀ v₀ r
      (fun z : TimeVelocity d => (z.2 i - v₀ i) * (z.2 j - v₀ j)) =
        if i = j then r ^ 2 / 3 else 0 := by
  have _ : r ≠ 0 := hr.ne'
  change parabolicMorreyUnitAverage (fun z : TimeVelocity d =>
    ((v₀ + r • z.2) i - v₀ i) * ((v₀ + r • z.2) j - v₀ j)) = _
  have hpullback : (fun z : TimeVelocity d =>
      ((v₀ + r • z.2) i - v₀ i) * ((v₀ + r • z.2) j - v₀ j)) =
      r ^ 2 • (fun z : TimeVelocity d => z.2 i * z.2 j) := by
    funext z
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hpullback, parabolicMorreyUnitAverage_smul,
    parabolicMorreyUnitAverage_velocity_mul_velocity]
  by_cases hij : i = j
  · simp only [hij, ite_true, smul_eq_mul]
    ring
  · simp only [hij, ite_false, smul_eq_mul, mul_zero]

/-- The dimensional physical slope extracts the coefficient of a centered
velocity-affine field. -/
theorem parabolicMorreyBoxVelocitySlope_centered_affine
    {d : Nat} (t₀ : Real) (v₀ : PDE.Vec d) {r : Real} (hr : 0 < r)
    (a : Real) (b : Fin d -> Real) (j : Fin d) :
    parabolicMorreyBoxVelocitySlope t₀ v₀ r
      (fun z : TimeVelocity d => a +
        ∑ i : Fin d, b i * (z.2 i - v₀ i)) j = b j := by
  change r⁻¹ * parabolicMorreyUnitVelocityCoeff
    (fun z : TimeVelocity d => a +
      ∑ i : Fin d, b i * ((v₀ + r • z.2) i - v₀ i)) j = b j
  let f : TimeVelocity d → Real := fun z => a +
    ∑ i : Fin d, (r * b i) * z.2 i
  have hpullback : (fun z : TimeVelocity d => a +
      ∑ i : Fin d, b i * ((v₀ + r • z.2) i - v₀ i)) = f := by
    funext z
    simp only [f, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hpullback]
  have hprojection : parabolicMorreyUnitAffineProjection f = f := by
    simpa only [f] using
      (parabolicMorreyUnitAffineProjection_reproduces_velocity_affine a
        (fun i => r * b i))
  have havg : parabolicMorreyUnitAverage f = a := by
    have hzero := congrFun hprojection (0, 0)
    simpa only [parabolicMorreyUnitAffineProjection, Pi.zero_apply, mul_zero,
      Finset.sum_const_zero, add_zero, f] using hzero
  let e : PDE.Vec d := fun i => if i = j then 1 else 0
  have hsumCoeff : ∑ i : Fin d, parabolicMorreyUnitVelocityCoeff f i * e i =
      parabolicMorreyUnitVelocityCoeff f j := by
    simp only [e, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
  have hsumAffine : ∑ i : Fin d, (r * b i) * e i = r * b j := by
    simp only [e, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
  have he := congrFun hprojection (0, e)
  have heq : parabolicMorreyUnitAverage f +
      ∑ i : Fin d, parabolicMorreyUnitVelocityCoeff f i * e i =
      a + ∑ i : Fin d, (r * b i) * e i := by
    simpa only [parabolicMorreyUnitAffineProjection, f] using he
  rw [hsumCoeff, hsumAffine, havg] at heq
  have hcoeff : parabolicMorreyUnitVelocityCoeff f j = r * b j := by
    linarith
  calc
    r⁻¹ * parabolicMorreyUnitVelocityCoeff f j = (r⁻¹ * r) * b j := by
      rw [hcoeff]
      ring
    _ = b j := by rw [inv_mul_cancel₀ hr.ne', one_mul]

end HypoellipticAleksandrov.Parabolic
