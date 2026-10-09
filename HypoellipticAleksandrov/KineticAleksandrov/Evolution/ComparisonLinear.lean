module

import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonCalculus

/-!
# Linearity of the viscous transported operator

The operator `L_ε` is linear on functions that are slice regular at the point
in the sense of `IsSliceRegularAt`.  These identities are used to apply the
maximum argument to differences of a solution and a barrier.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Filter Set Matrix
open scoped MatrixOrder Topology

/-- Additivity of the classical gradient. -/
theorem classicalGradient_add {n : ℕ} {g h : PDE.Vec n → ℝ} {x : PDE.Vec n}
    (hg : DifferentiableAt ℝ g x) (hh : DifferentiableAt ℝ h x) :
    PDE.classicalGradient (fun y => g y + h y) x =
      PDE.classicalGradient g x + PDE.classicalGradient h x := by
  ext i
  simp only [PDE.classicalGradient_apply, Pi.add_apply]
  rw [fderiv_fun_add hg hh]
  rfl

/-- Homogeneity of the classical gradient. -/
theorem classicalGradient_const_mul {n : ℕ} {g : PDE.Vec n → ℝ} {x : PDE.Vec n} (c : ℝ)
    (hg : DifferentiableAt ℝ g x) :
    PDE.classicalGradient (fun y => c * g y) x = c • PDE.classicalGradient g x := by
  ext i
  simp only [PDE.classicalGradient_apply, Pi.smul_apply, smul_eq_mul]
  rw [fderiv_const_mul hg]
  rfl

/-- Additivity of `sliceHessian` for `C²` functions. -/
theorem sliceHessian_add {n : ℕ} {g h : PDE.Vec n → ℝ} {x : PDE.Vec n}
    (hg : ContDiffAt ℝ 2 g x) (hh : ContDiffAt ℝ 2 h x) :
    sliceHessian (fun y => g y + h y) x = sliceHessian g x + sliceHessian h x := by
  have hgh : ContDiffAt ℝ 2 (fun y => g y + h y) x := hg.add hh
  have hdg : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdh : DifferentiableAt ℝ (fderiv ℝ h) x :=
    (hh.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  ext i j
  rw [sliceHessian_apply_eq_sndFDeriv hgh, Matrix.add_apply,
    sliceHessian_apply_eq_sndFDeriv hg, sliceHessian_apply_eq_sndFDeriv hh]
  have hev : fderiv ℝ (fun y => g y + h y) =ᶠ[𝓝 x]
      fun y => fderiv ℝ g y + fderiv ℝ h y := by
    filter_upwards [hg.eventually (by norm_num), hh.eventually (by norm_num)] with y hgy hhy
    exact fderiv_add (hgy.differentiableAt (by norm_num)) (hhy.differentiableAt (by norm_num))
  rw [hev.fderiv_eq, fderiv_fun_add hdg hdh]
  rfl

/-- Homogeneity of `sliceHessian` for `C²` functions. -/
theorem sliceHessian_const_mul {n : ℕ} {g : PDE.Vec n → ℝ} {x : PDE.Vec n} (c : ℝ)
    (hg : ContDiffAt ℝ 2 g x) :
    sliceHessian (fun y => c * g y) x = c • sliceHessian g x := by
  have hcg : ContDiffAt ℝ 2 (fun y => c * g y) x := contDiffAt_const.mul hg
  have hdg : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  ext i j
  rw [sliceHessian_apply_eq_sndFDeriv hcg, Matrix.smul_apply,
    sliceHessian_apply_eq_sndFDeriv hg]
  have hev : fderiv ℝ (fun y => c * g y) =ᶠ[𝓝 x] fun y => c • fderiv ℝ g y := by
    filter_upwards [hg.eventually (by norm_num)] with y hgy
    exact fderiv_const_mul (hgy.differentiableAt (by norm_num)) c
  rw [hev.fderiv_eq, fderiv_fun_const_smul hdg]
  simp

/-- Slice regularity is preserved by sums. -/
theorem IsSliceRegularAt.add {n : ℕ} {u v : KineticPoint n → ℝ} {p : KineticPoint n}
    (hu : IsSliceRegularAt u p) (hv : IsSliceRegularAt v p) :
    IsSliceRegularAt (fun q => u q + v q) p :=
  ⟨hu.time.add hv.time, hu.position.add hv.position, hu.velocity.add hv.velocity⟩

/-- Slice regularity is preserved by constant multiples. -/
theorem IsSliceRegularAt.const_mul {n : ℕ} {u : KineticPoint n → ℝ} {p : KineticPoint n}
    (c : ℝ) (hu : IsSliceRegularAt u p) :
    IsSliceRegularAt (fun q => c * u q) p :=
  ⟨hu.time.const_mul c, contDiffAt_const.mul hu.position, contDiffAt_const.mul hu.velocity⟩

/-- Slice regularity is preserved by differences. -/
theorem IsSliceRegularAt.sub {n : ℕ} {u v : KineticPoint n → ℝ} {p : KineticPoint n}
    (hu : IsSliceRegularAt u p) (hv : IsSliceRegularAt v p) :
    IsSliceRegularAt (fun q => u q - v q) p :=
  ⟨hu.time.sub hv.time, hu.position.sub hv.position, hu.velocity.sub hv.velocity⟩

/-- Slice regularity is preserved by negation. -/
theorem IsSliceRegularAt.neg {n : ℕ} {u : KineticPoint n → ℝ} {p : KineticPoint n}
    (hu : IsSliceRegularAt u p) : IsSliceRegularAt (fun q => -u q) p :=
  ⟨hu.time.neg, hu.position.neg, hu.velocity.neg⟩

/-- Constants are slice regular. -/
theorem IsSliceRegularAt.const {n : ℕ} (c : ℝ) (p : KineticPoint n) :
    IsSliceRegularAt (fun _ => c) p :=
  ⟨differentiableAt_const c, contDiffAt_const, contDiffAt_const⟩

/-- Additivity of `L_ε` at a slice-regular point. -/
theorem viscousTransportedOperator_add {n : ℕ} {B : FullKineticCoefficient n}
    {b : PDE.Vec n → PDE.Vec n} {ε : ℝ} {u v : KineticPoint n → ℝ} {p : KineticPoint n}
    (hu : IsSliceRegularAt u p) (hv : IsSliceRegularAt v p) :
    viscousTransportedOperator B b ε (fun q => u q + v q) p =
      viscousTransportedOperator B b ε u p + viscousTransportedOperator B b ε v p := by
  have ht : kineticTimeDerivative (fun q => u q + v q) p =
      kineticTimeDerivative u p + kineticTimeDerivative v p := by
    unfold kineticTimeDerivative
    exact deriv_fun_add hu.time hv.time
  have hpos : diffusedHessian (fun q => u q + v q) p =
      diffusedHessian u p + diffusedHessian v p := by
    simp only [diffusedHessian_eq_sliceHessian]
    exact sliceHessian_add hu.position hv.position
  have hvel : kineticVelocityGradient (fun q => u q + v q) p =
      kineticVelocityGradient u p + kineticVelocityGradient v p :=
    classicalGradient_add (hu.velocity.differentiableAt (by norm_num))
      (hv.velocity.differentiableAt (by norm_num))
  have hhess : kineticVelocityHessian (fun q => u q + v q) p =
      kineticVelocityHessian u p + kineticVelocityHessian v p := by
    simp only [kineticVelocityHessian_eq_sliceHessian]
    exact sliceHessian_add hu.velocity hv.velocity
  rw [viscousTransportedOperator_apply, viscousTransportedOperator_apply,
    viscousTransportedOperator_apply, transportedForwardOperator_apply,
    transportedForwardOperator_apply, transportedForwardOperator_apply, ht, hpos, hvel, hhess]
  simp only [matrixContraction_add_right, PDE.vecDot, Pi.add_apply, mul_add,
    Finset.sum_add_distrib, Matrix.add_apply]
  ring

/-- Homogeneity of `L_ε` at a slice-regular point. -/
theorem viscousTransportedOperator_const_mul {n : ℕ} {B : FullKineticCoefficient n}
    {b : PDE.Vec n → PDE.Vec n} {ε : ℝ} {u : KineticPoint n → ℝ} {p : KineticPoint n}
    (c : ℝ) (hu : IsSliceRegularAt u p) :
    viscousTransportedOperator B b ε (fun q => c * u q) p =
      c * viscousTransportedOperator B b ε u p := by
  have ht : kineticTimeDerivative (fun q => c * u q) p = c * kineticTimeDerivative u p := by
    unfold kineticTimeDerivative
    exact deriv_const_mul c hu.time
  have hpos : diffusedHessian (fun q => c * u q) p = c • diffusedHessian u p := by
    simp only [diffusedHessian_eq_sliceHessian]
    exact sliceHessian_const_mul c hu.position
  have hvel : kineticVelocityGradient (fun q => c * u q) p = c • kineticVelocityGradient u p :=
    classicalGradient_const_mul c (hu.velocity.differentiableAt (by norm_num))
  have hhess : kineticVelocityHessian (fun q => c * u q) p = c • kineticVelocityHessian u p := by
    simp only [kineticVelocityHessian_eq_sliceHessian]
    exact sliceHessian_const_mul c hu.velocity
  rw [viscousTransportedOperator_apply, viscousTransportedOperator_apply,
    transportedForwardOperator_apply, transportedForwardOperator_apply, ht, hpos, hvel, hhess]
  simp only [matrixContraction_smul_right, PDE.vecDot, Pi.smul_apply, smul_eq_mul,
    Matrix.smul_apply]
  have hs : ∑ i, b p.position i * (c * kineticVelocityGradient u p i) =
      c * ∑ i, b p.position i * kineticVelocityGradient u p i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hs2 : ∑ i, c * kineticVelocityHessian u p i i =
      c * ∑ i, kineticVelocityHessian u p i i := (Finset.mul_sum _ _ _).symm
  rw [hs, hs2]
  ring

end HypoellipticAleksandrov.KineticAleksandrov
