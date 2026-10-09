module

import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonRadial
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonMoving

/-!
# The growth barrier

The function `Φ(σ, y, z) = exp (C (T - σ)) (1 + |y|² + |z|²)` and the computation of
`L_ε Φ` for the viscous transported operator.  For the explicit constant
`C = 2 n (|Λ| + 1) + |b 0| + |L_b| + 1`, one has `L_ε Φ ≤ -Φ` for every
`0 ≤ ε ≤ 1`.  This is the Lyapunov inequality of Proposition 2.1,
here in absolute coordinates, where no derivative of the moving boundary enters.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Filter Set Matrix
open scoped Topology MatrixOrder

/-- The growth barrier `Φ(σ, y, z) = exp (C (T - σ)) (1 + |y|² + |z|²)`. -/
def growthBarrier {n : ℕ} (C T : ℝ) (p : KineticPoint n) : ℝ :=
  Real.exp (C * (T - p.time)) * (1 + radialSq p)

/-- The explicit growth constant, depending only on `d`, `Λ`, `|b 0|` and `L_b`. -/
def growthConstant (n : ℕ) (Lam b0 Lb : ℝ) : ℝ :=
  2 * n * (|Lam| + 1) + b0 + |Lb| + 1

/-- The growth barrier is positive. -/
theorem growthBarrier_pos {n : ℕ} (C T : ℝ) (p : KineticPoint n) :
    0 < growthBarrier C T p := by
  unfold growthBarrier
  have : 0 ≤ radialSq p := add_nonneg (PDE.vecNormSq_nonneg _) (PDE.vecNormSq_nonneg _)
  positivity

/-- The growth barrier dominates `1 + |y|² + |z|²` for `σ ≤ T`. -/
theorem one_add_radialSq_le_growthBarrier {n : ℕ} {C T : ℝ} (hC : 0 ≤ C) {p : KineticPoint n}
    (hp : p.time ≤ T) : 1 + radialSq p ≤ growthBarrier C T p := by
  unfold growthBarrier
  have h1 : 1 ≤ Real.exp (C * (T - p.time)) := by
    apply Real.one_le_exp
    exact mul_nonneg hC (sub_nonneg.mpr hp)
  have h2 : 0 ≤ 1 + radialSq p := by
    have : 0 ≤ radialSq p := add_nonneg (PDE.vecNormSq_nonneg _) (PDE.vecNormSq_nonneg _)
    linarith
  nlinarith

/-- Derivative of an affine function of the squared distance. -/
theorem deriv_affine_weight (c a : ℝ) :
    deriv (fun s : ℝ => c * (a + s)) = fun _ => c := by
  funext s
  have h : HasDerivAt (fun s : ℝ => c * (a + s)) c s := by
    have := ((hasDerivAt_id s).const_add a).const_mul c
    simpa using this
  exact h.deriv

/-- The squared distance to a fixed point is smooth. -/
theorem contDiff_vecNormSq_sub {n : ℕ} (m : PDE.Vec n) :
    ContDiff ℝ 2 (fun y : PDE.Vec n => PDE.vecNormSq (y - m)) := by
  have : (fun y : PDE.Vec n => PDE.vecNormSq (y - m)) = fun y => ∑ i, (y i - m i) ^ 2 := by
    funext y
    rw [PDE.vecNormSq_eq_sum_sq]
    rfl
  rw [this]
  exact ContDiff.sum fun i _ => ((contDiff_apply ℝ ℝ i).sub contDiff_const).pow 2

/-- The growth barrier is slice regular everywhere. -/
theorem isSliceRegularAt_growthBarrier {n : ℕ} (C T : ℝ) (p : KineticPoint n) :
    IsSliceRegularAt (growthBarrier C T) p := by
  have hpos : ContDiff ℝ 2 (fun y : PDE.Vec n => PDE.vecNormSq y) := by
    simpa using contDiff_vecNormSq_sub (0 : PDE.Vec n)
  refine ⟨?_, ?_, ?_⟩
  · have : DifferentiableAt ℝ (fun t : ℝ => Real.exp (C * (T - t)) * (1 + radialSq p)) p.time := by
      fun_prop
    exact this
  · have h : ContDiff ℝ 2 (fun y : PDE.Vec n =>
        Real.exp (C * (T - p.time)) * (1 + (PDE.vecNormSq y + PDE.vecNormSq p.velocity))) :=
      contDiff_const.mul (contDiff_const.add (hpos.add contDiff_const))
    exact h.contDiffAt
  · have h : ContDiff ℝ 2 (fun z : PDE.Vec n =>
        Real.exp (C * (T - p.time)) * (1 + (PDE.vecNormSq p.position + PDE.vecNormSq z))) :=
      contDiff_const.mul (contDiff_const.add (contDiff_const.add hpos))
    exact h.contDiffAt

/-- The time derivative of the growth barrier. -/
theorem kineticTimeDerivative_growthBarrier {n : ℕ} (C T : ℝ) (p : KineticPoint n) :
    kineticTimeDerivative (growthBarrier C T) p =
      Real.exp (C * (T - p.time)) * (-C * (1 + radialSq p)) := by
  show deriv (fun r : ℝ => Real.exp (C * (T - r)) * (1 + radialSq p)) p.time = _
  have h1 : HasDerivAt (fun r : ℝ => C * (T - r)) (C * (-1)) p.time :=
    ((hasDerivAt_id p.time).const_sub T).const_mul C
  have h2 := (h1.exp).mul_const (1 + radialSq p)
  rw [h2.deriv]
  ring

/-- The `y`-slice of the growth barrier, as a function of `|y|²`. -/
theorem growthBarrier_positionSlice {n : ℕ} (C T : ℝ) (p : KineticPoint n) :
    (fun y : PDE.Vec n => growthBarrier C T ⟨p.time, y, p.velocity⟩) =
      fun y => (fun s : ℝ => Real.exp (C * (T - p.time)) *
        ((1 + PDE.vecNormSq p.velocity) + s)) (PDE.vecNormSq (y - 0)) := by
  funext y
  simp only [growthBarrier, radialSq, sub_zero]
  ring

/-- The `z`-slice of the growth barrier, as a function of `|z|²`. -/
theorem growthBarrier_velocitySlice {n : ℕ} (C T : ℝ) (p : KineticPoint n) :
    (fun z : PDE.Vec n => growthBarrier C T ⟨p.time, p.position, z⟩) =
      fun z => (fun s : ℝ => Real.exp (C * (T - p.time)) *
        ((1 + PDE.vecNormSq p.position) + s)) (PDE.vecNormSq (z - 0)) := by
  funext z
  simp only [growthBarrier, radialSq, sub_zero]
  ring

/-- Affine functions are smooth. -/
theorem contDiffAt_affine_weight (c a s : ℝ) :
    ContDiffAt ℝ 2 (fun s : ℝ => c * (a + s)) s :=
  (contDiff_const.mul (contDiff_const.add contDiff_id)).contDiffAt

/-- The viscous operator applied to the growth barrier. -/
theorem viscousTransportedOperator_growthBarrier {n : ℕ} (B : FullKineticCoefficient n)
    (b : PDE.Vec n → PDE.Vec n) (ε C T : ℝ) (p : KineticPoint n) :
    viscousTransportedOperator B b ε (growthBarrier C T) p =
      Real.exp (C * (T - p.time)) *
        (-C * (1 + radialSq p) + 2 * (B p.time p.position p.velocity).trace +
          2 * PDE.vecDot (b p.position) p.velocity + 2 * ε * n) := by
  set E := Real.exp (C * (T - p.time)) with hE
  have hdiff : matrixContraction (B p.time p.position p.velocity) (diffusedHessian
      (growthBarrier C T) p) = 2 * E * (B p.time p.position p.velocity).trace := by
    rw [diffusedHessian_eq_sliceHessian, growthBarrier_positionSlice,
      matrixContraction_sliceHessian_comp_vecNormSq_sub
        (contDiffAt_affine_weight E (1 + PDE.vecNormSq p.velocity) _),
      deriv_affine_weight, deriv_const']
    simp
  have hgrad : kineticVelocityGradient (growthBarrier C T) p =
      fun i => 2 * E * (p.velocity i - (0 : PDE.Vec n) i) := by
    show PDE.classicalGradient (fun z : PDE.Vec n => growthBarrier C T ⟨p.time, p.position, z⟩)
      p.velocity = _
    rw [growthBarrier_velocitySlice,
      classicalGradient_comp_vecNormSq_sub
        ((contDiffAt_affine_weight E (1 + PDE.vecNormSq p.position) _).differentiableAt
          (by norm_num)),
      deriv_affine_weight]
  have hlap : ∑ i, kineticVelocityHessian (growthBarrier C T) p i i = 2 * n * E := by
    rw [kineticVelocityHessian_eq_sliceHessian, growthBarrier_velocitySlice,
      sum_diag_sliceHessian_comp_vecNormSq_sub
        (contDiffAt_affine_weight E (1 + PDE.vecNormSq p.position) _),
      deriv_affine_weight, deriv_const']
    simp
  rw [viscousTransportedOperator_apply, transportedForwardOperator_apply]
  simp only [fullKineticCoefficientAt_apply]
  rw [kineticTimeDerivative_growthBarrier, hdiff, hgrad, hlap]
  have hdot : PDE.vecDot (b p.position) (fun i => 2 * E * (p.velocity i - (0 : PDE.Vec n) i)) =
      2 * E * PDE.vecDot (b p.position) p.velocity := by
    unfold PDE.vecDot
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by simp; ring)
  rw [hdot]
  ring

/-- Linear growth of a Lipschitz drift in the Euclidean norm. -/
theorem vecEuclideanNorm_le_of_lipschitz {n : ℕ} {b : PDE.Vec n → PDE.Vec n} {Lb : ℝ}
    (hb : ∀ y y', PDE.vecEuclideanNorm (b y - b y') ≤ Lb * PDE.vecEuclideanNorm (y - y'))
    (y : PDE.Vec n) :
    PDE.vecEuclideanNorm (b y) ≤ PDE.vecEuclideanNorm (b 0) + |Lb| * PDE.vecEuclideanNorm y := by
  have h1 := hb y 0
  have h2 : PDE.vecEuclideanNorm (b y) ≤
      PDE.vecEuclideanNorm (b y - b 0) + PDE.vecEuclideanNorm (b 0) := by
    have := PDE.vecEuclideanNorm_add_le (b y - b 0) (b 0)
    simpa using this
  have h3 : Lb * PDE.vecEuclideanNorm (y - 0) ≤ |Lb| * PDE.vecEuclideanNorm y := by
    rw [sub_zero]
    exact mul_le_mul_of_nonneg_right (le_abs_self Lb) (PDE.vecEuclideanNorm_nonneg _)
  linarith

/-- The trace of a matrix bounded above by `Λ I` is at most `n Λ`. -/
theorem trace_le_of_le_smul_one {n : ℕ} {A : PDE.Mat n} {Lam : ℝ}
    (h : A ≤ Lam • (1 : PDE.Mat n)) : A.trace ≤ n * Lam := by
  have h1 : (Lam • (1 : PDE.Mat n) - A).PosSemidef := Matrix.le_iff.mp h
  have h2 := h1.trace_nonneg
  rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one] at h2
  simp only [Fintype.card_fin, smul_eq_mul] at h2
  linarith

/-- The Lyapunov inequality `L_ε Φ ≤ -Φ` for the growth barrier with the explicit
constant, for every `0 ≤ ε ≤ 1`, at every kinetic point. -/
theorem viscousTransportedOperator_growthBarrier_le {n : ℕ} {B : FullKineticCoefficient n}
    {b : PDE.Vec n → PDE.Vec n} {ε Lam Lb : ℝ} (hε1 : ε ≤ 1)
    (hBLam : ∀ σ y z, B σ y z ≤ Lam • (1 : PDE.Mat n))
    (hb : ∀ y y', PDE.vecEuclideanNorm (b y - b y') ≤ Lb * PDE.vecEuclideanNorm (y - y'))
    (T : ℝ) (p : KineticPoint n) :
    viscousTransportedOperator B b ε
        (growthBarrier (growthConstant n Lam (PDE.vecEuclideanNorm (b 0)) Lb) T) p ≤
      -growthBarrier (growthConstant n Lam (PDE.vecEuclideanNorm (b 0)) Lb) T p := by
  rw [viscousTransportedOperator_growthBarrier]
  unfold growthBarrier growthConstant
  set E := Real.exp (growthConstant n Lam (PDE.vecEuclideanNorm (b 0)) Lb * (T - p.time)) with hE
  unfold growthConstant at hE
  have hEpos : 0 < E := Real.exp_pos _
  set b0 := PDE.vecEuclideanNorm (b 0) with hb0
  have hb0nn : 0 ≤ b0 := PDE.vecEuclideanNorm_nonneg _
  have htr := trace_le_of_le_smul_one (hBLam p.time p.position p.velocity)
  have hs := PDE.vecEuclideanNorm_sq p.position
  have hr := PDE.vecEuclideanNorm_sq p.velocity
  set s := PDE.vecEuclideanNorm p.position
  set r := PDE.vecEuclideanNorm p.velocity
  have hsn : 0 ≤ s := PDE.vecEuclideanNorm_nonneg _
  have hrn : 0 ≤ r := PDE.vecEuclideanNorm_nonneg _
  have hdot : PDE.vecDot (b p.position) p.velocity ≤ (b0 + |Lb| * s) * r := by
    calc PDE.vecDot (b p.position) p.velocity ≤ |PDE.vecDot (b p.position) p.velocity| :=
          le_abs_self _
      _ ≤ PDE.vecEuclideanNorm (b p.position) * r := PDE.abs_vecDot_le_vecEuclideanNorm_mul _ _
      _ ≤ (b0 + |Lb| * s) * r :=
          mul_le_mul_of_nonneg_right (vecEuclideanNorm_le_of_lipschitz hb _) hrn
  have hLn : 0 ≤ |Lb| := abs_nonneg _
  have hq : 1 ≤ 1 + radialSq p := by
    have : 0 ≤ radialSq p := add_nonneg (PDE.vecNormSq_nonneg _) (PDE.vecNormSq_nonneg _)
    linarith
  have hradial : radialSq p = s ^ 2 + r ^ 2 := by
    unfold radialSq
    rw [← hs, ← hr]
  have hcross : 2 * ((b0 + |Lb| * s) * r) ≤ (b0 + |Lb|) * (1 + radialSq p) := by
    rw [hradial]
    have h1 : 0 ≤ b0 * (r - 1) ^ 2 := mul_nonneg hb0nn (sq_nonneg _)
    have h2 : 0 ≤ |Lb| * (s - r) ^ 2 := mul_nonneg hLn (sq_nonneg _)
    nlinarith [h1, h2]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hLamabs : Lam ≤ |Lam| := le_abs_self Lam
  have hpart : 2 * (B p.time p.position p.velocity).trace + 2 * ε * n ≤
      2 * n * (|Lam| + 1) * (1 + radialSq p) := by
    have h1 : 2 * (B p.time p.position p.velocity).trace ≤ 2 * (n * |Lam|) := by
      have : n * Lam ≤ n * |Lam| := mul_le_mul_of_nonneg_left hLamabs hn
      linarith
    have h2 : 2 * ε * n ≤ 2 * n := by nlinarith
    have h3 : 2 * n * (|Lam| + 1) ≤ 2 * n * (|Lam| + 1) * (1 + radialSq p) := by
      have : 0 ≤ 2 * n * (|Lam| + 1) := by positivity
      nlinarith
    nlinarith
  have hkey : -(2 * n * (|Lam| + 1) + b0 + |Lb| + 1) * (1 + radialSq p) +
      2 * (B p.time p.position p.velocity).trace +
        2 * PDE.vecDot (b p.position) p.velocity + 2 * ε * n ≤ -(1 + radialSq p) := by
    nlinarith
  calc E * (-(2 * n * (|Lam| + 1) + b0 + |Lb| + 1) * (1 + radialSq p) +
        2 * (B p.time p.position p.velocity).trace +
          2 * PDE.vecDot (b p.position) p.velocity + 2 * ε * n)
      ≤ E * (-(1 + radialSq p)) := mul_le_mul_of_nonneg_left hkey hEpos.le
    _ = -(E * (1 + radialSq p)) := by ring

end HypoellipticAleksandrov.KineticAleksandrov
