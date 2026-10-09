module

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonLinear
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Derivatives of radial functions

Functions of the form `y ↦ Ψ(|y - m|²)` of a native vector, together with their
gradients, Hessians, and the time derivative along a moving centre `m(σ)`.  Working with
the squared distance `|y - m|²` avoids square roots until the explicit barrier is
written down.  These formulas supply the growth barrier `Φ` of
Proposition 2.1 and the collar barrier `w(d)` of
Proposition 2.1.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov Filter Set Matrix
open scoped Topology

/-- The squared distance to a fixed centre has the expected derivative. -/
theorem hasFDerivAt_vecNormSq_sub {n : ℕ} (m x : PDE.Vec n) :
    HasFDerivAt (fun y : PDE.Vec n => PDE.vecNormSq (y - m))
      (∑ i, (2 * (x i - m i)) • (ContinuousLinearMap.proj i : PDE.Vec n →L[ℝ] ℝ)) x := by
  have hfun : (fun y : PDE.Vec n => PDE.vecNormSq (y - m)) =
      fun y => ∑ i, (y i - m i) ^ 2 := by
    funext y
    rw [PDE.vecNormSq_eq_sum_sq]
    rfl
  rw [hfun]
  apply HasFDerivAt.fun_sum
  intro i _
  have h1 : HasFDerivAt (fun y : PDE.Vec n => y i - m i)
      (ContinuousLinearMap.proj i : PDE.Vec n →L[ℝ] ℝ) x :=
    (hasFDerivAt_apply i x).sub_const (m i)
  have h2 := h1.pow 2
  convert h2 using 1
  simp

/-- Evaluation of the derivative of the squared distance on a basis vector. -/
theorem normSqGradCLM_apply_basisVec {n : ℕ} (m x : PDE.Vec n) (i : Fin n) :
    (∑ k, (2 * (x k - m k)) • (ContinuousLinearMap.proj k : PDE.Vec n →L[ℝ] ℝ))
      (PDE.basisVec i) = 2 * (x i - m i) := by
  simp [PDE.basisVec_apply]

/-- Gradient of a function of the squared distance. -/
theorem classicalGradient_comp_vecNormSq_sub {n : ℕ} {Ψ : ℝ → ℝ} {m x : PDE.Vec n}
    (hΨ : DifferentiableAt ℝ Ψ (PDE.vecNormSq (x - m))) :
    PDE.classicalGradient (fun y => Ψ (PDE.vecNormSq (y - m))) x =
      fun i => 2 * deriv Ψ (PDE.vecNormSq (x - m)) * (x i - m i) := by
  have h : HasFDerivAt (fun y => Ψ (PDE.vecNormSq (y - m)))
      (deriv Ψ (PDE.vecNormSq (x - m)) • (∑ i, (2 * (x i - m i)) •
        (ContinuousLinearMap.proj i : PDE.Vec n →L[ℝ] ℝ))) x :=
    hΨ.hasDerivAt.comp_hasFDerivAt x (hasFDerivAt_vecNormSq_sub m x)
  ext i
  rw [PDE.classicalGradient_apply, h.fderiv]
  simp only [_root_.smul_apply, normSqGradCLM_apply_basisVec, smul_eq_mul]
  ring

/-- Hessian of a function of the squared distance. -/
theorem sliceHessian_comp_vecNormSq_sub {n : ℕ} {Ψ : ℝ → ℝ} {m x : PDE.Vec n}
    (hΨ : ContDiffAt ℝ 2 Ψ (PDE.vecNormSq (x - m))) (i j : Fin n) :
    sliceHessian (fun y => Ψ (PDE.vecNormSq (y - m))) x i j =
      4 * deriv (deriv Ψ) (PDE.vecNormSq (x - m)) * (x i - m i) * (x j - m j) +
        (if i = j then 2 * deriv Ψ (PDE.vecNormSq (x - m)) else 0) := by
  set S : PDE.Vec n → ℝ := fun y => PDE.vecNormSq (y - m) with hS
  have hSc : Continuous S := by
    have : S = fun y => ∑ i, (y i - m i) ^ 2 := by
      funext y
      simp only [hS]
      rw [PDE.vecNormSq_eq_sum_sq]
      rfl
    rw [this]
    fun_prop
  have hSd : HasFDerivAt S
      (∑ i, (2 * (x i - m i)) • (ContinuousLinearMap.proj i : PDE.Vec n →L[ℝ] ℝ)) x :=
    hasFDerivAt_vecNormSq_sub m x
  have hΨev : ∀ᶠ s in 𝓝 (S x), ContDiffAt ℝ 2 Ψ s := hΨ.eventually (by norm_num)
  have hev : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 Ψ (S y) := hSc.continuousAt.eventually hΨev
  have hΨ2 : HasDerivAt (deriv Ψ) (deriv (deriv Ψ) (S x)) (S x) := by
    have h1 : ContDiffAt ℝ 1 (fun s => fderiv ℝ Ψ s 1) (S x) :=
      (hΨ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
    exact (h1.differentiableAt (by norm_num)).hasDerivAt
  have hgrad : (fun y => PDE.classicalGradient (fun y => Ψ (S y)) y) =ᶠ[𝓝 x]
      fun y => fun k => 2 * deriv Ψ (S y) * (y k - m k) := by
    filter_upwards [hev] with y hy
    exact classicalGradient_comp_vecNormSq_sub (hy.differentiableAt (by norm_num))
  have hfj : ∀ k : Fin n, ∃ L : PDE.Vec n →L[ℝ] ℝ,
      HasFDerivAt (fun y : PDE.Vec n => 2 * deriv Ψ (S y) * (y k - m k)) L x ∧
        ∀ i : Fin n, L (PDE.basisVec i) =
          4 * deriv (deriv Ψ) (S x) * (x i - m i) * (x k - m k) +
            (if i = k then 2 * deriv Ψ (S x) else 0) := by
    intro k
    have h1 := hΨ2.comp_hasFDerivAt x hSd
    have h2 : HasFDerivAt (fun y : PDE.Vec n => y k - m k)
        (ContinuousLinearMap.proj k : PDE.Vec n →L[ℝ] ℝ) x :=
      (hasFDerivAt_apply k x).sub_const (m k)
    have h3 := (h1.const_mul 2).mul h2
    refine ⟨_, h3, ?_⟩
    intro i
    simp only [_root_.add_apply, _root_.smul_apply, normSqGradCLM_apply_basisVec, smul_eq_mul,
      ContinuousLinearMap.proj_apply, PDE.basisVec_apply]
    by_cases h : i = k
    · subst h; simp; ring
    · have h' : k ≠ i := fun e => h e.symm
      simp [h, h']; ring
  choose L hL hLe using hfj
  have hdiff : ∀ k : Fin n, DifferentiableAt ℝ
      (fun y : PDE.Vec n => 2 * deriv Ψ (S y) * (y k - m k)) x :=
    fun k => (hL k).differentiableAt
  unfold sliceHessian
  rw [hgrad.fderiv_eq]
  rw [fderiv_pi hdiff]
  simp only [ContinuousLinearMap.pi_apply]
  rw [(hL j).fderiv, hLe j i]

/-- Contraction of a matrix with the Hessian of a function of the squared distance. -/
theorem matrixContraction_sliceHessian_comp_vecNormSq_sub {n : ℕ} {Ψ : ℝ → ℝ}
    {m x : PDE.Vec n} (hΨ : ContDiffAt ℝ 2 Ψ (PDE.vecNormSq (x - m))) (A : PDE.Mat n) :
    matrixContraction A (sliceHessian (fun y => Ψ (PDE.vecNormSq (y - m))) x) =
      4 * deriv (deriv Ψ) (PDE.vecNormSq (x - m)) * dotProduct (x - m) (A.mulVec (x - m)) +
        2 * deriv Ψ (PDE.vecNormSq (x - m)) * A.trace := by
  unfold matrixContraction
  simp_rw [sliceHessian_comp_vecNormSq_sub hΨ]
  simp only [mul_add, Finset.sum_add_distrib]
  congr 1
  · simp only [dotProduct, Matrix.mulVec, Pi.sub_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    ring
  · simp only [Matrix.trace, Matrix.diag, mul_ite, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
    rw [Finset.sum_congr rfl (fun i _ => by ring : ∀ i ∈ Finset.univ,
      A i i * (2 * deriv Ψ (PDE.vecNormSq (x - m))) =
        2 * deriv Ψ (PDE.vecNormSq (x - m)) * A i i)]
    rw [← Finset.mul_sum]

/-- The Laplacian of a function of the squared distance. -/
theorem sum_diag_sliceHessian_comp_vecNormSq_sub {n : ℕ} {Ψ : ℝ → ℝ} {m x : PDE.Vec n}
    (hΨ : ContDiffAt ℝ 2 Ψ (PDE.vecNormSq (x - m))) :
    ∑ i, sliceHessian (fun y => Ψ (PDE.vecNormSq (y - m))) x i i =
      4 * deriv (deriv Ψ) (PDE.vecNormSq (x - m)) * PDE.vecNormSq (x - m) +
        2 * n * deriv Ψ (PDE.vecNormSq (x - m)) := by
  simp_rw [sliceHessian_comp_vecNormSq_sub hΨ]
  simp only [ite_true, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [PDE.vecNormSq_eq_sum_sq, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [Pi.sub_apply]
    ring
  · ring

/-- Time derivative of a function of the squared distance to a moving centre. -/
theorem hasDerivAt_comp_vecNormSq_sub_moving {n : ℕ} {Ψ : ℝ → ℝ} {m : ℝ → PDE.Vec n}
    {m' : PDE.Vec n} {σ : ℝ} (y : PDE.Vec n) (hm : HasDerivAt m m' σ)
    (hΨ : DifferentiableAt ℝ Ψ (PDE.vecNormSq (y - m σ))) :
    HasDerivAt (fun t => Ψ (PDE.vecNormSq (y - m t)))
      (deriv Ψ (PDE.vecNormSq (y - m σ)) * (-2 * ∑ i, (y i - m σ i) * m' i)) σ := by
  have hi : ∀ i : Fin n, HasDerivAt (fun t => (y i - m t i) ^ 2)
      (2 * (y i - m σ i) * (-(m' i))) σ := by
    intro i
    have h1 : HasDerivAt (fun t => m t i) (m' i) σ := (hasDerivAt_pi.1 hm) i
    have h2 := (h1.const_sub (y i)).pow 2
    convert h2 using 1
    norm_num
  have hsum : HasDerivAt (fun t => PDE.vecNormSq (y - m t))
      (∑ i, 2 * (y i - m σ i) * (-(m' i))) σ := by
    have hfun : (fun t => PDE.vecNormSq (y - m t)) = fun t => ∑ i, (y i - m t i) ^ 2 := by
      funext t
      rw [PDE.vecNormSq_eq_sum_sq]
      rfl
    rw [hfun]
    exact HasDerivAt.fun_sum (fun i _ => hi i)
  have h : HasDerivAt (fun t => Ψ (PDE.vecNormSq (y - m t)))
      (deriv Ψ (PDE.vecNormSq (y - m σ)) * ∑ i, 2 * (y i - m σ i) * -m' i) σ :=
    hΨ.hasDerivAt.comp σ hsum
  have e : (-2 * ∑ i, (y i - m σ i) * m' i) = ∑ i, 2 * (y i - m σ i) * -m' i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [e]
  exact h

end HypoellipticAleksandrov.KineticAleksandrov
