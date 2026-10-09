module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.SkeletonApproximation
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Linear
import PDEFoundation.Ambient.HilbertVec
import Mathlib.Tactic

/-! # The exact Euclidean acceleration and Young bounds for the source Gaussian -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Filter
open scoped Topology

/-- A smooth Euclidean Lipschitz velocity has the same Euclidean acceleration bound. -/
theorem vecEuclideanNorm_deriv_le {d : ℕ} {v : ℝ → PDE.Vec d} {H : ℝ}
    (hH : 0 ≤ H) (hv : Differentiable ℝ v)
    (hLip : ∀ s t, PDE.vecEuclideanNorm (v s - v t) ≤ H * |s - t|) (s : ℝ) :
    PDE.vecEuclideanNorm (deriv v s) ≤ H := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  have he : HasDerivAt (fun t => e (v t)) (e (deriv v s)) s :=
    e.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt s (hv s).hasDerivAt
  have hb : ∀ᶠ t in 𝓝 s, ‖e (v t) - e (v s)‖ ≤ H * ‖t - s‖ := by
    exact Eventually.of_forall fun t => by
      rw [← map_sub, Real.norm_eq_abs]
      change ‖(v t - v s).toHilbertVec‖ ≤ H * |t - s|
      rw [← PDE.Vec.vecEuclideanNorm_eq_norm_toHilbertVec]
      exact hLip t s
  have hnorm := norm_deriv_le_of_lip' hH hb
  rw [he.deriv] at hnorm
  rw [PDE.Vec.vecEuclideanNorm_eq_norm_toHilbertVec]
  exact hnorm

/-- Young's inequality with exactly the source coefficient `3 lam / 2`. -/
theorem acceleration_young {d : ℕ} {lam H : ℝ} (hlam : 0 < lam)
    (a p : PDE.Vec d) (ha : PDE.vecEuclideanNorm a ≤ H) :
    2 * PDE.vecDot a p ≤ (3 * lam / 2) * PDE.vecNormSq p + 2 * H ^ 2 / (3 * lam) := by
  have hdot := (le_abs_self (PDE.vecDot a p)).trans
    ((PDE.abs_vecDot_le_vecEuclideanNorm_mul a p).trans
      (mul_le_mul_of_nonneg_right ha (PDE.vecEuclideanNorm_nonneg p)))
  have hr := PDE.vecEuclideanNorm_sq p
  have hden : 0 < 3 * lam := by positivity
  have hy : 2 * H * PDE.vecEuclideanNorm p ≤
      (3 * lam / 2) * PDE.vecNormSq p + 2 * H ^ 2 / (3 * lam) := by
    apply (mul_le_mul_iff_right₀ hden).mp
    have hcancel : (3 * lam) * (2 * H ^ 2 / (3 * lam)) = 2 * H ^ 2 := by
      field_simp
    rw [mul_add, hcancel, ← hr]
    nlinarith only [sq_nonneg (3 * lam * PDE.vecEuclideanNorm p - 2 * H)]
  exact (mul_le_mul_of_nonneg_left hdot (by norm_num)).trans (by
    simpa only [mul_assoc] using hy)

end HypoellipticAleksandrov.KineticAleksandrov.Holder
