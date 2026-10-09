module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.GaussianKernelCalculus
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic

/-! # Directional Gaussian derivatives and compact test jets -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory

/-- A fixed directional derivative of a smooth function is smooth. -/
theorem bellman_contDiff_direction {f : ℝ × ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (v : ℝ × ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q => fderiv ℝ f q v) := by
  exact (hf.contDiff_fderiv_apply (m := (⊤ : ℕ∞)) (by simp)).comp
    (contDiff_id.prodMk contDiff_const)

/-- The Fréchet position derivative equals the computed scalar derivative. -/
theorem bellmanGaussianKernel_fderiv_position (t : BellmanPositiveTime) (q : ℝ × ℝ) :
    fderiv ℝ (bellmanGaussianKernel t) q (1, 0) =
      (-6 * q.1 / t.val ^ 3 + 3 * q.2 / t.val ^ 2) *
        bellmanGaussianKernel t q := by
  have hf := (contDiff_bellmanGaussianKernel t).differentiable (by simp)
  have h := (hf q).hasFDerivAt.comp_hasDerivAt q.1
    ((hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2))
  exact h.unique (hasDerivAt_bellmanGaussianKernel_position t q.1 q.2)

/-- The Fréchet velocity derivative equals the computed scalar derivative. -/
theorem bellmanGaussianKernel_fderiv_velocity (t : BellmanPositiveTime) (q : ℝ × ℝ) :
    fderiv ℝ (bellmanGaussianKernel t) q (0, 1) =
      (3 * q.1 / t.val ^ 2 - 2 * q.2 / t.val) * bellmanGaussianKernel t q := by
  have hf := (contDiff_bellmanGaussianKernel t).differentiable (by simp)
  have h := (hf q).hasFDerivAt.comp_hasDerivAt q.2
    ((hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2))
  exact h.unique (hasDerivAt_bellmanGaussianKernel_velocity t q.1 q.2)

/-- The second Fréchet velocity derivative equals the computed scalar derivative. -/
theorem bellmanGaussianKernel_fderiv_velocity_twice
    (t : BellmanPositiveTime) (q : ℝ × ℝ) :
    fderiv ℝ (fun z => fderiv ℝ (bellmanGaussianKernel t) z (0, 1)) q (0, 1) =
      ((3 * q.1 / t.val ^ 2 - 2 * q.2 / t.val) ^ 2 - 2 / t.val) *
        bellmanGaussianKernel t q := by
  have hf := (bellman_contDiff_direction (contDiff_bellmanGaussianKernel t) (0, 1))
    |>.differentiable (by simp)
  have h := (hf q).hasFDerivAt.comp_hasDerivAt q.2
    ((hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2))
  have he : (fun y => fderiv ℝ (bellmanGaussianKernel t) (q.1, y) (0, 1)) =
      (fun y => deriv (fun z => bellmanGaussianKernel t (q.1, z)) y) := by
    funext y
    rw [bellmanGaussianKernel_fderiv_velocity, deriv_bellmanGaussianKernel_velocity]
  change HasDerivAt (fun y => fderiv ℝ (bellmanGaussianKernel t) (q.1, y) (0, 1)) _ _ at h
  rw [he] at h
  exact h.unique (hasDerivAt_deriv_bellmanGaussianKernel_velocity t q.1 q.2)

end HypoellipticAleksandrov.KineticAleksandrov
