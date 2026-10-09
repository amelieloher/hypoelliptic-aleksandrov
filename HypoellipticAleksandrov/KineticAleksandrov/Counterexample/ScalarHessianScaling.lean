module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarJetFields
import Mathlib.Tactic

/-! # Exact scalar Hessian representative scaling -/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open Filter Set
open scoped Topology ContDiff

/-- The velocity representative agrees locally with the native derivative off the axis. -/
theorem scalarGv_eq_nhds (gamma : ScalarGamma) (Lam : ℝ) (q : XV 1)
    (hx : q.1 0 ≠ 0) : scalarGv gamma Lam =ᶠ[𝓝 q] dv (scalarProfile gamma Lam) := by
  have hc : Continuous (fun z : XV 1 => z.1 0) := by fun_prop
  filter_upwards [hc.continuousAt.eventually_ne hx] with z hz
  simp only [scalarGv, hz, ↓reduceIte]

/-- Each velocity component is differentiable at every off-axis point. -/
theorem scalarGv_differentiableAt (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam)
    (q : XV 1) (hx : q.1 0 ≠ 0) (k : Fin 1) :
    DifferentiableAt ℝ (fun z => scalarGv gamma Lam z k) q := by
  have hH := scalarProfile_contDiffAt_off_axis gamma Lam hLam q hx
  have hd : DifferentiableAt ℝ (fun z => dv (scalarProfile gamma Lam) z k) q :=
    ((hH.fderiv_right (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)).clm_apply
      contDiffAt_const).differentiableAt (by norm_num)
  exact hd.congr_of_eventuallyEq ((scalarGv_eq_nhds gamma Lam q hx).fun_comp (fun w => w k))

/-- The off-axis Hessian equals the velocity selector of the representative velocity component. -/
theorem scalarHess_eq_velocity_derivative (gamma : ScalarGamma) (Lam : ℝ)
    (q : XV 1) (hx : q.1 0 ≠ 0) (i k : Fin 1) :
    scalarHess gamma Lam q i k = dv (fun z => scalarGv gamma Lam z k) q i := by
  simp only [scalarHess, hx, ↓reduceIte, dvv, dv]
  exact congrArg (fun T : XV 1 →L[ℝ] ℝ => T (0, Pi.single i 1))
    (((scalarGv_eq_nhds gamma Lam q hx).fun_comp (fun w => w k)).fderiv_eq.symm)

/-- The selected velocity Hessian has the exact source homogeneous degree everywhere. -/
theorem scalarHess_homogeneous (gamma : ScalarGamma) (Lam r : ℝ) (hLam : 0 < Lam)
    (hr : 0 < r) (q : XV 1) : scalarHess gamma Lam (dilate r q) =
      Real.rpow r (3 * gamma.1 - 2) • scalarHess gamma Lam q := by
  have hxDil : (dilate r q).1 0 = 0 ↔ q.1 0 = 0 := by
    simp only [dilate, Pi.smul_apply, smul_eq_mul, mul_eq_zero,
      pow_ne_zero 3 hr.ne', false_or]
  by_cases hx : q.1 0 = 0
  · simp only [scalarHess, hxDil, hx, ↓reduceIte, smul_zero]
  · have hxr : (dilate r q).1 0 ≠ 0 := mt hxDil.mp hx
    funext i k
    rw [scalarHess_eq_velocity_derivative gamma Lam (dilate r q) hxr i k]
    have hhom : ∀ z, scalarGv gamma Lam (dilate r z) k =
        Real.rpow r (3 * gamma.1 - 1) * scalarGv gamma Lam z k := by
      intro z
      exact congrArg (fun w => w k) (scalarGv_homogeneous gamma Lam r hLam hr z)
    have hh := homogeneous_dv_identity (fun z => scalarGv gamma Lam z k)
      (3 * gamma.1 - 1) r hr hhom q
      (scalarGv_differentiableAt gamma Lam hLam q hx k)
      (scalarGv_differentiableAt gamma Lam hLam (dilate r q) hxr k) i
    rw [show 3 * gamma.1 - 1 - 1 = 3 * gamma.1 - 2 by ring,
      ← scalarHess_eq_velocity_derivative gamma Lam q hx i k] at hh
    exact hh

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
