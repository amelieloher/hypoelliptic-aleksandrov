module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.GeometryHomogeneity
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileGeTwoRegularity
import Mathlib.Tactic.Linarith

/-! # Homogeneity of the higher-dimensional profile jets -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open Set Filter

/-- Positive kinetic dilation preserves nonzero points. -/
theorem dilate_ne_zero {d : ℕ} (r : ℝ) (hr : 0 < r) (q : XV d) (hq : q ≠ 0) :
    dilate r q ≠ 0 := by
  intro hz
  have he := congrArg (dilate r⁻¹) hz
  rw [dilate_mul, inv_mul_cancel₀ hr.ne', dilate_one, dilate_zero] at he
  exact hq he

/-- The smooth homogeneous profile is differentiable at every nonzero point. -/
theorem differentiableAt_profile_off_origin {d : ℕ} (H : XV d → ℝ)
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ : Set (XV d))) (q : XV d) (hq : q ≠ 0) :
    DifferentiableAt ℝ H q :=
  (hs.contDiffAt (isOpen_compl_singleton.mem_nhds (by simpa using hq))).differentiableAt
    (by simp)

/-- Differentiating kinetic homogeneity twice gives the Hessian degree alpha minus two. -/
theorem homogeneous_dvv_off_origin {d : ℕ} (H : XV d → ℝ) (alpha r : ℝ)
    (hr : 0 < r) (hhom : ∀ q, H (dilate r q) = Real.rpow r alpha * H q)
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ : Set (XV d)))
    (q : XV d) (hq : q ≠ 0) (i k : Fin d) :
    dvv H (dilate r q) i k = Real.rpow r (alpha - 2) * dvv H q i k := by
  have hg : DifferentiableAt ℝ (fun z => dv H z k) q :=
    (contDiffAt_dv_off_origin H hs q hq k).differentiableAt (by simp)
  have hgr : DifferentiableAt ℝ (fun z => dv H z k) (dilate r q) :=
    (contDiffAt_dv_off_origin H hs _ (dilate_ne_zero r hr q hq) k).differentiableAt (by simp)
  have hloc : (fun z => dv H (dilate r z) k) =ᶠ[nhds q]
      (fun z => Real.rpow r (alpha - 1) * dv H z k) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hq] with z hz
    exact homogeneous_dv_identity H alpha r hr hhom z
      (differentiableAt_profile_off_origin H hs z hz)
      (differentiableAt_profile_off_origin H hs _ (dilate_ne_zero r hr z hz)) k
  have he := congrArg (fun L : XV d →L[ℝ] ℝ => L (0, Pi.single i 1)) hloc.fderiv_eq
  rw [fderiv_fun_comp q hgr (hasFDerivAt_dilate r q).differentiableAt,
    fderiv_const_mul hg, (hasFDerivAt_dilate r q).fderiv] at he
  have hw : dilate r ((0, Pi.single i 1) : XV d) = r • (0, Pi.single i 1) := by
    simp [dilate, Prod.smul_mk]
  simp only [ContinuousLinearMap.comp_apply, dilationLinearMap_apply, smul_apply,
    smul_eq_mul] at he
  rw [hw, map_smul] at he
  change r * dvv H (dilate r q) i k = Real.rpow r (alpha - 1) * dvv H q i k at he
  simp only [Real.rpow_eq_pow] at he ⊢
  rw [show alpha - 2 = (alpha - 1) - 1 by ring, Real.rpow_sub hr, Real.rpow_one,
    div_mul_eq_mul_div]
  apply (eq_div_iff hr.ne').mpr
  simpa only [mul_comm] using he

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
