module

public import HypoellipticAleksandrov.Parabolic.WeakDerivatives
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Local directional integration by parts with compact test support -/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

open Set MeasureTheory
open scoped Topology

private theorem integrable_mul_test
    {d : ℕ} {U : Set (TimeVelocity d)} {f ψ : TimeVelocity d → ℝ}
    (hf : ContinuousOn f U) (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (hsub : tsupport ψ ⊆ U) : Integrable (fun z => f z * ψ z) := by
  have hK : IntegrableOn f (tsupport ψ) volume :=
    (hf.mono hsub).integrableOn_compact hc.isCompact
  have hprod := hK.mul_continuousOn hψ.continuousOn hc.isCompact
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp hprod
  intro z hz
  exact tsupport_mul_subset_right (subset_closure hz)

/-- Local continuous line derivatives give integration by parts against a compact smooth test. -/
theorem setIntegral_mul_directional_test
    {d : ℕ} {U : Set (TimeVelocity d)} {f df φ : TimeVelocity d → ℝ}
    (hf : ContinuousOn f U) (hdf : ContinuousOn df U) (v : TimeVelocity d)
    (hd : ∀ z ∈ U, HasLineDerivAt ℝ f (df z) z v)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hsub : tsupport φ ⊆ U) :
    (∫ z in U, f z * fderiv ℝ φ z v) = -∫ z in U, df z * φ z := by
  have hDcont : Continuous (fun z => fderiv ℝ φ z v) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDcompact : HasCompactSupport (fun z => fderiv ℝ φ z v) := hc.fderiv_apply (𝕜 := ℝ) v
  have hDsub : tsupport (fun z => fderiv ℝ φ z v) ⊆ tsupport φ := by
    refine (closure_mono ?_).trans (tsupport_fderiv_subset ℝ)
    intro z hz
    rw [Function.mem_support] at hz ⊢
    intro hzero
    exact hz (by simp [hzero])
  have hglobal := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (B := ContinuousLinearMap.mul ℝ ℝ)
    (integrable_mul_test hdf hφ.continuous hc hsub)
    (integrable_mul_test hf hDcont hDcompact (hDsub.trans hsub))
    (integrable_mul_test hf hφ.continuous hc hsub)
    (fun z hz => hd z (hsub hz))
    (fun z _ => (hφ.differentiable (by simp) z).hasFDerivAt.hasLineDerivAt v)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => ?_),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => ?_)]
  · exact hglobal
  · rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hsub h)), mul_zero]
  · rw [image_eq_zero_of_notMem_tsupport (fun h => hz ((hDsub.trans hsub) h)), mul_zero]

end HypoellipticAleksandrov.Parabolic
