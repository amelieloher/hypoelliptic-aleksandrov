module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.HormanderBridgeAdjoint
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Compactly supported directional integration by parts in evolution coordinates -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Evolution

open Set MeasureTheory
open scoped Topology

/-- Multiplication by a compactly supported test is integrable locally. -/
theorem integrable_evolution_mul_test
    {n : ℕ} {U : Set (EvolutionVec n)} {f ψ : EvolutionVec n → ℝ}
    (hf : ContinuousOn f U) (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (hsub : tsupport ψ ⊆ U) : Integrable (fun z => f z * ψ z) := by
  have hK : IntegrableOn f (tsupport ψ) volume :=
    (hf.mono hsub).integrableOn_compact hc.isCompact
  have hprod := hK.mul_continuousOn hψ.continuousOn hc.isCompact
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp hprod
  intro z hz
  exact tsupport_mul_subset_right (subset_closure hz)

/-- Local continuous line derivatives give integration by parts against a compact smooth test. -/
theorem setIntegral_mul_evolution_directional_test
    {n : ℕ} {U : Set (EvolutionVec n)} {f df φ : EvolutionVec n → ℝ}
    (hf : ContinuousOn f U) (hdf : ContinuousOn df U) (v : EvolutionVec n)
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
    (integrable_evolution_mul_test hdf hφ.continuous hc hsub)
    (integrable_evolution_mul_test hf hDcont hDcompact (hDsub.trans hsub))
    (integrable_evolution_mul_test hf hφ.continuous hc hsub)
    (fun z hz => hd z (hsub hz))
    (fun z _ => (hφ.differentiable (by simp) z).hasFDerivAt.hasLineDerivAt v)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => ?_),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => ?_)]
  · exact hglobal
  · rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hsub h)), mul_zero]
  · rw [image_eq_zero_of_notMem_tsupport (fun h => hz ((hDsub.trans hsub) h)), mul_zero]

/-- A directional derivative does not enlarge the support of a smooth test. -/
theorem tsupport_evolution_fderiv_apply {n : ℕ} (φ : EvolutionVec n → ℝ)
    (v : EvolutionVec n) :
    tsupport (fun x => fderiv ℝ φ x v) ⊆ tsupport φ := by
  refine (closure_mono ?_).trans (tsupport_fderiv_subset ℝ)
  intro x hx
  rw [Function.mem_support] at hx ⊢
  intro hz
  exact hx (by simp [hz])

/-- Two compactly supported integrations by parts transfer two spatial derivatives. -/
theorem setIntegral_mul_evolution_second_test
    {n : ℕ} {U : Set (EvolutionVec n)} {f df ddf φ : EvolutionVec n → ℝ}
    (hf : ContinuousOn f U) (hdf : ContinuousOn df U) (hddf : ContinuousOn ddf U)
    (v w : EvolutionVec n)
    (hd : ∀ x ∈ U, HasLineDerivAt ℝ f (df x) x v)
    (hdd : ∀ x ∈ U, HasLineDerivAt ℝ df (ddf x) x w)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hsub : tsupport φ ⊆ U) :
    (∫ x in U, f x * fderiv ℝ (fun y => fderiv ℝ φ y w) x v) =
      ∫ x in U, ddf x * φ x := by
  have hD : ContDiff ℝ (⊤ : ℕ∞) (fun y => fderiv ℝ φ y w) :=
    (hφ.fderiv_right (by simp)).clm_apply (contDiff_const (c := w))
  rw [setIntegral_mul_evolution_directional_test hf hdf v hd hD
    (hc.fderiv_apply (𝕜 := ℝ) w) ((tsupport_evolution_fderiv_apply φ w).trans hsub),
    setIntegral_mul_evolution_directional_test hdf hddf w hdd hφ hc hsub, neg_neg]

end HypoellipticAleksandrov.KineticAleksandrov.Evolution
