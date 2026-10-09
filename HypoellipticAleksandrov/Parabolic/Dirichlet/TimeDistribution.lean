module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeTests
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Scalar reverse-time distribution separation

This module transfers scalar distribution separation on an open interval from
ambient Lebesgue measure to the literal restricted reverse-time measure.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open Filter MeasureTheory Set
open scoped ENNReal

private theorem integrable_mul_of_tsupport_subset
    {U : Set ℝ} {f g : ℝ → ℝ}
    (hf : Integrable f (volume.restrict U)) (hg : Continuous g)
    (hgCompact : HasCompactSupport g) (hgSupport : tsupport g ⊆ U) :
    Integrable (fun tau => f tau * g tau) volume := by
  have hfOn : IntegrableOn f U volume := by
    simpa only [IntegrableOn] using hf
  have hfSupport : IntegrableOn f (tsupport g) volume :=
    hfOn.mono_set hgSupport
  have hproductSupport :
      IntegrableOn (fun tau => f tau * g tau) (tsupport g) volume :=
    hfSupport.mul_continuousOn hg.continuousOn hgCompact.isCompact
  have hproductSupportSubset :
      Function.support (fun tau => f tau * g tau) ⊆ tsupport g := by
    intro tau htau
    exact tsupport_mul_subset_right (subset_closure htau)
  exact (integrableOn_iff_integrable_of_support_subset hproductSupportSubset).mp
    hproductSupport

/-- An integrable scalar function on the literal reverse-time interval whose
pairing with every compact smooth reverse-time test vanishes is zero a.e. -/
theorem ae_eq_zero_of_integral_reverseTimeScalarTest
    (T : ℝ) {f : ℝ → ℝ}
    (hf : MeasureTheory.Integrable f (reverseTimeVolume T))
    (hzero : ∀ eta : ReverseTimeScalarTest T,
      (∫ tau, f tau * eta tau ∂reverseTimeVolume T) = 0) :
    f =ᵐ[reverseTimeVolume T] 0 := by
  let U : Set ℝ := reverseTimeOpenInterval T
  have hUOpen : IsOpen U := by
    simpa only [U, reverseTimeOpenInterval] using
      (isOpen_Ioo : IsOpen (Set.Ioo (0 : ℝ) T))
  have hfRestrict : Integrable f (volume.restrict U) := by
    simpa only [U, reverseTimeVolume] using hf
  have hfLocal : LocallyIntegrableOn f U volume :=
    locallyIntegrableOn_of_locallyIntegrable_restrict hfRestrict.locallyIntegrable
  have hPairing : ∀ (g : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) g →
      HasCompactSupport g → tsupport g ⊆ U →
      (∫ tau, g tau • f tau ∂volume) = 0 := by
    intro g hgSmooth hgCompact hgSupport
    let eta : ReverseTimeScalarTest T :=
      { toFun := g
        contDiff' := hgSmooth
        hasCompactSupport' := hgCompact
        tsupport_subset' := by
          change tsupport g ⊆ reverseTimeOpenInterval T
          exact hgSupport }
    have hzeroOutPublic : ∀ tau, tau ∉ U → f tau * g tau = 0 := by
      intro tau htau
      have htSupport : tau ∉ tsupport g := fun htsupport => htau (hgSupport htsupport)
      rw [image_eq_zero_of_notMem_tsupport htSupport]
      simp
    have hrestricted : (∫ tau in U, f tau * g tau ∂volume) = 0 := by
      have hzeroEta := hzero eta
      change (∫ tau, f tau * g tau ∂(volume.restrict U)) = 0 at hzeroEta
      exact hzeroEta
    have hsetPairing : (∫ tau in U, g tau * f tau ∂volume) = 0 := by
      calc
        (∫ tau in U, g tau * f tau ∂volume) =
            ∫ tau in U, f tau * g tau ∂volume := by
              apply setIntegral_congr_fun hUOpen.measurableSet
              intro tau htau
              exact mul_comm _ _
        _ = 0 := hrestricted
    have hzeroOut : ∀ tau, tau ∉ U → g tau * f tau = 0 := by
      intro tau htau
      simpa only [mul_comm] using hzeroOutPublic tau htau
    have hproductAndPairing :
        Integrable (fun tau => g tau * f tau) volume ∧
          (∫ tau, g tau * f tau ∂volume) = 0 := by
      constructor
      · simpa only [mul_comm] using
          integrable_mul_of_tsupport_subset hfRestrict hgSmooth.continuous hgCompact hgSupport
      · calc
          (∫ tau, g tau * f tau ∂volume) = ∫ tau in U, g tau * f tau ∂volume := by
            rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzeroOut]
          _ = 0 := hsetPairing
    simpa only [smul_eq_mul] using hproductAndPairing.2
  have hAmbient : ∀ᵐ tau ∂volume, tau ∈ U → f tau = 0 :=
    hUOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero hfLocal hPairing
  rw [Filter.EventuallyEq, reverseTimeVolume,
    ae_restrict_iff' hUOpen.measurableSet]
  exact hAmbient

/-- The `L²` specialization of reverse-time scalar distribution separation. -/
theorem ae_eq_zero_of_memLp_two_integral_reverseTimeScalarTest
    (T : ℝ) {f : ℝ → ℝ}
    (hf : MeasureTheory.MemLp f (2 : ℝ≥0∞) (reverseTimeVolume T))
    (hzero : ∀ eta : ReverseTimeScalarTest T,
      (∫ tau, f tau * eta tau ∂reverseTimeVolume T) = 0) :
    f =ᵐ[reverseTimeVolume T] 0 := by
  letI : IsFiniteMeasure (reverseTimeVolume T) := by
    change IsFiniteMeasure (volume.restrict (Ioo 0 T))
    infer_instance
  exact ae_eq_zero_of_integral_reverseTimeScalarTest T
    (hf.integrable (by norm_num : 1 ≤ (2 : ℝ≥0∞))) hzero

end HypoellipticAleksandrov.Parabolic.Dirichlet
