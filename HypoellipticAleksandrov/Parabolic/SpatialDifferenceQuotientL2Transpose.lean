module

public import HypoellipticAleksandrov.Parabolic.SpatialDifferenceQuotientTest
public import HypoellipticAleksandrov.Parabolic.WeakDerivatives
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Spacetime spatial difference-quotient transposition

This file establishes the fixed-step, coefficient-free transposition identity
for a spatial difference quotient against a compactly supported spacetime test.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped ENNReal

private theorem spatialShift_neg_comp_apply
    {d : ℕ} (k : Fin d) (h : ℝ) (z : TimeVelocity d) :
    spatialShift k (-h) (spatialShift k h z) = z := by
  change (spatialShift k (-h) ∘ spatialShift k h) z = z
  rw [spatialShift_comp]
  simp

private theorem spatialShift_comp_neg_apply
    {d : ℕ} (k : Fin d) (h : ℝ) (z : TimeVelocity d) :
    spatialShift k h (spatialShift k (-h) z) = z := by
  change (spatialShift k h ∘ spatialShift k (-h)) z = z
  rw [spatialShift_comp]
  simp

private theorem spatialShift_measurableEmbedding
    {d : ℕ} (k : Fin d) (h : ℝ) :
    MeasurableEmbedding (spatialShift k h) := by
  change MeasurableEmbedding (fun z : TimeVelocity d => z + (0, h • PDE.basisVec k))
  simpa only [Homeomorph.coe_addRight] using
    (Homeomorph.addRight ((0, h • PDE.basisVec k) : TimeVelocity d)).measurableEmbedding

private theorem spatialShift_measurePreserving
    {d : ℕ} (k : Fin d) (h : ℝ) :
    MeasurePreserving (spatialShift k h)
      (volume : Measure (TimeVelocity d))
      (volume : Measure (TimeVelocity d)) := by
  change MeasurePreserving
    (fun z : TimeVelocity d => z + (0, h • PDE.basisVec k)) volume volume
  exact measurePreserving_add_right volume _

/-- A forward spatial difference quotient transposes to the negative backward
quotient on any raw carrier containing the test support and its forward shift. -/
theorem setIntegral_spatialDifferenceQuotient_mul_eq_neg_mul_spatialDifferenceQuotient_neg
    {d : ℕ} (U : Set (TimeVelocity d))
    (k : Fin d) (h : ℝ) (u φ : TimeVelocity d → ℝ)
    (hu : ParabolicMemLpOn U (2 : ℝ≥0∞) u)
    (hφ : Continuous φ) (hφcompact : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U)
    (hφshift : Set.MapsTo (spatialShift k h) (tsupport φ) U) :
    (∫ z in U, spatialDifferenceQuotient k h u z * φ z ∂volume) =
      -∫ z in U,
        u z * spatialDifferenceQuotient k (-h) φ z ∂volume := by
  rcases eq_or_ne h 0 with rfl | hh
  · simp [spatialDifferenceQuotient]
  let ψ : TimeVelocity d → ℝ := spatialTranslate k (-h) φ
  let A : TimeVelocity d → ℝ := fun z => spatialTranslate k h u z * φ z
  let B : TimeVelocity d → ℝ := fun z => u z * φ z
  let C : TimeVelocity d → ℝ := fun z => u z * ψ z
  have hψcont : Continuous ψ := by
    change Continuous (φ ∘ spatialShift k (-h))
    exact hφ.comp <| by
      change Continuous (fun z : TimeVelocity d => z + (0, (-h) • PDE.basisVec k))
      simpa only [Homeomorph.coe_addRight] using
        (Homeomorph.addRight ((0, (-h) • PDE.basisVec k) : TimeVelocity d)).continuous
  have hψcompact : HasCompactSupport ψ := by
    exact HasCompactSupport.spatialTranslate hφcompact
  have hψU : tsupport ψ ⊆ U := by
    intro z hz
    rw [mem_tsupport_spatialTranslate_iff] at hz
    have hforward := hφshift hz
    simpa only [ψ, spatialShift_comp_neg_apply] using hforward
  have hqcont : Continuous (spatialDifferenceQuotient k (-h) φ) := by
    change Continuous (fun z => (ψ z - φ z) / (-h))
    exact (hψcont.sub hφ).div_const _
  have hqcompact : HasCompactSupport (spatialDifferenceQuotient k (-h) φ) := by
    exact HasCompactSupport.spatialDifferenceQuotient hφcompact
  have hqU : tsupport (spatialDifferenceQuotient k (-h) φ) ⊆ U := by
    apply tsupport_spatialDifferenceQuotient_subset_of_mapsTo_spatialShift_neg
      k (-h) φ (fun _ hz => hz) hφU
    simpa using hφshift
  have hφmem : MemLp φ (2 : ℝ≥0∞) (volume.restrict U) :=
    hφ.memLp_of_hasCompactSupport hφcompact
  have hψmem : MemLp ψ (2 : ℝ≥0∞) (volume.restrict U) :=
    hψcont.memLp_of_hasCompactSupport hψcompact
  have hBOn : IntegrableOn B U volume := by
    exact hu.integrable_mul hφmem
  have hCOn : IntegrableOn C U volume := by
    exact hu.integrable_mul hψmem
  have hBsupport : Function.support B ⊆ U := by
    intro z hz
    rw [Function.mem_support] at hz
    by_contra hnot
    have hzero : φ z = 0 := image_eq_zero_of_notMem_tsupport fun hzs => hnot (hφU hzs)
    apply hz
    simp [B, hzero]
  have hCsupport : Function.support C ⊆ U := by
    intro z hz
    rw [Function.mem_support] at hz
    by_contra hnot
    have hzero : ψ z = 0 := image_eq_zero_of_notMem_tsupport fun hzs => hnot (hψU hzs)
    apply hz
    simp [C, hzero]
  have hB : Integrable B volume :=
    (integrableOn_iff_integrable_of_support_subset hBsupport).mp hBOn
  have hC : Integrable C volume :=
    (integrableOn_iff_integrable_of_support_subset hCsupport).mp hCOn
  let hμ := spatialShift_measurePreserving k h
  let hembed := spatialShift_measurableEmbedding k h
  have hA : Integrable A volume := by
    have hcomp : Integrable (C ∘ spatialShift k h) volume :=
      (hμ.integrable_comp_emb hembed).mpr hC
    convert hcomp using 1
    ext z
    dsimp [A, C, ψ, Function.comp_def]
    rw [spatialShift_neg_comp_apply]
  have hAint : (∫ z, A z ∂volume) = ∫ z, C z ∂volume := by
    have hcomp := hμ.integral_comp hembed C
    calc
      (∫ z, A z ∂volume) = ∫ z, C (spatialShift k h z) ∂volume := by
        apply integral_congr_ae
        filter_upwards with z
        dsimp [A, C, ψ]
        rw [spatialShift_neg_comp_apply]
      _ = ∫ z, C z ∂volume := hcomp
  have hDsupport : Function.support (fun z => spatialDifferenceQuotient k h u z * φ z) ⊆ U := by
    intro z hz
    rw [Function.mem_support] at hz
    by_contra hnot
    have hzero : φ z = 0 := image_eq_zero_of_notMem_tsupport fun hzs => hnot (hφU hzs)
    exact hz (by rw [hzero, mul_zero])
  have hRsupport : Function.support
      (fun z => u z * spatialDifferenceQuotient k (-h) φ z) ⊆ U := by
    intro z hz
    rw [Function.mem_support] at hz
    by_contra hnot
    have hzero : spatialDifferenceQuotient k (-h) φ z = 0 :=
      image_eq_zero_of_notMem_tsupport fun hzs => hnot (hqU hzs)
    exact hz (by rw [hzero, mul_zero])
  calc
    (∫ z in U, spatialDifferenceQuotient k h u z * φ z ∂volume) =
        ∫ z, spatialDifferenceQuotient k h u z * φ z ∂volume := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      by_contra hne
      exact hz (hDsupport (Function.mem_support.mpr hne))
    _ = ∫ z, (A z - B z) / h ∂volume := by
      congr with z
      dsimp [A, B]
      ring
    _ = ((∫ z, A z ∂volume) - ∫ z, B z ∂volume) / h := by
      rw [integral_div, integral_sub hA hB]
    _ = ((∫ z, C z ∂volume) - ∫ z, B z ∂volume) / h := by rw [hAint]
    _ = ∫ z, (C z - B z) / h ∂volume := by
      rw [← integral_sub hC hB, ← integral_div]
    _ = -∫ z, u z * spatialDifferenceQuotient k (-h) φ z ∂volume := by
      rw [← integral_neg]
      congr with z
      dsimp [B, C, ψ]
      field_simp [hh]
    _ = -∫ z in U, u z * spatialDifferenceQuotient k (-h) φ z ∂volume := by
      have hset : (∫ z in U, u z * spatialDifferenceQuotient k (-h) φ z ∂volume) =
          ∫ z, u z * spatialDifferenceQuotient k (-h) φ z ∂volume := by
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro z hz
        by_contra hne
        exact hz (hRsupport (Function.mem_support.mpr hne))
      rw [hset]

end HypoellipticAleksandrov.Parabolic
