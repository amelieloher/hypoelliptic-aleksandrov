module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.MollifyApproximateIdentity
import Mathlib.Tactic.Linarith

/-!
# Positivity and order for the normalized spatial mollifier

These are scalar convolution facts, to be applied after the operator identity is proved.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory ContinuousLinearMap
open scoped Convolution
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [MeasureSpace G] [BorelSpace G] [FiniteDimensional ℝ G]
  [Measure.IsAddHaarMeasure (volume : Measure G)]

omit [BorelSpace G] [Measure.IsAddHaarMeasure (volume : Measure G)] in
/-- Nonnegative spatial data remain nonnegative after normalized convolution. -/
theorem spatialMollify_nonneg (phi : ContDiffBump (0 : G)) (f : G → ℝ)
    (hf : ∀ y, 0 ≤ f y) (q : G) : 0 ≤ spatialMollify phi f q := by
  unfold spatialMollify
  apply integral_nonneg
  intro y
  exact mul_nonneg (phi.nonneg_normed y) (hf (q - y))

/-- Spatial mollification preserves pointwise order for locally integrable data. -/
theorem spatialMollify_mono (phi : ContDiffBump (0 : G)) (f g : G → ℝ)
    (hf : LocallyIntegrable f volume) (hg : LocallyIntegrable g volume)
    (hfg : ∀ y, f y ≤ g y) (q : G) :
    spatialMollify phi f q ≤ spatialMollify phi g q := by
  exact convolution_mono_right
    (phi.hasCompactSupport_normed.convolutionExists_left (lsmul ℝ ℝ)
      (phi.contDiff_normed (n := 0)).continuous hf q)
    (phi.hasCompactSupport_normed.convolutionExists_left (lsmul ℝ ℝ)
      (phi.contDiff_normed (n := 0)).continuous hg q)
    phi.nonneg_normed hfg

/-- The order-preservation lemma also respects almost-everywhere source bounds. -/
theorem spatialMollify_mono_ae (phi : ContDiffBump (0 : G)) (f g : G → ℝ)
    (hf : LocallyIntegrable f volume) (hg : LocallyIntegrable g volume)
    (hfg : ∀ᵐ y ∂volume, f y ≤ g y) (q : G) :
    spatialMollify phi f q ≤ spatialMollify phi g q := by
  apply integral_mono_ae
    (phi.hasCompactSupport_normed.convolutionExists_left (lsmul ℝ ℝ)
      (phi.contDiff_normed (n := 0)).continuous hf q)
    (phi.hasCompactSupport_normed.convolutionExists_left (lsmul ℝ ℝ)
      (phi.contDiff_normed (n := 0)).continuous hg q)
  have he := (volume.measurePreserving_sub_left q).quasiMeasurePreserving.ae hfg
  filter_upwards [he] with y hy
  exact mul_le_mul_of_nonneg_left hy (phi.nonneg_normed y)

/-- The scalar positive-part estimate used to absorb an operator commutator. -/
theorem positive_part_add_le (a f e : ℝ) (hf : 0 ≤ f) (haf : a ≤ f) :
    max (a + e) 0 ≤ f + |e| := by
  apply max_le
  · have he := le_abs_self e
    linarith
  · exact add_nonneg hf (abs_nonneg e)

/-- A positive convolution majorant absorbs any additive scalar error. -/
theorem mollified_positive_part_add_le (phi : ContDiffBump (0 : G)) (a f : G → ℝ)
    (ha : LocallyIntegrable a volume) (hf : LocallyIntegrable f volume)
    (hnonneg : ∀ y, 0 ≤ f y) (hmajor : ∀ y, a y ≤ f y) (q : G) (e : ℝ) :
    max (spatialMollify phi a q + e) 0 ≤ spatialMollify phi f q + |e| :=
  positive_part_add_le _ _ e (spatialMollify_nonneg phi f hnonneg q)
    (spatialMollify_mono phi a f ha hf hmajor q)

/-- Almost-everywhere majorization suffices for the positive-part error estimate. -/
theorem mollified_positive_part_add_le_ae (phi : ContDiffBump (0 : G)) (a f : G → ℝ)
    (ha : LocallyIntegrable a volume) (hf : LocallyIntegrable f volume)
    (hnonneg : ∀ y, 0 ≤ f y) (hmajor : ∀ᵐ y ∂volume, a y ≤ f y) (q : G) (e : ℝ) :
    max (spatialMollify phi a q + e) 0 ≤ spatialMollify phi f q + |e| :=
  positive_part_add_le _ _ e (spatialMollify_nonneg phi f hnonneg q)
    (spatialMollify_mono_ae phi a f ha hf hmajor q)

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
