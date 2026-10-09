module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularCoordinatesMeasure
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDisintegrationDensity
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureDegree
import Mathlib.Tactic

/-! # Measure-level radial homogeneity in the source coordinates -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- Density degree gives the exact pushforward factor under kinetic dilation. -/
theorem HasBellmanDensityDegree.map_dilation {β : ℝ} {μ : Measure BellmanPuncturedPlane}
    (hμ : HasBellmanDensityDegree β μ) (r : ℝ) (hr : 0 < r) :
    Measure.map (bellmanDilation r hr) μ = ENNReal.ofReal (r ^ (β - 4)) • μ := by
  let D := bellmanDilationHomeomorph r hr
  ext E hE
  change (Measure.map D μ) E = _
  rw [Measure.map_apply D.measurable hE, Measure.smul_apply, smul_eq_mul]
  have hpre : D ⁻¹' E = bellmanDilation r⁻¹ (inv_pos.mpr hr) '' E := by
    ext q
    constructor
    · intro hq
      exact ⟨D q, hq, D.symm_apply_apply q⟩
    · rintro ⟨z, hz, rfl⟩
      change D (D.symm z) ∈ E
      rw [D.apply_symm_apply]
      exact hz
  rw [hpre, hμ r⁻¹ (inv_pos.mpr hr) E hE]
  have hp : (r⁻¹) ^ (4 - β) = r ^ (β - 4) := by
    rw [← Real.rpow_neg_eq_inv_rpow]
    congr 1
    ring
  rw [hp]

/-- Kinetic dilation preserves the positive-position part of the punctured carrier. -/
theorem bellmanDilation_preimage_positive (r : ℝ) (hr : 0 < r) :
    bellmanDilation r hr ⁻¹' {q : BellmanPuncturedPlane | 0 < q.val.1} =
      {q : BellmanPuncturedPlane | 0 < q.val.1} := by
  ext q
  exact mul_pos_iff_of_pos_left (pow_pos hr 3)

/-- Density degree also gives the exact pushforward factor on the positive-position
restriction. -/
theorem HasBellmanDensityDegree.map_positive_restrict {β : ℝ}
    {μ : Measure BellmanPuncturedPlane} (hμ : HasBellmanDensityDegree β μ)
    (r : ℝ) (hr : 0 < r) :
    Measure.map (bellmanDilation r hr) (μ.restrict {q | 0 < q.val.1}) =
      ENNReal.ofReal (r ^ (β - 4)) • μ.restrict {q | 0 < q.val.1} := by
  have hm : MeasurableSet {q : BellmanPuncturedPlane | 0 < q.val.1} :=
    (isOpen_lt continuous_const (continuous_fst.comp continuous_subtype_val)).measurableSet
  rw [← bellmanDilation_preimage_positive r hr,
    ← Measure.restrict_map (measurable_bellmanDilation r hr) hm,
    hμ.map_dilation r hr, Measure.restrict_smul, bellmanDilation_preimage_positive r hr]

/-- The source coordinate pullback has the same degree, acting only on its radial coordinate. -/
theorem HasBellmanDensityDegree.map_angularPullback {β : ℝ}
    {μ : Measure BellmanPuncturedPlane} (hμ : HasBellmanDensityDegree β μ)
    (r : ℝ) (hr : 0 < r) :
    Measure.map ((bellmanRadialScale r hr).prodCongr (Homeomorph.refl ℝ))
      (bellmanAngularPullback μ) =
      ENNReal.ofReal (r ^ (β - 4)) • bellmanAngularPullback μ := by
  let S := (bellmanRadialScale r hr).prodCongr (Homeomorph.refl ℝ)
  have he := isOpenEmbedding_bellmanAngularPoint.measurableEmbedding
  apply he.map_injective
  rw [Measure.map_map he.measurable S.measurable,
    Measure.map_smul _ he.measurable.aemeasurable, map_bellmanAngularPullback]
  have hc : bellmanAngularPoint ∘ S = bellmanDilation r hr ∘ bellmanAngularPoint := by
    funext w
    exact (bellmanAngularPoint_dilation r hr w).symm
  rw [hc, ← Measure.map_map (measurable_bellmanDilation r hr) he.measurable,
    map_bellmanAngularPullback, hμ.map_positive_restrict r hr]

end HypoellipticAleksandrov.KineticAleksandrov
