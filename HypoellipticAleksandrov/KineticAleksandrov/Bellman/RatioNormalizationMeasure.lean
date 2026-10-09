module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.RatioNormalizationGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.PairSetting
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureDegree
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Tactic

/-! # Radon and homogeneous measure transport under position normalization -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- A homeomorphism preserves the literal Radon conditions used for Bellman pairs. -/
theorem IsBellmanRadon.map_homeomorph {μ : Measure BellmanPuncturedPlane}
    (hμ : IsBellmanRadon μ) (T : BellmanPuncturedPlane ≃ₜ BellmanPuncturedPlane) :
    IsBellmanRadon (Measure.map T μ) := by
  let : IsFiniteMeasureOnCompacts μ := hμ.1
  let : Measure.InnerRegular μ := hμ.2
  refine ⟨?_, Measure.InnerRegular.map T⟩
  constructor
  intro K hK
  rw [Measure.map_apply T.measurable hK.measurableSet]
  have he : T ⁻¹' K = T.symm '' K := by
    ext q
    constructor
    · intro hq
      exact ⟨T q, hq, T.symm_apply_apply q⟩
    · rintro ⟨z, hz, rfl⟩
      change T (T.symm z) ∈ K
      rw [T.apply_symm_apply]
      exact hz
  rw [he]
  exact (hK.image T.symm.continuous).measure_lt_top

/-- Finite scalar multiplication preserves the literal Radon conditions. -/
theorem IsBellmanRadon.smul {μ : Measure BellmanPuncturedPlane}
    (hμ : IsBellmanRadon μ) (c : ENNReal) (hc : c ≠ ⊤) : IsBellmanRadon (c • μ) := by
  let : IsFiniteMeasureOnCompacts μ := hμ.1
  let : Measure.InnerRegular μ := hμ.2
  exact ⟨IsFiniteMeasureOnCompacts.smul μ hc, inferInstance⟩

/-- Position rescaling preserves every density degree without changing its exponent. -/
theorem HasBellmanDensityDegree.map_position {β : ℝ}
    {μ : Measure BellmanPuncturedPlane} (hμ : HasBellmanDensityDegree β μ)
    (s : ℝ) (hs : 0 < s) :
    HasBellmanDensityDegree β (Measure.map (bellmanPositionHomeomorph s hs) μ) := by
  intro r hr E hE
  let T := bellmanPositionHomeomorph s hs
  let D := bellmanDilationHomeomorph r hr
  have hcomm (q : BellmanPuncturedPlane) : T (D q) = D (T q) :=
    bellmanPositionHomeomorph_dilation s hs r hr q
  have hset : T ⁻¹' (D '' E) = D '' (T ⁻¹' E) := by
    ext q
    constructor
    · rintro ⟨z, hz, he⟩
      refine ⟨T.symm z, by simpa using hz, ?_⟩
      apply T.injective
      rw [hcomm, T.apply_symm_apply]
      exact he
    · rintro ⟨z, hz, rfl⟩
      exact ⟨T z, hz, (hcomm z).symm⟩
  change μ.map T (D '' E) = ENNReal.ofReal (r ^ (4 - β)) * μ.map T E
  rw [Measure.map_apply T.measurable (D.measurableEmbedding.measurableSet_image.mpr hE),
    hset, Measure.map_apply T.measurable hE]
  exact hμ r hr (T ⁻¹' E) (T.measurable hE)

/-- Scalar multiplication preserves every density degree. -/
theorem HasBellmanDensityDegree.smul {β : ℝ} {μ : Measure BellmanPuncturedPlane}
    (hμ : HasBellmanDensityDegree β μ) (c : ENNReal) :
    HasBellmanDensityDegree β (c • μ) := by
  intro r hr E hE
  simp only [Measure.smul_apply, smul_eq_mul, hμ r hr E hE]
  ring

end HypoellipticAleksandrov.KineticAleksandrov
