module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDisintegrationDensity
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularCoordinatesLog
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasurePositive
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Tactic

/-! # The actual ds/s reference measure and its translation-invariant log-radius image -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Measure Set
open scoped NNReal

/-- The multiplicatively invariant reference radial measure is literally ds/s. -/
def bellmanRadialHaar : Measure BellmanPositiveTime :=
  bellmanPositiveTimeVolume.withDensity (fun s => ENNReal.ofReal s.val⁻¹)

/-- The reference measure is finite on compact subsets of the positive radial carrier. -/
instance bellmanRadialHaar_finiteOnCompacts : IsFiniteMeasureOnCompacts bellmanRadialHaar := by
  apply bellman_withDensity_finiteOnCompacts
  exact continuous_subtype_val.inv₀ (fun s => s.property.ne')

/-- The reference radial measure is sigma finite. -/
instance bellmanRadialHaar_sigmaFinite : SigmaFinite bellmanRadialHaar := by
  let : LocallyCompactSpace BellmanPositiveTime := isOpen_Ioi.locallyCompactSpace
  infer_instance

/-- The actual ds/s measure is invariant under every positive radial scaling. -/
theorem map_bellmanRadialHaar_radialScale (r : ℝ) (hr : 0 < r) :
    Measure.map (bellmanRadialScale r hr) bellmanRadialHaar = bellmanRadialHaar := by
  have hf : Measurable (fun s : BellmanPositiveTime => ENNReal.ofReal s.val⁻¹) := by
    fun_prop
  rw [bellmanRadialHaar, bellman_map_withDensity _ _ _ hf,
    map_bellmanPositiveTimeVolume_radialScale, withDensity_smul_measure]
  have he : (fun s : BellmanPositiveTime =>
      ENNReal.ofReal ((bellmanRadialScale r hr).symm s).val⁻¹) =
      ENNReal.ofReal r • (fun s : BellmanPositiveTime => ENNReal.ofReal s.val⁻¹) := by
    funext s
    change ENNReal.ofReal (r⁻¹ * s.val)⁻¹ = ENNReal.ofReal r * ENNReal.ofReal s.val⁻¹
    rw [mul_inv_rev, inv_inv, ← ENNReal.ofReal_mul hr.le, mul_comm]
  rw [he, withDensity_smul _ hf, smul_smul, ← ENNReal.ofReal_mul (inv_nonneg.mpr hr.le)]
  simp only [inv_mul_cancel₀ hr.ne', ENNReal.ofReal_one, one_smul]

/-- The ds/s measure in log radius. -/
def bellmanLogRadialHaar : Measure ℝ :=
  Measure.map bellmanLogRadiusHomeomorph bellmanRadialHaar

/-- The reference log-radius measure is finite on compact sets. -/
instance bellmanLogRadialHaar_finiteOnCompacts :
    IsFiniteMeasureOnCompacts bellmanLogRadialHaar where
  lt_top_of_isCompact K hK := by
    rw [bellmanLogRadialHaar, Measure.map_apply bellmanLogRadiusHomeomorph.measurable
      hK.measurableSet]
    have he : bellmanLogRadiusHomeomorph ⁻¹' K = bellmanLogRadiusHomeomorph.symm '' K := by
      ext q
      constructor
      · intro hq
        exact ⟨bellmanLogRadiusHomeomorph q, hq,
          bellmanLogRadiusHomeomorph.symm_apply_apply q⟩
      · rintro ⟨z, hz, rfl⟩
        change bellmanLogRadiusHomeomorph (bellmanLogRadiusHomeomorph.symm z) ∈ K
        rw [bellmanLogRadiusHomeomorph.apply_symm_apply]
        exact hz
    rw [he]
    exact (hK.image bellmanLogRadiusHomeomorph.symm.continuous).measure_lt_top

/-- Positive radial scaling gives actual translation invariance in log radius. -/
instance bellmanLogRadialHaar_addInvariant : IsAddLeftInvariant bellmanLogRadialHaar := by
  constructor
  intro a
  rw [bellmanLogRadialHaar,
    Measure.map_map (by fun_prop) bellmanLogRadiusHomeomorph.measurable]
  have he : (fun x : ℝ => a + x) ∘ bellmanLogRadiusHomeomorph =
      bellmanLogRadiusHomeomorph ∘ bellmanRadialScale (Real.exp a) (Real.exp_pos a) := by
    funext s
    change a + Real.log s.val = Real.log (Real.exp a * s.val)
    rw [Real.log_mul (Real.exp_ne_zero a) s.property.ne', Real.log_exp]
  rw [he, ← Measure.map_map bellmanLogRadiusHomeomorph.measurable
    (bellmanRadialScale (Real.exp a) (Real.exp_pos a)).measurable,
    map_bellmanRadialHaar_radialScale]

/-- The reference radial measure is nonzero. -/
theorem bellmanRadialHaar_ne_zero : bellmanRadialHaar ≠ 0 := by
  intro h
  have hac : bellmanPositiveTimeVolume ≪ bellmanRadialHaar :=
    withDensity_absolutelyContinuous' (by fun_prop) (ae_of_all _ fun s =>
      (ENNReal.ofReal_pos.mpr (inv_pos.mpr s.property)).ne')
  have hz : bellmanPositiveTimeVolume = 0 := by
    rw [h] at hac
    exact absolutelyContinuous_zero_iff.mp hac
  have hu := bellmanPositiveTimeVolume_univ
  rw [hz] at hu
  change (0 : ENNReal) = ⊤ at hu
  exact ENNReal.zero_ne_top hu

/-- The log-radius reference measure is nonzero. -/
theorem bellmanLogRadialHaar_ne_zero : bellmanLogRadialHaar ≠ 0 :=
  (Measure.map_ne_zero_iff bellmanLogRadiusHomeomorph.measurable.aemeasurable).mpr
    bellmanRadialHaar_ne_zero

/-- The finite Haar normalization factor of the literal log-radius reference measure. -/
def bellmanRadialHaarFactor : ℝ≥0 :=
  addHaarScalarFactor bellmanLogRadialHaar (volume : Measure ℝ)

/-- The actual log-radius reference measure is its finite Haar factor times volume. -/
theorem bellmanLogRadialHaar_eq_smul_volume :
    bellmanLogRadialHaar = bellmanRadialHaarFactor • (volume : Measure ℝ) :=
  isAddLeftInvariant_eq_smul bellmanLogRadialHaar volume

/-- The reference Haar factor is strictly positive, so normalization never divides by zero. -/
theorem bellmanRadialHaarFactor_ne_zero : bellmanRadialHaarFactor ≠ 0 := by
  intro h
  have he := bellmanLogRadialHaar_eq_smul_volume
  rw [h, zero_smul] at he
  exact bellmanLogRadialHaar_ne_zero he

end HypoellipticAleksandrov.KineticAleksandrov
