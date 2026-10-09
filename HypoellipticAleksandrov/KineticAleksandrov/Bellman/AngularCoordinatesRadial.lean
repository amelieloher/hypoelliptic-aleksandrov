module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDisintegrationDensity
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularCoordinates
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic

/-! # Local finiteness of the literal degree-dependent radial measure -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Measure Set

/-- The literal radial weight is finite on compact subsets of positive radius. -/
instance bellmanRadialWeight_finiteOnCompacts (β : ℝ) :
    IsFiniteMeasureOnCompacts (bellmanRadialWeight β) := by
  apply bellman_withDensity_finiteOnCompacts
  apply Continuous.rpow_const continuous_subtype_val
  intro s
  exact Or.inl s.property.ne'

/-- The literal radial weight is sigma finite. -/
instance bellmanRadialWeight_sigmaFinite (β : ℝ) : SigmaFinite (bellmanRadialWeight β) := by
  let : LocallyCompactSpace BellmanPositiveTime := isOpen_Ioi.locallyCompactSpace
  infer_instance

/-- Positive radial Lebesgue measure gives positive mass to every nonempty open radial set. -/
instance bellmanPositiveTimeVolume_isOpenPosMeasure :
    IsOpenPosMeasure bellmanPositiveTimeVolume := by
  constructor
  intro U hU hUne
  have he : Topology.IsOpenEmbedding (Subtype.val : BellmanPositiveTime → ℝ) :=
    isOpen_Ioi.isOpenEmbedding_subtypeVal
  have ho : IsOpen (Subtype.val '' U : Set ℝ) := he.isOpen_iff_image_isOpen.mp hU
  rw [bellmanPositiveTimeVolume, he.measurableEmbedding.comap_apply,
    Measure.restrict_apply ho.measurableSet]
  have hs : (Subtype.val '' U : Set ℝ) ⊆ Ioi (0 : ℝ) := by
    rintro s ⟨t, _, rfl⟩
    exact t.property
  rw [inter_eq_left.mpr hs]
  exact (ho.measure_pos volume (hUne.image Subtype.val)).ne'

/-- The source radial measure is positive on every nonempty open radial set. -/
instance bellmanRadialWeight_isOpenPosMeasure (β : ℝ) :
    IsOpenPosMeasure (bellmanRadialWeight β) := by
  have hm : Measurable (fun s : BellmanPositiveTime =>
      ENNReal.ofReal (s.val ^ (3 - β))) := by fun_prop
  have hn : ∀ᵐ s ∂bellmanPositiveTimeVolume,
      ENNReal.ofReal (s.val ^ (3 - β)) ≠ 0 :=
    ae_of_all _ fun s => (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos s.property _)).ne'
  have hac := withDensity_absolutelyContinuous' hm.aemeasurable hn
  constructor
  intro U hU hUne hz
  exact (hU.measure_pos bellmanPositiveTimeVolume hUne).ne'
    (hac hz)

end HypoellipticAleksandrov.KineticAleksandrov
