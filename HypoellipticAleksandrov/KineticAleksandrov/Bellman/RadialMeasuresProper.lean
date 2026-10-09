module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.RadialMeasures
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.PairSetting
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AnnularNormalizationGeometry
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Tactic

/-! # Proper radial projection and local finiteness of the literal adjoint measures -/

@[expose] public section
noncomputable section
open MeasureTheory Set
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- On the punctured plane the gauge is a continuous positive radius coordinate. -/
def bellmanGaugeRadius (q : BellmanPuncturedPlane) : BellmanPositiveTime :=
  ⟨bellmanGauge q.val, bellmanGauge_pos q.val q.property⟩

/-- The positive gauge radius is continuous. -/
theorem continuous_bellmanGaugeRadius : Continuous bellmanGaugeRadius :=
  (bellmanGauge_continuous.comp continuous_subtype_val).subtype_mk _

/-- The source radial projection is proper because its radius is recovered by the gauge. -/
theorem isProperMap_sphereRadialPoint (lam Lam : ℝ) :
    IsProperMap (sphereRadialPoint (lam := lam) (Lam := Lam)) := by
  apply isProperMap_of_comp_of_t2 (continuous_sphereRadialPoint lam Lam)
    continuous_bellmanGaugeRadius
  have he : bellmanGaugeRadius ∘ (sphereRadialPoint (lam := lam) (Lam := Lam)) =
      Prod.fst := by
    funext w
    exact Subtype.ext (sphereRadialPoint_gauge w)
  rw [he]
  exact isProperMap_fst_of_compactSpace

/-- A proper continuous map preserves finite mass on compact subsets. -/
theorem bellman_proper_map_finiteOnCompacts {A B : Type*}
    [TopologicalSpace A] [TopologicalSpace B] [MeasurableSpace A] [MeasurableSpace B]
    [BorelSpace A] [BorelSpace B] [T2Space B]
    (f : A → B) (hf : IsProperMap f) (mu : Measure A)
    [IsFiniteMeasureOnCompacts mu] : IsFiniteMeasureOnCompacts (Measure.map f mu) where
  lt_top_of_isCompact K hK := by
    rw [Measure.map_apply hf.continuous.measurable hK.measurableSet]
    exact (hf.isCompact_preimage hK).measure_lt_top

/-- The first radial measure is finite on compact subsets of the punctured plane. -/
instance radialMu_finiteOnCompacts {lam Lam : ℝ} (alpha : ℝ)
    (pi : Measure (BellmanSphere × BellmanCoefficient lam Lam)) [IsFiniteMeasure pi] :
    IsFiniteMeasureOnCompacts (radialMu alpha pi) :=
  bellman_proper_map_finiteOnCompacts _ (isProperMap_sphereRadialPoint lam Lam) _

/-- The coefficient-weighted product is finite on compact subsets before projection. -/
theorem bellmanRadialEtaProduct_finiteOnCompacts {lam Lam : ℝ} (alpha : ℝ)
    (pi : Measure (BellmanSphere × BellmanCoefficient lam Lam)) [IsFiniteMeasure pi] :
    IsFiniteMeasureOnCompacts (((bellmanRadiusMeasure alpha).prod pi).withDensity
      (fun w => ENNReal.ofReal w.2.2.val)) := by
  have hf : Continuous (fun w : BellmanPositiveTime ×
      (BellmanSphere × BellmanCoefficient lam Lam) => w.2.2.val) := by fun_prop
  exact bellman_withDensity_finiteOnCompacts ((bellmanRadiusMeasure alpha).prod pi) _ hf

/-- The second radial measure is finite on compact subsets of the punctured plane. -/
instance radialEta_finiteOnCompacts {lam Lam : ℝ} (alpha : ℝ)
    (pi : Measure (BellmanSphere × BellmanCoefficient lam Lam)) [IsFiniteMeasure pi] :
    IsFiniteMeasureOnCompacts (radialEta alpha pi) := by
  let := bellmanRadialEtaProduct_finiteOnCompacts alpha pi
  exact bellman_proper_map_finiteOnCompacts _ (isProperMap_sphereRadialPoint lam Lam) _

/-- Both radial measures have the required Radon regularity on the actual punctured carrier. -/
theorem radial_bellman_measures_radon {lam Lam : ℝ} (alpha : ℝ)
    (pi : Measure (BellmanSphere × BellmanCoefficient lam Lam)) [IsFiniteMeasure pi] :
    IsBellmanRadon (radialMu alpha pi) ∧ IsBellmanRadon (radialEta alpha pi) := by
  let : LocallyCompactSpace BellmanPuncturedPlane :=
    isOpen_compl_singleton.locallyCompactSpace
  exact ⟨⟨inferInstance, inferInstance⟩, ⟨inferInstance, inferInstance⟩⟩

end HypoellipticAleksandrov.KineticAleksandrov
