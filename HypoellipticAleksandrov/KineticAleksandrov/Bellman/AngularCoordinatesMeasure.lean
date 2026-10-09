module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularCoordinates
import Mathlib.Topology.Maps.Basic
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Tactic

/-! # The open coordinate embedding and the exact restricted-measure bridge -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set Topology

/-- The positive-position half-plane embeds in the actual punctured plane. -/
def bellmanPositivePositionInclusion (q : BellmanPositivePositionPlane) :
    BellmanPuncturedPlane := ⟨q.val, by
  intro h
  have hx := congrArg Prod.fst h
  exact q.property.ne' hx⟩

/-- The positive-position inclusion is an open embedding. -/
theorem isOpenEmbedding_bellmanPositivePositionInclusion :
    IsOpenEmbedding bellmanPositivePositionInclusion := by
  have hpunct : IsOpenEmbedding (Subtype.val : BellmanPuncturedPlane → ℝ × ℝ) :=
    isOpen_compl_singleton.isOpenEmbedding_subtypeVal
  apply IsOpenEmbedding.of_comp bellmanPositivePositionInclusion hpunct
  change IsOpenEmbedding (Subtype.val : BellmanPositivePositionPlane → ℝ × ℝ)
  exact (isOpen_lt continuous_const continuous_fst).isOpenEmbedding_subtypeVal

/-- The literal coordinate point is the positive-position inclusion after the homeomorphism. -/
theorem bellmanAngularPoint_eq_comp :
    bellmanAngularPoint = bellmanPositivePositionInclusion ∘ bellmanAngularHomeomorph := rfl

/-- The source coordinates form an open embedding into the punctured plane. -/
theorem isOpenEmbedding_bellmanAngularPoint : IsOpenEmbedding bellmanAngularPoint := by
  rw [bellmanAngularPoint_eq_comp]
  exact isOpenEmbedding_bellmanPositivePositionInclusion.comp
    bellmanAngularHomeomorph.isOpenEmbedding

/-- The angular coordinate image is exactly the positive-position portion of the carrier. -/
theorem range_bellmanAngularPoint :
    range bellmanAngularPoint = {q : BellmanPuncturedPlane | 0 < q.val.1} := by
  ext q
  constructor
  · rintro ⟨w, rfl⟩
    exact pow_pos w.1.property 3
  · intro hq
    let z : BellmanPositivePositionPlane := ⟨q.val, hq⟩
    refine ⟨bellmanAngularHomeomorph.symm z, ?_⟩
    rw [bellmanAngularPoint_eq_comp, Function.comp_apply,
      bellmanAngularHomeomorph.apply_symm_apply]
    apply Subtype.ext
    rfl

/-- Pullback along the literal source coordinates, retaining possible angular singular
measures. -/
def bellmanAngularPullback (μ : Measure BellmanPuncturedPlane) :
    Measure (BellmanPositiveTime × ℝ) := Measure.comap bellmanAngularPoint μ

/-- Mapping the coordinate pullback recovers precisely restriction to positive position. -/
theorem map_bellmanAngularPullback (μ : Measure BellmanPuncturedPlane) :
    Measure.map bellmanAngularPoint (bellmanAngularPullback μ) =
      μ.restrict {q | 0 < q.val.1} := by
  rw [bellmanAngularPullback,
    isOpenEmbedding_bellmanAngularPoint.measurableEmbedding.map_comap,
    range_bellmanAngularPoint]

/-- Pulling back a locally finite measure gives a locally finite coordinate measure. -/
theorem bellmanAngularPullback_finiteOnCompacts (μ : Measure BellmanPuncturedPlane)
    (hμ : IsFiniteMeasureOnCompacts μ) : IsFiniteMeasureOnCompacts (bellmanAngularPullback μ) := by
  let : IsFiniteMeasureOnCompacts μ := hμ
  exact IsFiniteMeasureOnCompacts.comap' μ continuous_bellmanAngularPoint
    isOpenEmbedding_bellmanAngularPoint.measurableEmbedding

end HypoellipticAleksandrov.KineticAleksandrov
