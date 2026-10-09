module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDisintegrationComparison
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.PairSetting

/-! # Angular disintegration of actual homogeneous stationary Radon pairs -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- Homogeneous compared Radon measures have the exact source angular representation. -/
theorem angular_disintegration (R β : ℝ) (_hR : 1 ≤ R) (_hβ : 3 ≤ β)
    (μ η : Measure BellmanPuncturedPlane) (hp : IsBellmanAdjointPair 1 R β μ η) :
    ∃ F H : Measure ℝ,
      (μ.restrict {q | 0 < q.val.1} = bellmanAngularRep β F ∧
        η.restrict {q | 0 < q.val.1} = bellmanAngularRep β H) ∧
      IsFiniteMeasureOnCompacts F ∧ Measure.InnerRegular F ∧
      IsFiniteMeasureOnCompacts H ∧ Measure.InnerRegular H ∧ F ≤ H ∧
      H ≤ ENNReal.ofReal R • F := by
  refine ⟨bellmanAngularMeasure β μ, bellmanAngularMeasure β η, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨bellmanAngularMeasure_representation β μ hp.1.1 hp.2.2.2.2.2.2.1,
      bellmanAngularMeasure_representation β η hp.2.1.1 hp.2.2.2.2.2.2.2⟩
  · exact bellmanAngularMeasure_finiteOnCompacts β μ hp.1.1
  · exact bellmanAngularMeasure_innerRegular β μ hp.1.1
  · exact bellmanAngularMeasure_finiteOnCompacts β η hp.2.1.1
  · exact bellmanAngularMeasure_innerRegular β η hp.2.1.1
  · apply bellmanAngularMeasure_mono
    simpa only [ENNReal.ofReal_one, one_smul] using hp.2.2.2.1
  · rw [← bellmanAngularMeasure_smul]
    exact bellmanAngularMeasure_mono β hp.2.2.2.2.1

end HypoellipticAleksandrov.KineticAleksandrov
