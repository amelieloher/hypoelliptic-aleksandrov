module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDisintegrationReweight
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDisintegrationFactorization
import Mathlib.Tactic

/-! # Factorization of the actual homogeneous measure after degree reweighting -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- The actual reweighted log-coordinate measure remains finite on compact sets. -/
theorem bellmanLogAngularMeasure_finiteOnCompacts (β : ℝ)
    (μ : Measure BellmanPuncturedPlane) (hμ : IsFiniteMeasureOnCompacts μ) :
    IsFiniteMeasureOnCompacts (bellmanLogAngularMeasure β μ) := by
  let : IsFiniteMeasureOnCompacts (bellmanAngularPullback μ) :=
    bellmanAngularPullback_finiteOnCompacts μ hμ
  have hw : Continuous (fun w : BellmanPositiveTime × ℝ => w.1.val ^ (β - 4)) := by
    apply Continuous.rpow_const
    · fun_prop
    · intro w
      exact Or.inl w.1.property.ne'
  let : IsFiniteMeasureOnCompacts
      ((bellmanAngularPullback μ).withDensity (bellmanRadialDegreeWeight β)) :=
    bellman_withDensity_finiteOnCompacts (bellmanAngularPullback μ) _ hw
  exact bellman_map_homeomorph_finiteOnCompacts bellmanLogAngularHomeomorph _

/-- Homogeneity alone produces a literal angular measure after passing to log radius. -/
theorem bellmanLogAngularMeasure_factorization (β : ℝ)
    (μ : Measure BellmanPuncturedPlane) (hμ : IsFiniteMeasureOnCompacts μ)
    (hd : HasBellmanDensityDegree β μ) :
    bellmanLogAngularMeasure β μ =
      (volume : Measure ℝ).prod (bellmanUnitSection (bellmanLogAngularMeasure β μ)) := by
  let : IsFiniteMeasureOnCompacts (bellmanLogAngularMeasure β μ) :=
    bellmanLogAngularMeasure_finiteOnCompacts β μ hμ
  exact bellman_translation_factorization _ hd.logAngularMeasure_invariant

end HypoellipticAleksandrov.KineticAleksandrov
