module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripUnionRestart
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FiniteUnionDomainsClosedComponent
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripExit

/-! # Component independence of the genuine internal-exit restart measure -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- The certified component pole inclusion is measurable in the existing subtype carrier. -/
theorem measurable_componentPoleInclusion (H : FiniteIntervalUnion) (i : Fin H.count)
    (T : WithTop ℝ) : Measurable (componentPoleInclusion H i T) :=
  measurable_subtype_coe.subtype_mk

/-- The actual union restart on a component is the image of that component's actual restart. -/
theorem finiteUnionPointRestartPoles_component
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : FiniteIntervalUnion)
    (i : Fin H1.count) (j : Fin H2.count)
    (hsub : (H1.component i).carrier ⊆ (H2.component j).carrier) (sMinus T : ℝ)
    (e : StripPole (H1.component i) (T : WithTop ℝ)) (he : sMinus < e.1.time) :
    finiteUnionPointRestartPoles hH hLE hlam hLam A H1 H2 sMinus T
      (componentPoleInclusion H1 i T e) =
      (nestedIntervalRestartPoles hH hLE hlam hLam A
        (H1.component i) (H2.component j) sMinus T e).map (componentPoleInclusion H2 j T) := by
  apply MeasurableEmbedding.map_injective (MeasurableEmbedding.subtype_coe
    (measurableSet_finiteUnionPole H2 T))
  have hback : ((nestedIntervalRestartPoles hH hLE hlam hLam A
      (H1.component i) (H2.component j) sMinus T e).map
        (componentPoleInclusion H2 j T)).map Subtype.val =
      (stripExit hH hLE hlam hLam A (H1.component i) T e).restrict
        (nestedIntervalInternalExit (H1.component i) (H2.component j) sMinus T) := by
    rw [Measure.map_map measurable_subtype_coe (measurable_componentPoleInclusion H2 j T)]
    exact nestedIntervalRestartPoles_map hH hLE hlam hLam A
      (H1.component i) (H2.component j) sMinus T e
  have hΩ := finiteUnionExit_component hH hLE hlam hLam A H1 i T e
  have hrestrict : (stripExit hH hLE hlam hLam A (H1.component i) T e).restrict
      (finiteUnionInternalExit H1 H2 sMinus T) =
      (stripExit hH hLE hlam hLam A (H1.component i) T e).restrict
        (nestedIntervalInternalExit (H1.component i) (H2.component j) sMinus T) := by
    apply Measure.restrict_congr_set
    have hp : ∀ᵐ p ∂stripExit hH hLE hlam hLam A (H1.component i) T e,
        p ∈ reconstructionExit (H1.component i) sMinus T := by
      rw [ae_iff]
      exact (strip_exit_probability hH hLE hlam hLam A (H1.component i) sMinus T e he.le).2.1
    filter_upwards [hp] with p hp
    exact propext (finiteUnionInternalExit_on_component_exit H1 H2 i j hsub sMinus T p hp)
  exact (finiteUnionPointRestartPoles_map hH hLE hlam hLam A H1 H2 sMinus T
    (componentPoleInclusion H1 i T e)).trans
      ((congrArg (fun μ : Measure Point => μ.restrict
        (finiteUnionInternalExit H1 H2 sMinus T)) hΩ).trans (hrestrict.trans hback.symm))

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
