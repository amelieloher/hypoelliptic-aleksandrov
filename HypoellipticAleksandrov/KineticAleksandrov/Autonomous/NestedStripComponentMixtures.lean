module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripComponentRestart

/-! # Actual restart mixtures are independent of certified component representations -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- Restart mixture transport through a certified component inclusion.
The Green and exit consumers discharge the component-family equality by their proved APIs. -/
theorem nested_restart_bind_component
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : FiniteIntervalUnion)
    (i : Fin H1.count) (j : Fin H2.count)
    (hsub : (H1.component i).carrier ⊆ (H2.component j).carrier) (sMinus T : ℝ)
    (e : StripPole (H1.component i) (T : WithTop ℝ)) (he : sMinus < e.1.time)
    (k : FiniteUnionPole H2 (T : WithTop ℝ) → Measure Point) (hk : Measurable k)
    (l : StripPole (H2.component j) (T : WithTop ℝ) → Measure Point)
    (hl : ∀ ep, k (componentPoleInclusion H2 j T ep) = l ep) :
    (finiteUnionPointRestartPoles hH hLE hlam hLam A H1 H2 sMinus T
      (componentPoleInclusion H1 i T e)).bind k =
      (nestedIntervalRestartPoles hH hLE hlam hLam A
        (H1.component i) (H2.component j) sMinus T e).bind l := by
  have hr := finiteUnionPointRestartPoles_component
    hH hLE hlam hLam A H1 H2 i j hsub sMinus T e he
  have h := congrArg (fun μ => μ.bind k) hr
  exact h.trans ((nested_bind_map _ _ (measurable_componentPoleInclusion H2 j T) k hk).trans
    (Measure.bind_congr_right (Filter.Eventually.of_forall hl)))

/-- A nested union inclusion and certified component inclusion are the same physical pole. -/
theorem finiteUnionNestedPoleInclusion_component
    (H1 H2 : FiniteIntervalUnion) (hsub : H1.carrier ⊆ H2.carrier)
    (i : Fin H1.count) (j : Fin H2.count)
    (hij : (H1.component i).carrier ⊆ (H2.component j).carrier) (T : WithTop ℝ)
    (e : StripPole (H1.component i) T) :
    finiteUnionNestedPoleInclusion H1 H2 hsub T (componentPoleInclusion H1 i T e) =
      componentPoleInclusion H2 j T
        (nestedPoleInclusion (H1.component i) (H2.component j) hij T e) := by
  apply Subtype.ext
  rfl

/-- The larger union and larger component exits give identical restrictions of a smaller exit. -/
theorem nested_component_outer_restriction
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : FiniteIntervalUnion)
    (i : Fin H1.count) (j : Fin H2.count)
    (hsub : (H1.component i).carrier ⊆ (H2.component j).carrier) (sMinus T : ℝ)
    (e : StripPole (H1.component i) (T : WithTop ℝ)) (he : sMinus < e.1.time) :
    (stripExit hH hLE hlam hLam A (H1.component i) T e).restrict
      (finiteUnionExitSet H2 sMinus T) =
      (stripExit hH hLE hlam hLam A (H1.component i) T e).restrict
        (reconstructionExit (H2.component j) sMinus T) := by
  apply Measure.restrict_congr_set
  filter_upwards [nested_exit_ae_larger_slab hH hLE hlam hLam A
    (H1.component i) (H2.component j) hsub sMinus T e he.le] with p hp
  exact propext (H2.exit_on_component_closure j sMinus T p hp.2.2)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
