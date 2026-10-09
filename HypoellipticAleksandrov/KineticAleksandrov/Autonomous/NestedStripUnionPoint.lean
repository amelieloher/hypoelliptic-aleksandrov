module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripComponentMixtures

/-! # The literal nested Green and exit identities at a finite-union starting pole -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- Both actual union measure identities hold on every certified nested component. -/
theorem nested_union_component_identity
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : FiniteIntervalUnion)
    (hsub : H1.carrier ⊆ H2.carrier) (i : Fin H1.count) (j : Fin H2.count)
    (hij : (H1.component i).carrier ⊆ (H2.component j).carrier) (sMinus T : ℝ)
    (e : StripPole (H1.component i) (T : WithTop ℝ)) (he : sMinus < e.1.time) :
    let ep := componentPoleInclusion H1 i T e
    let eb := finiteUnionNestedPoleInclusion H1 H2 hsub T ep
    let τ := finiteUnionPointRestartPoles hH hLE hlam hLam A H1 H2 sMinus T ep
    finiteUnionGreen hH hLE hlam hLam A H2 T eb =
      finiteUnionGreen hH hLE hlam hLam A H1 T ep +
        τ.bind (finiteUnionGreen hH hLE hlam hLam A H2 T) ∧
    finiteUnionExit hH hLE hlam hLam A H2 T eb =
      (finiteUnionExit hH hLE hlam hLam A H1 T ep).restrict
        (finiteUnionExitSet H2 sMinus T) + τ.bind (finiteUnionExit hH hLE hlam hLam A H2 T) := by
  dsimp only
  let e2 := nestedPoleInclusion (H1.component i) (H2.component j) hij T e
  have hp := finiteUnionNestedPoleInclusion_component H1 H2 hsub i j hij T e
  have hGb := (congrArg (finiteUnionGreen hH hLE hlam hLam A H2 T) hp).trans
    (finiteUnionGreen_component hH hLE hlam hLam A H2 j T e2)
  have hOb := (congrArg (finiteUnionExit hH hLE hlam hLam A H2 T) hp).trans
    (finiteUnionExit_component hH hLE hlam hLam A H2 j T e2)
  have hGs := finiteUnionGreen_component hH hLE hlam hLam A H1 i T e
  have hOs := finiteUnionExit_component hH hLE hlam hLam A H1 i T e
  have hGτ := nested_restart_bind_component hH hLE hlam hLam A H1 H2 i j hij sMinus T e he
    (finiteUnionGreen hH hLE hlam hLam A H2 T)
    (finiteUnionGreen_measurable hH hLE hlam hLam A H2 T)
    (stripGreen hH hLE hlam hLam A (H2.component j) T)
    (fun ep => finiteUnionGreen_component hH hLE hlam hLam A H2 j T ep)
  have hOτ := nested_restart_bind_component hH hLE hlam hLam A H1 H2 i j hij sMinus T e he
    (finiteUnionExit hH hLE hlam hLam A H2 T)
    (finiteUnionExit_measurable hH hLE hlam hLam A H2 T)
    (stripExit hH hLE hlam hLam A (H2.component j) T)
    (fun ep => finiteUnionExit_component hH hLE hlam hLam A H2 j T ep)
  have houter := (congrArg (fun μ : Measure Point =>
    μ.restrict (finiteUnionExitSet H2 sMinus T)) hOs).trans
      (nested_component_outer_restriction hH hLE hlam hLam A H1 H2 i j hij sMinus T e he)
  constructor
  · exact hGb.trans ((nestedIntervalGreen_identity hH hLE hlam hLam A
      (H1.component i) (H2.component j) hij sMinus T e he).trans
        (congrArg₂ (· + ·) hGs.symm hGτ.symm))
  · exact hOb.trans ((nestedIntervalExit_identity hH hLE hlam hLam A
      (H1.component i) (H2.component j) hij sMinus T e he).trans
        (congrArg₂ (· + ·) houter.symm hOτ.symm))

/-- The literal nested identities hold for every physical pole of a finite interval union. -/
theorem strip_nested_union_point
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : FiniteIntervalUnion)
    (hsub : H1.carrier ⊆ H2.carrier) (sMinus T : ℝ)
    (e : FiniteUnionPole H1 (T : WithTop ℝ)) (he : sMinus < e.1.time) :
    finiteUnionGreen hH hLE hlam hLam A H2 T
      (finiteUnionNestedPoleInclusion H1 H2 hsub T e) =
      finiteUnionGreen hH hLE hlam hLam A H1 T e +
        (finiteUnionPointRestartPoles hH hLE hlam hLam A H1 H2 sMinus T e).bind
          (finiteUnionGreen hH hLE hlam hLam A H2 T) ∧
    finiteUnionExit hH hLE hlam hLam A H2 T
      (finiteUnionNestedPoleInclusion H1 H2 hsub T e) =
      (finiteUnionExit hH hLE hlam hLam A H1 T e).restrict (finiteUnionExitSet H2 sMinus T) +
        (finiteUnionPointRestartPoles hH hLE hlam hLam A H1 H2 sMinus T e).bind
          (finiteUnionExit hH hLE hlam hLam A H2 T) := by
  let i := finiteUnionPoleIndex H1 T e
  let ep := finiteUnionComponentPole H1 T e
  obtain ⟨j, hij⟩ := H1.component_contained H2 hsub i
  have hh := nested_union_component_identity hH hLE hlam hLam A H1 H2 hsub i j hij
    sMinus T ep he
  have heq : componentPoleInclusion H1 i T ep = e := by apply Subtype.ext; rfl
  dsimp only at hh
  rw [heq] at hh
  exact hh

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
