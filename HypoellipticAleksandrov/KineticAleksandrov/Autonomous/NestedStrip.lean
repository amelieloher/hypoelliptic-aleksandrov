module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripUnionPoint

/-! # The literal nested finite-union Green and exit decomposition for finite sources -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- The genuine nested-strip identities for a finite measure supported in the smaller open strip.
The source's strict lower-time support, omitted by the planned signature, is restored here. -/
theorem strip_nested
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : FiniteIntervalUnion)
    (hsub : H1.carrier ⊆ H2.carrier) (sMinus T : ℝ) (_hT : sMinus < T)
    (nu : Measure (FiniteUnionPole H1 (T : WithTop ℝ))) [IsFiniteMeasure nu]
    (hnu : ∀ᵐ e ∂nu, sMinus < e.1.time) :
    let nu2 := nu.map (finiteUnionNestedPoleInclusion H1 H2 hsub T)
    let tau := finiteUnionRestartPoleMeasure hH hLE hlam hLam A H1 H2 sMinus T nu
    finiteUnionGreenMixture hH hLE hlam hLam A H2 T nu2 =
      finiteUnionGreenMixture hH hLE hlam hLam A H1 T nu +
        finiteUnionGreenMixture hH hLE hlam hLam A H2 T tau ∧
    finiteUnionExitMixture hH hLE hlam hLam A H2 T nu2 =
      (finiteUnionExitMixture hH hLE hlam hLam A H1 T nu).restrict
        (finiteUnionExitSet H2 sMinus T) +
        finiteUnionExitMixture hH hLE hlam hLam A H2 T tau := by
  let inc := finiteUnionNestedPoleInclusion H1 H2 hsub (T : WithTop ℝ)
  let k := finiteUnionPointRestartPoles hH hLE hlam hLam A H1 H2 sMinus T
  have hinc : Measurable inc := measurable_finiteUnionNestedPoleInclusion H1 H2 hsub T
  have hk : Measurable k := finiteUnionPointRestartPoles_measurable
    hH hLE hlam hLam A H1 H2 sMinus T
  have hG1 := finiteUnionGreen_measurable hH hLE hlam hLam A H1 (T : WithTop ℝ)
  have hG2 := finiteUnionGreen_measurable hH hLE hlam hLam A H2 (T : WithTop ℝ)
  have hO1 := finiteUnionExit_measurable hH hLE hlam hLam A H1 T
  have hO2 := finiteUnionExit_measurable hH hLE hlam hLam A H2 T
  have hτ := finiteUnionRestartPoleMeasure_disintegration
    hH hLE hlam hLam A H1 H2 sMinus T nu
  have hpoint : ∀ᵐ e ∂nu,
      finiteUnionGreen hH hLE hlam hLam A H2 T (inc e) =
        finiteUnionGreen hH hLE hlam hLam A H1 T e +
          (k e).bind (finiteUnionGreen hH hLE hlam hLam A H2 T) ∧
      finiteUnionExit hH hLE hlam hLam A H2 T (inc e) =
        (finiteUnionExit hH hLE hlam hLam A H1 T e).restrict
          (finiteUnionExitSet H2 sMinus T) +
            (k e).bind (finiteUnionExit hH hLE hlam hLam A H2 T) := by
    filter_upwards [hnu] with e he
    exact strip_nested_union_point hH hLE hlam hLam A H1 H2 hsub sMinus T e he
  constructor
  · have hmap := nested_bind_map nu inc hinc _ hG2
    have hp := Measure.bind_congr_right (hpoint.mono (fun _ hp => hp.1))
    have hadd := nested_bind_add nu _ _ hG1 ((Measure.measurable_bind' hG2).comp hk)
    have hassoc := Measure.bind_bind hk.aemeasurable hG2.aemeasurable
      (m := nu)
    have hlast := congrArg (fun τ => τ.bind (finiteUnionGreen hH hLE hlam hLam A H2 T)) hτ
    exact hmap.trans (hp.trans (hadd.trans
      (congrArg₂ (· + ·) rfl (hassoc.symm.trans hlast.symm))))
  · have hmap := nested_bind_map nu inc hinc _ hO2
    have hp := Measure.bind_congr_right (hpoint.mono (fun _ hp => hp.2))
    have hrestrict := nested_bind_restrict nu _ hO1 (finiteUnionExitSet H2 sMinus T)
      (measurableSet_finiteUnionExitSet H2 sMinus T)
    have hadd := nested_bind_add nu _ _
      (nested_measurable_family_restrict _ hO1 _ (measurableSet_finiteUnionExitSet H2 sMinus T))
      ((Measure.measurable_bind' hO2).comp hk)
    have hassoc := Measure.bind_bind hk.aemeasurable hO2.aemeasurable (m := nu)
    have hlast := congrArg (fun τ => τ.bind (finiteUnionExit hH hLE hlam hLam A H2 T)) hτ
    exact hmap.trans (hp.trans (hadd.trans
      (congrArg₂ (· + ·) hrestrict.symm (hassoc.symm.trans hlast.symm))))

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
