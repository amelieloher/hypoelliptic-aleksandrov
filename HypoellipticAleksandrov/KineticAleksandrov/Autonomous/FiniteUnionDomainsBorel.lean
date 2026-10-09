module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FiniteUnionDomainsMeasures

/-! # Borel dependence of componentwise union measures -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open scoped ENNReal

/-- A measurable family on each certified component is measurable on the physical union. -/
theorem finiteUnion_component_family_measurable
    (H : FiniteIntervalUnion) (T : WithTop ℝ)
    (f : ∀ i : Fin H.count, StripPole (H.component i) T → Measure Point)
    (hf : ∀ i, Measurable (f i)) :
    Measurable (fun e : FiniteUnionPole H T =>
      f (finiteUnionPoleIndex H T e) (finiteUnionComponentPole H T e)) := by
  classical
  apply Measure.measurable_measure.mpr
  intro B hB
  let D (i : Fin H.count) : Set (FiniteUnionPole H T) :=
    {e | e.1.velocity 0 ∈ (H.component i).carrier}
  have hD (i : Fin H.count) : MeasurableSet (D i) :=
    isOpen_Ioo.measurableSet.preimage
      (((continuous_apply 0).comp continuous_velocity).measurable.comp measurable_subtype_coe)
  let g (i : Fin H.count) (e : FiniteUnionPole H T) : ℝ≥0∞ :=
    if h : e ∈ D i then f i ⟨e.1, e.2.1, h⟩ B else 0
  have hg (i : Fin H.count) : Measurable (g i) := by
    have hp : Measurable (fun e : D i => (⟨e.1.1, e.1.2.1, e.2⟩ :
        StripPole (H.component i) T)) :=
      (measurable_subtype_coe.comp measurable_subtype_coe).subtype_mk
    exact Measurable.dite
      (((Measure.measurable_measure.mp (hf i)) B hB).comp hp) measurable_const (hD i)
  have heq (e : FiniteUnionPole H T) :
      f (finiteUnionPoleIndex H T e) (finiteUnionComponentPole H T e) B =
        ∑ i : Fin H.count, g i e := by
    symm
    rw [Finset.sum_eq_single (finiteUnionPoleIndex H T e)]
    · dsimp only [g]
      have hmem : e ∈ D (finiteUnionPoleIndex H T e) := H.mem_componentIndex _ e.2.2
      rw [dite_eq_left hmem]
      rfl
    · intro j _ hji
      dsimp only [g]
      rw [dite_eq_right]
      intro hj
      exact hji (H.componentIndex_eq e.2.2 j hj).symm
    · intro hn
      exact False.elim (hn (Finset.mem_univ _))
  have hm : Measurable (fun e => ∑ i : Fin H.count, g i e) :=
    Finset.measurable_sum _ (fun i _ => hg i)
  have hfun : (fun e : FiniteUnionPole H T =>
      f (finiteUnionPoleIndex H T e) (finiteUnionComponentPole H T e) B) =
        fun e => ∑ i : Fin H.count, g i e := funext heq
  rw [hfun]
  exact hm

/-- The actual Green family of a finite union has Borel pole dependence. -/
theorem finiteUnionGreen_measurable
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion) (T : WithTop ℝ) :
    Measurable (finiteUnionGreen hH hLE hlam hLam A H T) := by
  unfold finiteUnionGreen
  exact finiteUnion_component_family_measurable H T
    (fun i => stripGreen hH hLE hlam hLam A (H.component i) T)
    (fun i => Measure.measurable_measure.mpr
      (stripGreen_measurable_apply hH hLE hlam hLam A (H.component i) T))

/-- The actual finite-horizon exit family of a finite union has Borel pole dependence. -/
theorem finiteUnionExit_measurable
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion) (T : ℝ) :
    Measurable (finiteUnionExit hH hLE hlam hLam A H T) := by
  unfold finiteUnionExit
  exact finiteUnion_component_family_measurable H T
    (fun i => stripExit hH hLE hlam hLam A (H.component i) T)
    (fun i => stripExit_measurable hH hLE hlam hLam A (H.component i) T)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
