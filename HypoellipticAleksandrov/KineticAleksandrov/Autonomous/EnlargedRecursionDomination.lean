module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionFinite
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationWaiting
import Mathlib.Tactic

/-! # Active occupations and outer exits in the finite alternating decomposition

The lower observation endpoint is included in the canonical enlarged recursion.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory

/-- Actual active Green mixtures are supported in the open active velocity interval. -/
theorem enlargedGreenMixture_ae_active
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (T : ℝ)
    (mu : Measure Point) :
    ∀ᵐ q ∂(enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) T ∘ₘ mu),
      q.velocity 0 ∈ c.active := by
  classical
  apply Measure.ae_comp_of_ae_ae
    (isOpen_Ioo.measurableSet.preimage ((continuous_apply 0).comp continuous_velocity).measurable)
  apply Filter.Eventually.of_forall
  intro p
  change ∀ᵐ q ∂(if hp : p ∈ enlargedVisitPoleSet (visitActiveUnion c J) T then
    finiteUnionGreen hH hLE hlam hLam A (visitActiveUnion c J) T
      (enlargedVisitPole _ T ⟨p, hp⟩) else 0), q.velocity 0 ∈ c.active
  split
  · rename_i hp
    exact (visitUnionGreen_ae_velocity hH hLE hlam hLam A (visitActiveUnion c J) T
      (enlargedVisitPole _ T ⟨p, hp⟩)).mono fun q hq =>
        ((visitActiveUnion_carrier c J).le hq).1
  · simp only [ae_zero, Filter.eventually_bot]

/-- Literal finite-piece active domination in the source open physical observation strip. -/
theorem enlarged_piece_domination
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ) (P : Point)
    (hP : s ≤ P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier) (N : ℕ) :
    let gamma := enlargedVisitEntrance hH hLE hlam hLam A c J s T P
    let GA := enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) T
    let EA := enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) T
    let GO := enlargedVisitGreenKernel hH hLE hlam hLam A J.toFiniteUnion T
    let outer := finiteUnionExitSet J.toFiniteUnion s T
    (∑ n ∈ Finset.range N, ((EA ∘ₘ gamma n).restrict outer)) univ ≤ 1 ∧
      (∑ n ∈ Finset.range N, GA ∘ₘ gamma n) ≤
        (GO P).restrict {p | p.velocity 0 ∈ c.active} := by
  classical
  dsimp only
  let gamma := enlargedVisitEntrance hH hLE hlam hLam A c J s T P
  let GA := enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) T
  let GW := enlargedVisitGreenKernel hH hLE hlam hLam A (visitWaitingUnion c J) T
  let GO := enlargedVisitGreenKernel hH hLE hlam hLam A J.toFiniteUnion T
  let EA := enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) T
  let EW := enlargedVisitExitKernel hH hLE hlam hLam A (visitWaitingUnion c J) T
  let EO := enlargedVisitExitKernel hH hLE hlam hLam A J.toFiniteUnion T
  let beta := enlargedVisitOutgoing hH hLE hlam hLam A c J s T P
  let outer := finiteUnionExitSet J.toFiniteUnion s T
  have hT : s < T := hP.1.trans_lt hP.2.1
  have hG := enlargedAlternating_green hH hLE hlam hLam A c J s T hT P hP N
  have hE := enlargedAlternating_exit hH hLE hlam hLam A c J s T hT P hP N
  have hGle : (∑ n ∈ Finset.range N, GA ∘ₘ gamma n) ≤ GO P := by
    rw [hG]
    calc
      _ ≤ ∑ n ∈ Finset.range N, (GA ∘ₘ gamma n + GW ∘ₘ beta n) :=
        Finset.sum_le_sum (fun _ _ => le_add_of_nonneg_right (Measure.zero_le _))
      _ ≤ _ := (le_add_of_nonneg_left (Measure.zero_le _)).trans
        (le_add_of_nonneg_right (Measure.zero_le _))
  have hEle : (∑ n ∈ Finset.range N, (EA ∘ₘ gamma n).restrict outer) ≤ EO P := by
    rw [hE]
    calc
      _ ≤ ∑ n ∈ Finset.range N,
          ((EA ∘ₘ gamma n).restrict outer + (EW ∘ₘ beta n).restrict outer) :=
        Finset.sum_le_sum (fun _ _ => le_add_of_nonneg_right (Measure.zero_le _))
      _ ≤ _ := (le_add_of_nonneg_left (Measure.zero_le _)).trans
        (le_add_of_nonneg_right (Measure.zero_le _))
  have hmass : EO P univ = 1 := by
    have hp : P ∈ enlargedVisitPoleSet J.toFiniteUnion T :=
      ⟨hP.2.1, by simpa only [Interval.toFiniteUnion_carrier] using hP.2.2⟩
    change (if h : P ∈ enlargedVisitPoleSet J.toFiniteUnion T then
      finiteUnionExit hH hLE hlam hLam A J.toFiniteUnion T
        (enlargedVisitPole _ T ⟨P, h⟩) else 0) univ = 1
    rw [dite_eq_left hp, measure_univ]
  refine ⟨(hEle univ).trans_eq hmass, ?_⟩
  have hs : ∀ᵐ p ∂(∑ n ∈ Finset.range N, GA ∘ₘ gamma n), p.velocity 0 ∈ c.active := by
    apply ae_finsetSum_measure_iff.mpr
    intro n _
    exact enlargedGreenMixture_ae_active hH hLE hlam hLam A c J T (gamma n)
  have hrestrict := Measure.restrict_mono (subset_refl {p : Point | p.velocity 0 ∈ c.active})
    hGle
  have hr : (∑ n ∈ Finset.range N, GA ∘ₘ gamma n).restrict
      {p | p.velocity 0 ∈ c.active} = ∑ n ∈ Finset.range N, GA ∘ₘ gamma n :=
    Measure.restrict_eq_self_of_ae_mem hs
  rw [hr] at hrestrict
  exact hrestrict

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
