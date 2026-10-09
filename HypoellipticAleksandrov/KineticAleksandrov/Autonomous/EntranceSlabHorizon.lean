module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EntranceSlabIntegrated
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonGreen

/-! # Exact horizon clipping of the active Green kernels -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory ProbabilityTheory HypoellipticAleksandrov

/-- Componentwise finite-union Green measures retain the exact physical horizon restriction. -/
theorem entranceSlab_unionGreen_horizon_restrict
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion) (b T : ℝ)
    (hBT : b ≤ T) (p : Point) (hb : p.time < b) (hv : p.velocity 0 ∈ H.carrier) :
    finiteUnionGreen hH hLE hlam hLam A H b (enlargedVisitPole H b ⟨p, hb, hv⟩) =
      (finiteUnionGreen hH hLE hlam hLam A H T
        (enlargedVisitPole H T ⟨p, hb.trans_le hBT, hv⟩)).restrict {q | q.time < b} := by
  let ep := enlargedVisitPole H T ⟨p, hb.trans_le hBT, hv⟩
  let i := finiteUnionPoleIndex H T ep
  let e := stripPoleInfinite (H.component i) T (finiteUnionComponentPole H T ep)
  have he : enlargedVisitPole H b ⟨p, hb, hv⟩ =
      componentPoleInclusion H i b (stripPoleFinite (H.component i) e b hb) :=
    Subtype.ext rfl
  rw [he, finiteUnionGreen_component]
  change stripGreen hH hLE hlam hLam A (H.component i) b
      (stripPoleFinite (H.component i) e b hb) =
    (stripGreen hH hLE hlam hLam A (H.component i) T
      (stripPoleFinite (H.component i) e T (hb.trans_le hBT))).restrict {q | q.time < b}
  rw [stripGreen_finite_restrict_infinite hH hLE hlam hLam A (H.component i) e b hb,
    stripGreen_finite_restrict_infinite hH hLE hlam hLam A (H.component i) e T
      (hb.trans_le hBT),
    Measure.restrict_restrict (isOpen_lt continuous_time continuous_const).measurableSet,
    inter_eq_left.mpr (show {q : Point | q.time < b} ⊆ {q | q.time < T} from
      fun _ hq => hq.trans_le hBT)]

/-- Clipping a Green kernel at `b` only removes occupation after `b`. -/
theorem entranceSlab_greenKernel_horizon_le
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion) (b T : ℝ)
    (hBT : b ≤ T) (p : Point) :
    enlargedVisitGreenKernel hH hLE hlam hLam A H b p ≤
      (enlargedVisitGreenKernel hH hLE hlam hLam A H T p).restrict {q | q.time < b} := by
  classical
  by_cases hp : p ∈ enlargedVisitPoleSet H b
  · have hpT : p ∈ enlargedVisitPoleSet H T := ⟨hp.1.trans_le hBT, hp.2⟩
    change (if h : p ∈ enlargedVisitPoleSet H b then
      finiteUnionGreen hH hLE hlam hLam A H b (enlargedVisitPole H b ⟨p, h⟩) else 0) ≤
      (if h : p ∈ enlargedVisitPoleSet H T then
        finiteUnionGreen hH hLE hlam hLam A H T (enlargedVisitPole H T ⟨p, h⟩)
          else 0).restrict {q | q.time < b}
    rw [dite_eq_left hp, dite_eq_left hpT]
    exact (entranceSlab_unionGreen_horizon_restrict
      hH hLE hlam hLam A H b T hBT p hp.1 hp.2).le
  · have hz : enlargedVisitGreenKernel hH hLE hlam hLam A H b p = 0 := by
      change (if h : p ∈ enlargedVisitPoleSet H b then
        finiteUnionGreen hH hLE hlam hLam A H b (enlargedVisitPole H b ⟨p, h⟩)
          else 0) = 0
      exact dite_eq_right hp
    rw [hz]
    exact Measure.zero_le _

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
