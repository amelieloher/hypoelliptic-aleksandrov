module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionStartCumulative

/-! # The literal position-start Green identity on a half-open observation slab -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- Subtracting the cumulative identities gives the exact source slab identity for one pole. -/
theorem positionStartQuadratic_slab_identity
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (Y a b : ℝ)
    (hc : |c.vbar| = 2 * c.r) (hJ : closure c.active ⊆ J.carrier)
    (p : Point) (hv : p.velocity 0 ∈ c.active) (hab : a ≤ b) :
    let f := fun q : Point => positionStartCutoff Y c.r c.positive (q.position 0) *
      visitQuadratic c (q.velocity 0)
    ({q : Point | a < q.time ∧ q.time ≤ b}.indicator f) p =
      (∫ q, f q ∂enlargedActiveTerminalFamily hH hLE hlam hLam A c J b p) -
      (∫ q, f q ∂enlargedActiveTerminalFamily hH hLE hlam hLam A c J a p) -
      ∫ q in {q : Point | a < q.time ∧ q.time ≤ b}, forwardScalarOperator A.a f q
        ∂stripGreen hH hLE hlam hLam A c.activeInterval ⊤ (densityClockPole c p hv) := by
  dsimp only
  let f := fun q : Point => positionStartCutoff Y c.r c.positive (q.position 0) *
    visitQuadratic c (q.velocity 0)
  let G := stripGreen hH hLE hlam hLam A c.activeInterval ⊤ (densityClockPole c p hv)
  have hg : Integrable (fun q => forwardScalarOperator A.a f q) G :=
    positionStartQuadratic_operator_integrable hlam hLam A c Y hc G
      ((stripGreen_infinite_ae_future_carrier hH hLE hlam hLam A c.activeInterval
        (densityClockPole c p hv)).mono fun _ hq => hq.2)
  have hid := positionStartQuadratic_cumulative_identity
    hH hLE hlam hLam A c J Y b hc hJ p hv
  have hia := positionStartQuadratic_cumulative_identity
    hH hLE hlam hLam A c J Y a hc hJ p hv
  change ({q : Point | q.time ≤ b}.indicator f) p = _ at hid
  change ({q : Point | q.time ≤ a}.indicator f) p = _ at hia
  have hd : {q : Point | a < q.time ∧ q.time ≤ b} =
      {q : Point | q.time ≤ b} \ {q : Point | q.time ≤ a} := by
    ext q
    simp only [mem_ofPred_eq, mem_sdiff, not_le]
    exact and_comm
  have hi : (∫ q in {q : Point | a < q.time ∧ q.time ≤ b},
      forwardScalarOperator A.a f q ∂G) =
      (∫ q in {q : Point | q.time ≤ b}, forwardScalarOperator A.a f q ∂G) -
      ∫ q in {q : Point | q.time ≤ a}, forwardScalarOperator A.a f q ∂G := by
    rw [hd]
    exact setIntegral_sdiff₀
      (isClosed_le continuous_time continuous_const).measurableSet.nullMeasurableSet
      hg.integrableOn (fun _ hq => hq.trans hab)
  rw [hi]
  have he : ({q : Point | a < q.time ∧ q.time ≤ b}.indicator f) p =
      ({q : Point | q.time ≤ b}.indicator f) p -
      ({q : Point | q.time ≤ a}.indicator f) p := by
    by_cases hpa : p.time ≤ a
    · rw [indicator_of_notMem (show p ∉ {q : Point | a < q.time ∧ q.time ≤ b} from
        fun h => (not_lt_of_ge hpa) h.1),
        indicator_of_mem (show p ∈ {q : Point | q.time ≤ b} from hpa.trans hab),
        indicator_of_mem (show p ∈ {q : Point | q.time ≤ a} from hpa), sub_self]
    · rw [indicator_of_notMem (show p ∉ {q : Point | q.time ≤ a} from hpa), sub_zero]
      by_cases hpb : p.time ≤ b
      · rw [indicator_of_mem (show p ∈ {q : Point | a < q.time ∧ q.time ≤ b} from
          ⟨lt_of_not_ge hpa, hpb⟩),
          indicator_of_mem (show p ∈ {q : Point | q.time ≤ b} from hpb)]
      · rw [indicator_of_notMem (show p ∉ {q : Point | a < q.time ∧ q.time ≤ b} from
          fun h => hpb h.2),
          indicator_of_notMem (show p ∉ {q : Point | q.time ≤ b} from hpb)]
  rw [he, hid, hia]
  ring

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
