module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ActiveTerminalDominationStep

/-! # Stopped potential inequalities including observation-time entrance atoms -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Parabolic
open SectionTwo TheoremA Evolution
open scoped Classical

/-- An active piece spends its potential on its terminal value and strictly earlier exits. -/
theorem enlarged_active_stopped_step
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b T : ℝ) (hBT : b ≤ T)
    (hJ : closure c.active ⊆ J.carrier) (u : Point → ℝ)
    (hphi : IsKineticC112On u {p | p.time < b})
    (hc : ContinuousOn u {p | p.time ≤ b}) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ p, p.time ≤ b → |u p| ≤ M)
    (hop : ∀ p, p.time < b → forwardScalarOperator A.a u p = 0)
    (hn : ∀ p, p.time ≤ b → 0 ≤ u p)
    (p : Point) (hv : p.velocity 0 ∈ c.active)
    (B : Set Point) (hB : MeasurableSet B) (hsub : B ⊆ {q | q.time < b}) :
    (∫ q, enlargedStoppedPotential b u q
      ∂enlargedActiveTerminalFamily hH hLE hlam hLam A c J b p) +
    (∫ q, enlargedStoppedPotential b u q
      ∂(enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) T p).restrict B) ≤
        enlargedStoppedPotential b u p := by
  by_cases hb : p.time < b
  · rw [show enlargedStoppedPotential b u p = u p from ite_eq_left hb.le]
    exact enlarged_active_stopped_step_earlier hH hLE hlam hLam A c J b T hBT hJ u hphi
      hc M hM hbound hop hn p hv hb B hB hsub
  · have hz : (∫ q, enlargedStoppedPotential b u q
        ∂(enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) T p).restrict B) =
        0 := by
      apply integral_eq_zero_of_ae
      apply (ae_restrict_of_ae
        (enlargedVisitExitKernel_ae_time_gt hH hLE hlam hLam A (visitActiveUnion c J) T p)).mono
      intro q hq
      exact ite_eq_right (not_le_of_gt ((le_of_not_gt hb).trans_lt hq))
    rw [hz, add_zero]
    by_cases he : p.time = b
    · have hvJ : p.velocity 0 ∈ (visitActiveUnion c J).carrier := by
        rw [visitActiveUnion_carrier]
        exact ⟨hv, hJ (subset_closure hv)⟩
      have hterm : enlargedActiveTerminalFamily hH hLE hlam hLam A c J b p =
          Measure.dirac p := by
        unfold enlargedActiveTerminalFamily
        exact ite_eq_left ⟨he, hvJ⟩
      rw [hterm, integral_dirac]
    · have hp : p ∉ enlargedVisitPoleSet (visitActiveUnion c J) b :=
        fun hp => hb hp.1
      have hterm : enlargedActiveTerminalFamily hH hLE hlam hLam A c J b p = 0 := by
        unfold enlargedActiveTerminalFamily
        rw [ite_eq_right (fun h => he h.1)]
        change (if ht : p ∈ enlargedVisitPoleSet (visitActiveUnion c J) b then
          finiteUnionExit hH hLE hlam hLam A _ b (enlargedVisitPole _ _ ⟨p, ht⟩)
            else 0).restrict {q | q.time = b} = 0
        rw [dite_eq_right hp, Measure.restrict_zero]
      rw [hterm, integral_zero_measure]
      rw [show enlargedStoppedPotential b u p = 0 from
        ite_eq_right (fun h => he (le_antisymm h (le_of_not_gt hb)))]

/-- A waiting piece returns only the potential carried by poles strictly before observation. -/
theorem enlarged_waiting_stopped_step
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion) (b T : ℝ) (hBT : b ≤ T)
    (u : Point → ℝ) (hphi : IsKineticC112On u {p | p.time < b})
    (hc : ContinuousOn u {p | p.time ≤ b}) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ p, p.time ≤ b → |u p| ≤ M)
    (hop : ∀ p, p.time < b → forwardScalarOperator A.a u p = 0)
    (hn : ∀ p, p.time ≤ b → 0 ≤ u p)
    (p : Point) (B : Set Point) (_hB : MeasurableSet B) :
    (∫ q, enlargedStoppedPotential b u q
      ∂(enlargedVisitExitKernel hH hLE hlam hLam A H T p).restrict B) ≤
        {q : Point | q.time < b}.indicator (enlargedStoppedPotential b u) p := by
  by_cases hp : p.time < b
  · rw [show {q : Point | q.time < b}.indicator (enlargedStoppedPotential b u) p =
      enlargedStoppedPotential b u p from
      Set.indicator_of_mem (show p ∈ {q : Point | q.time < b} from hp) _]
    have hi := enlargedStoppedPotential_integrable b u hc M hM hbound
      (enlargedVisitExitKernel hH hLE hlam hLam A H T p)
    have hnV : 0 ≤ᵐ[enlargedVisitExitKernel hH hLE hlam hLam A H T p]
        enlargedStoppedPotential b u := Filter.Eventually.of_forall fun q => by
      unfold enlargedStoppedPotential
      split
      · exact hn q ‹q.time ≤ b›
      · exact le_rfl
    exact (integral_mono_measure Measure.restrict_le_self hnV hi).trans
      (enlarged_exit_stopped_integral_le hH hLE hlam hLam A H b T hBT u hphi hc M hM
        hbound hop hn p)
  · rw [show {q : Point | q.time < b}.indicator (enlargedStoppedPotential b u) p =
      0 from Set.indicator_of_notMem (show p ∉ {q : Point | q.time < b} from hp) _]
    apply le_of_eq
    apply integral_eq_zero_of_ae
    exact (ae_restrict_of_ae
      (enlargedVisitExitKernel_ae_time_gt hH hLE hlam hLam A H T p)).mono
        fun q hq => ite_eq_right (not_le_of_gt ((le_of_not_gt hp).trans_lt hq))

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
