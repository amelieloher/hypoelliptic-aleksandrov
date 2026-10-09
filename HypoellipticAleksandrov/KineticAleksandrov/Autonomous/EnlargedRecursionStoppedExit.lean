module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionPotential
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionFuture

/-! # Stopped homogeneous actions of the actual finite-union exit kernels -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Parabolic
open SectionTwo TheoremA Evolution
open scoped Classical

/-- A stopped potential vanishes on every strictly later exit from a pole at or after `b`. -/
theorem enlarged_exit_stopped_integral_zero
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion) (T b : ℝ)
    (u : Point → ℝ) (p : Point) (hp : b ≤ p.time) :
    (∫ q, enlargedStoppedPotential b u q
      ∂enlargedVisitExitKernel hH hLE hlam hLam A H T p) = 0 := by
  apply integral_eq_zero_of_ae
  exact (enlargedVisitExitKernel_ae_time_gt hH hLE hlam hLam A H T p).mono
    fun q hq => ite_eq_right (not_le_of_gt (hp.trans_lt hq))

/-- The true enlarged exit kernel is sub-Markov for a stopped homogeneous potential. -/
theorem enlarged_exit_stopped_integral_le
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion) (b T : ℝ) (hBT : b ≤ T)
    (u : Point → ℝ) (hphi : IsKineticC112On u {p | p.time < b})
    (hc : ContinuousOn u {p | p.time ≤ b}) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ p, p.time ≤ b → |u p| ≤ M)
    (hop : ∀ p, p.time < b → forwardScalarOperator A.a u p = 0)
    (hn : ∀ p, p.time ≤ b → 0 ≤ u p) (p : Point) :
    (∫ q, enlargedStoppedPotential b u q
      ∂enlargedVisitExitKernel hH hLE hlam hLam A H T p) ≤
        enlargedStoppedPotential b u p := by
  by_cases hp : p ∈ enlargedVisitPoleSet H T
  · by_cases hb : p.time < b
    · let e := enlargedVisitPole H T ⟨p, hp⟩
      let I := H.component (finiteUnionPoleIndex H T e)
      let ep : StripPole I ⊤ := ⟨p, WithTop.coe_lt_top _,
        (finiteUnionComponentPole H T e).2.2⟩
      have hi := enlarged_stripExit_stopped_potential_le hH hLE hlam hLam A I ep b T
        hb hBT u hphi hc M hM hbound hop hn
      change (∫ q, enlargedStoppedPotential b u q ∂
        (if ht : p ∈ enlargedVisitPoleSet H T then _ else 0)) ≤ _
      rw [dite_eq_left hp]
      change (∫ q, enlargedStoppedPotential b u q ∂stripExit hH hLE hlam hLam A I T _) ≤ _
      rw [show enlargedStoppedPotential b u p = u p from ite_eq_left hb.le]
      exact hi
    · rw [enlarged_exit_stopped_integral_zero hH hLE hlam hLam A H T b u p (le_of_not_gt hb)]
      unfold enlargedStoppedPotential
      split
      · exact hn p ‹p.time ≤ b›
      · exact le_rfl
  · change (∫ q, enlargedStoppedPotential b u q ∂
      (if ht : p ∈ enlargedVisitPoleSet H T then _ else 0)) ≤ _
    rw [dite_eq_right hp, integral_zero_measure]
    unfold enlargedStoppedPotential
    split
    · exact hn p ‹p.time ≤ b›
    · exact le_rfl

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
