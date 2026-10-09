module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ActiveTerminalDominationKernel
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionStoppedExit

/-! # One actual active piece spends its stopped potential only once -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Parabolic
open SectionTwo TheoremA Evolution
open scoped Classical

/-- Earlier active poles split their potential between the terminal cap and earlier exits. -/
theorem enlarged_active_stopped_step_earlier
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b T : ℝ) (hBT : b ≤ T)
    (hJ : closure c.active ⊆ J.carrier) (u : Point → ℝ)
    (hphi : IsKineticC112On u {p | p.time < b})
    (hc : ContinuousOn u {p | p.time ≤ b}) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ p, p.time ≤ b → |u p| ≤ M)
    (hop : ∀ p, p.time < b → forwardScalarOperator A.a u p = 0)
    (hn : ∀ p, p.time ≤ b → 0 ≤ u p)
    (p : Point) (hv : p.velocity 0 ∈ c.active) (hb : p.time < b)
    (B : Set Point) (hB : MeasurableSet B) (hsub : B ⊆ {q | q.time < b}) :
    (∫ q, enlargedStoppedPotential b u q
      ∂enlargedActiveTerminalFamily hH hLE hlam hLam A c J b p) +
    (∫ q, enlargedStoppedPotential b u q
      ∂(enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) T p).restrict B) ≤
        u p := by
  let V := enlargedStoppedPotential b u
  let ep := densityClockPole c p hv
  let E := stripExit hH hLE hlam hLam A c.activeInterval b
    (stripPoleFinite c.activeInterval ep b hb)
  have he : enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) b p = E := by
    rw [enlarged_activeUnion_eq c J hJ]
    have hp' : p ∈ enlargedVisitPoleSet c.activeInterval.toFiniteUnion b :=
      ⟨hb, by rw [Interval.toFiniteUnion_carrier]; exact ep.2.2⟩
    change (if ht : p ∈ enlargedVisitPoleSet c.activeInterval.toFiniteUnion b then
      finiteUnionExit hH hLE hlam hLam A _ b (enlargedVisitPole _ _ ⟨p, ht⟩) else 0) = E
    rw [dite_eq_left hp']
    rfl
  have hs : ∀ᵐ q ∂E, q.time ≤ b :=
    (stripExitOfRealization_ae_closed_future hH hlam hLam A c.activeInterval
      (stripEvolution hH hLE hlam hLam A c.activeInterval)
      (stripEvolution_spec hH hLE hlam hLam A c.activeInterval) b
      (stripPoleFinite c.activeInterval ep b hb)).mono fun _ hq => hq.2.1
  have hiE := enlargedStoppedPotential_integrable b u hc M hM hbound E
  have hnn : 0 ≤ᵐ[E] V := hs.mono fun q hq => by
    change 0 ≤ (if q.time ≤ b then u q else 0)
    rw [ite_eq_left hq]
    exact hn q hq
  have hd := enlarged_terminal_and_early_exit_le hH hLE hlam hLam A c J b T hJ p hv hb
    hBT B hB hsub
  rw [he] at hd
  have hm := integral_mono_measure hd hnn hiE
  have hi1 := enlargedStoppedPotential_integrable b u hc M hM hbound
    (enlargedActiveTerminalFamily hH hLE hlam hLam A c J b p)
  have hi2 := enlargedStoppedPotential_integrable b u hc M hM hbound
    ((enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) T p).restrict B)
  rw [integral_add_measure hi1 hi2] at hm
  have heq : V =ᵐ[E] u := hs.mono fun _ hq => ite_eq_left hq
  rw [integral_congr_ae heq, enlarged_stripExit_potential_identity hH hLE hlam hLam A
    c.activeInterval ep b hb u hphi hc M hM hbound hop] at hm
  exact hm

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
