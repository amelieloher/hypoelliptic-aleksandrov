module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ActiveTerminalDominationIntegration
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionSupport
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitMassSupport

/-! # Actual finite terminal visits telescope against a homogeneous stopped potential -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory Parabolic
open SectionTwo TheoremA Evolution
open scoped Classical

/-- A supplied homogeneous potential bounds the actual finite enlarged terminal sum. -/
theorem enlarged_terminal_stopped_potential_le
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T b : ℝ)
    (P : Point) (hs : s ≤ P.time) (hT : P.time < T) (hBT : b ≤ T)
    (hJ : closure c.active ⊆ J.carrier) (u : Point → ℝ)
    (hphi : IsKineticC112On u {p | p.time < b})
    (hc : ContinuousOn u {p | p.time ≤ b}) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ p, p.time ≤ b → |u p| ≤ M)
    (hop : ∀ p, p.time < b → forwardScalarOperator A.a u p = 0)
    (hn : ∀ p, p.time ≤ b → 0 ≤ u p) (N : ℕ) :
    (∫ q, enlargedStoppedPotential b u q
      ∂enlargedActiveTerminal hH hLE hlam hLam A c J s T P N b) ≤
        enlargedStoppedPotential b u P := by
  let V := enlargedStoppedPotential b u
  let D : Set Point := {q | q.time < b}
  have hD : MeasurableSet D := (isOpen_lt continuous_time continuous_const).measurableSet
  let Sin := visitBoundary s T (visitEntranceInterval c) J
  let Sout := visitBoundary s T (visitActiveInterval c) J
  have hi : MeasurableSet Sin := measurableSet_visitBoundary s T _ J
  have ho : MeasurableSet Sout := measurableSet_visitBoundary s T _ J
  let EA := enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) T
  let EW := enlargedVisitExitKernel hH hLE hlam hLam A (visitWaitingUnion c J) T
  let KA := EA.restrict (ho.inter hD)
  let KW := EW.restrict hi
  let KT := enlargedTerminalFamilyKernel hH hLE hlam hLam A c J b
  let gamma := enlargedVisitEntrance hH hLE hlam hLam A c J s T P
  let beta := enlargedVisitOutgoing hH hLE hlam hLam A c J s T P
  let U := fun n => ∫ p, V p ∂gamma n
  let R := fun n => ∫ p, V p ∂(beta n).restrict D
  let W := fun n => ∫ p, V p ∂KT ∘ₘ gamma n
  have hint (mu : Measure Point) [IsFiniteMeasure mu] : Integrable V mu :=
    enlargedStoppedPotential_integrable b u hc M hM hbound mu
  have hnV (p : Point) : 0 ≤ V p := by
    dsimp [V, enlargedStoppedPotential]
    split
    · exact hn p ‹p.time ≤ b›
    · exact le_rfl
  have hka (n : ℕ) : KA ∘ₘ gamma n = (beta n).restrict D := by
    change (gamma n).bind (fun p => (EA p).restrict (Sout ∩ D)) = _
    rw [← nested_bind_restrict (gamma n) EA EA.measurable _ (ho.inter hD)]
    change (EA ∘ₘ gamma n).restrict (Sout ∩ D) =
      ((EA ∘ₘ gamma n).restrict Sout).restrict D
    rw [Measure.restrict_restrict hD, inter_comm]
  have hkw (n : ℕ) : KW ∘ₘ beta n = gamma (n + 1) := by
    change (beta n).bind (fun p => (EW p).restrict Sin) = _
    rw [← nested_bind_restrict (beta n) EW EW.measurable Sin hi]
    rfl
  have ha (n : ℕ) : W n + R n ≤ U n := by
    have hp : ∀ᵐ p ∂gamma n, p.velocity 0 ∈ c.active :=
      (enlargedVisitEntrance_ae_support hH hLE hlam hLam A c J s T P hs hT n).mono
        fun _ hp => enlarged_closedEntrance_subset_active c hp.2.2
    have hh := enlarged_integral_kernel_pair_le KT KA (gamma n) V V
      (hint _) (hint _) (hint _) (hp.mono fun p hp =>
        enlarged_active_stopped_step hH hLE hlam hLam A c J b T hBT hJ u hphi hc M hM
          hbound hop hn p hp (Sout ∩ D) (ho.inter hD) inter_subset_right)
    rw [hka n] at hh
    exact hh
  have hw (n : ℕ) : U (n + 1) ≤ R n := by
    have hh := enlarged_integral_kernel_le KW (beta n) V (D.indicator V)
      (hint _) ((hint _).indicator hD) (Filter.Eventually.of_forall fun p =>
        enlarged_waiting_stopped_step hH hLE hlam hLam A (visitWaitingUnion c J) b T hBT
          u hphi hc M hM hbound hop hn p Sin hi)
    rw [hkw n, integral_indicator hD] at hh
    exact hh
  have hinit : U 0 ≤ V P := by
    change (∫ p, V p ∂visitInitial P (visitEntranceInterval c) Sin EW) ≤ V P
    unfold visitInitial
    split
    · rw [integral_dirac]
    · have hh := enlarged_waiting_stopped_step hH hLE hlam hLam A (visitWaitingUnion c J)
        b T hBT u hphi hc M hM hbound hop hn P Sin hi
      apply hh.trans
      by_cases hp : P ∈ D
      · rw [Set.indicator_of_mem hp]
      · rw [Set.indicator_of_notMem hp]
        exact hnV P
  have hsum := (enlarged_terminal_values_telescope U R W
    (fun n => integral_nonneg hnV) ha hw N).trans hinit
  change (∫ p, V p ∂∑ n ∈ Finset.range N, KT ∘ₘ gamma n) ≤ V P
  rw [integral_finsetSum_measure (fun n _ => hint (KT ∘ₘ gamma n))]
  exact hsum

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
