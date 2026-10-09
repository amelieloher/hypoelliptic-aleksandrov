module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionHorizonSplit
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitMassTerminal
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionFuture

/-! # The actual terminal family and its disjoint earlier exits -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory
open scoped Classical

/-- Every actual terminal family has mass at most one, including zero-duration poles. -/
theorem enlarged_terminal_family_mass_le_one
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b : ℝ) (p : Point) :
    enlargedActiveTerminalFamily hH hLE hlam hLam A c J b p univ ≤ 1 := by
  unfold enlargedActiveTerminalFamily
  split
  · simp only [Measure.dirac_apply_of_mem (mem_univ p), le_refl]
  · apply (Measure.restrict_le_self univ).trans
    change (if hp : p ∈ enlargedVisitPoleSet (visitActiveUnion c J) b then
      finiteUnionExit hH hLE hlam hLam A (visitActiveUnion c J) b
        (enlargedVisitPole _ _ ⟨p, hp⟩) else 0) univ ≤ 1
    split
    · simp only [measure_univ, le_refl]
    · exact zero_le

/-- Every actual terminal fiber is finite. -/
instance enlarged_terminal_family_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b : ℝ) (p : Point) :
    IsFiniteMeasure (enlargedActiveTerminalFamily hH hLE hlam hLam A c J b p) :=
  ⟨(enlarged_terminal_family_mass_le_one hH hLE hlam hLam A c J b p).trans_lt
    ENNReal.one_lt_top⟩

/-- At a valid earlier active pole, terminal and earlier restart exits are disjoint submeasures. -/
theorem enlarged_terminal_and_early_exit_le
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b T : ℝ)
    (hJ : closure c.active ⊆ J.carrier) (p : Point) (hv : p.velocity 0 ∈ c.active)
    (hb : p.time < b) (hBT : b ≤ T)
    (B : Set Point) (hB : MeasurableSet B) (hsub : B ⊆ {q | q.time < b}) :
    enlargedActiveTerminalFamily hH hLE hlam hLam A c J b p +
      (enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) T p).restrict B ≤
        enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) b p := by
  let H := c.activeInterval.toFiniteUnion
  have hp : p ∈ enlargedVisitPoleSet H b :=
    ⟨hb, by
      rw [show H.carrier = c.activeInterval.carrier from Interval.toFiniteUnion_carrier _]
      exact (densityClockPole c p hv).2.2⟩
  have hpT : p ∈ enlargedVisitPoleSet H T := ⟨hb.trans_le hBT, hp.2⟩
  let ep : StripPole c.activeInterval ⊤ := ⟨p, WithTop.coe_lt_top _, (densityClockPole c p hv).2.2⟩
  unfold enlargedActiveTerminalFamily
  rw [enlarged_activeUnion_eq c J hJ]
  rw [ite_eq_right (fun h => (ne_of_lt hb) h.1)]
  change (if h : p ∈ enlargedVisitPoleSet H b then
    finiteUnionExit hH hLE hlam hLam A H b (enlargedVisitPole H b ⟨p, h⟩)
      else 0).restrict {q | q.time = b} +
    (if h : p ∈ enlargedVisitPoleSet H T then
      finiteUnionExit hH hLE hlam hLam A H T (enlargedVisitPole H T ⟨p, h⟩)
        else 0).restrict B ≤
      (if h : p ∈ enlargedVisitPoleSet H b then
        finiteUnionExit hH hLE hlam hLam A H b (enlargedVisitPole H b ⟨p, h⟩) else 0)
  rw [dite_eq_left hp, dite_eq_left hpT]
  exact enlarged_stripExit_cap_and_early_le hH hLE hlam hLam A c.activeInterval ep b T
    hb hBT B hB hsub

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
