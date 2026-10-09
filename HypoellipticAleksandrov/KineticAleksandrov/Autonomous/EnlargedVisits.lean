module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalSetting
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PushforwardStatement

/-! # Canonical visits in an enlarged bounded velocity strip

Source: companion paper, Lemma 8.6 and its proof. Unlike the cylinder-specific count,
the outer interval is an independent argument. Initial poles at time zero
are retained, as required by the initial atom of the entrance count.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory ProbabilityTheory HypoellipticAleksandrov
open scoped Classical

/-- Valid physical poles before a finite horizon, including the initial time. -/
def enlargedVisitPoleSet (H : FiniteIntervalUnion) (T : ℝ) : Set Point :=
  {p | p.time < T ∧ p.velocity 0 ∈ H.carrier}

/-- The enlarged visit pole carrier is measurable. -/
theorem measurableSet_enlargedVisitPoleSet (H : FiniteIntervalUnion) (T : ℝ) :
    MeasurableSet (enlargedVisitPoleSet H T) :=
  (isOpen_lt continuous_time continuous_const).measurableSet.inter
    (H.isOpen_carrier.measurableSet.preimage
      ((continuous_apply 0).comp continuous_velocity).measurable)

/-- Physical poles enter the canonical finite-union pole carrier. -/
def enlargedVisitPole (H : FiniteIntervalUnion) (T : ℝ)
    (p : enlargedVisitPoleSet H T) : FiniteUnionPole H (T : WithTop ℝ) :=
  ⟨p.1, WithTop.coe_lt_coe.mpr p.2.1, p.2.2⟩

/-- The physical pole inclusion is measurable. -/
theorem measurable_enlargedVisitPole (H : FiniteIntervalUnion) (T : ℝ) :
    Measurable (enlargedVisitPole H T) := measurable_subtype_coe.subtype_mk

/-- Canonical exit kernel extended by zero only outside its valid pole carrier. -/
def enlargedVisitExitKernel
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion) (T : ℝ) :
    Kernel Point Point :=
  visitExtendKernel (enlargedVisitPoleSet H T) (measurableSet_enlargedVisitPoleSet H T)
    (fun p => finiteUnionExit hH hLE hlam hLam A H T (enlargedVisitPole H T p))
    ((finiteUnionExit_measurable hH hLE hlam hLam A H T).comp
      (measurable_enlargedVisitPole H T))

/-- Every enlarged exit kernel has mass at most one. -/
instance enlargedVisitExitKernel_isFiniteKernel
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion) (T : ℝ) :
    IsFiniteKernel (enlargedVisitExitKernel hH hLE hlam hLam A H T) := by
  refine ⟨1, by simp only [ENNReal.one_lt_top], ?_⟩
  intro p
  change (if hp : p ∈ enlargedVisitPoleSet H T then
    finiteUnionExit hH hLE hlam hLam A H T (enlargedVisitPole H T ⟨p, hp⟩)
    else 0) univ ≤ 1
  split
  · simp only [measure_univ, le_refl]
  · exact zero_le

/-- Entrance number `n+1` in the literal enlarged-strip alternating recursion. -/
def enlargedVisitEntrance
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ)
    (P : Point) (n : ℕ) : Measure Point :=
  visitGamma P (visitEntranceInterval c)
    (visitBoundary s T (visitEntranceInterval c) J)
    (visitBoundary s T (visitActiveInterval c) J)
    (enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) T)
    (enlargedVisitExitKernel hH hLE hlam hLam A (visitWaitingUnion c J) T) n

/-- The enlarged-strip counting measure, including the initial atom exactly once. -/
def enlargedVisitStarts
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ)
    (P : Point) : Measure Point :=
  Measure.sum (enlargedVisitEntrance hH hLE hlam hLam A c J s T P)

/-- Each individual entrance is finite; finiteness of the full sum is a separate estimate. -/
instance enlargedVisitEntrance_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ)
    (P : Point) (n : ℕ) :
    IsFiniteMeasure (enlargedVisitEntrance hH hLE hlam hLam A c J s T P n) := by
  unfold enlargedVisitEntrance
  infer_instance

/-- A canonical all-time Green kernel on the active interval. -/
def enlargedActiveGreenKernel
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) : Kernel Point Point :=
  visitExtendKernel {p | p.velocity 0 ∈ c.active}
    (isOpen_Ioo.measurableSet.preimage
      ((continuous_apply 0).comp continuous_velocity).measurable)
    (fun p => stripGreen hH hLE hlam hLam A c.activeInterval ⊤
      (densityClockPole c p.1 p.2))
    ((Measure.measurable_measure.mpr
      (stripGreen_measurable_apply hH hLE hlam hLam A c.activeInterval ⊤)).comp
      (show Measurable (fun p : {p : Point | p.velocity 0 ∈ c.active} =>
        densityClockPole c p.1 p.2) from measurable_subtype_coe.subtype_mk))

/-- Integrate the actual all-time active Green family against physical starting points. -/
def enlargedActiveGreen
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (nu : Measure Point) : Measure Point :=
  enlargedActiveGreenKernel hH hLE hlam hLam A c ∘ₘ nu

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
