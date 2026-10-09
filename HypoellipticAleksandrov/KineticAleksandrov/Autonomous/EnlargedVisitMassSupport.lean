module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitsPieces
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassEntranceIntegrals
import Mathlib.Tactic

/-! # Support of the canonical enlarged-strip visit count

The initial atom is retained at the starting time; every subsequent entrance
is restricted to the literal internal face in the open observation slab.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory ProbabilityTheory HypoellipticAleksandrov

/-- The closed entrance interval lies strictly inside the active interval. -/
theorem enlarged_closedEntrance_subset_active (c : Clock) :
    closure c.entrance ⊆ c.active := by
  intro v hv
  rw [Clock.entrance, closure_Ioo (by linarith [c.positive])] at hv
  change c.vbar - 3 * c.r / 4 < v ∧ v < c.vbar + 3 * c.r / 4
  constructor <;> linarith [hv.1, hv.2, c.positive]

/-- Every canonical entrance lies between the initial time and the horizon. -/
theorem enlargedVisitEntrance_ae_support
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ)
    (P : Point) (hs : s ≤ P.time) (hT : P.time < T) (n : ℕ) :
    ∀ᵐ p ∂enlargedVisitEntrance hH hLE hlam hLam A c J s T P n,
      s ≤ p.time ∧ p.time < T ∧ p.velocity 0 ∈ closure c.entrance := by
  cases n with
  | zero =>
    unfold enlargedVisitEntrance visitGamma visitInitial
    split
    · rename_i hv
      apply (ae_dirac_iff ?_).mpr
      · exact ⟨hs, hT, hv⟩
      · exact (isClosed_le continuous_const continuous_time).measurableSet.inter
          ((isOpen_lt continuous_time continuous_const).measurableSet.inter
            (isClosed_closure.measurableSet.preimage
              ((continuous_apply 0).comp continuous_velocity).measurable))
    · exact (ae_restrict_mem
        (measurableSet_visitBoundary s T (visitEntranceInterval c) J)).mono
          (fun _ hp => ⟨hp.1.le, hp.2.1, frontier_subset_closure hp.2.2.1⟩)
  | succ n =>
    exact (ae_restrict_mem
      (measurableSet_visitBoundary s T (visitEntranceInterval c) J)).mono
        (fun _ hp => ⟨hp.1.le, hp.2.1, frontier_subset_closure hp.2.2.1⟩)

/-- The canonical counting measure has the same time and entrance support as its pieces. -/
theorem enlargedVisitStarts_ae_support
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ)
    (P : Point) (hs : s ≤ P.time) (hT : P.time < T) :
    ∀ᵐ p ∂enlargedVisitStarts hH hLE hlam hLam A c J s T P,
      s ≤ p.time ∧ p.time < T ∧ p.velocity 0 ∈ closure c.entrance :=
  Measure.ae_sum_iff.mpr fun n =>
    enlargedVisitEntrance_ae_support hH hLE hlam hLam A c J s T P hs hT n

/-- The enlarged active-pole carrier includes almost every actual entrance. -/
theorem enlargedVisitEntrance_ae_activePole
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ)
    (P : Point) (hs : s ≤ P.time) (hT : P.time < T)
    (hJ : closure c.active ⊆ J.carrier) (n : ℕ) :
    ∀ᵐ p ∂enlargedVisitEntrance hH hLE hlam hLam A c J s T P n,
      p ∈ enlargedVisitPoleSet (visitActiveUnion c J) T := by
  apply (enlargedVisitEntrance_ae_support hH hLE hlam hLam A c J s T P hs hT n).mono
  intro p hp
  refine ⟨hp.2.1, ?_⟩
  rw [visitActiveUnion_carrier]
  have hv := enlarged_closedEntrance_subset_active c hp.2.2
  exact ⟨hv, hJ (subset_closure hv)⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
