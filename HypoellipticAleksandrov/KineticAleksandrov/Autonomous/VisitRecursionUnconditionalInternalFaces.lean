module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalFaces
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FiniteUnionDomainsNesting
import Mathlib.Topology.Constructions
import Mathlib.Tactic

/-! # The nested-strip internal exits are exactly the alternating visit faces -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- Clipping the active interval by the outer interval leaves the same internal exit face. -/
theorem visitActive_internalExit (c : Clock) (J : Interval) (s T : ℝ) :
    finiteUnionInternalExit (visitActiveUnion c J) J.toFiniteUnion s T =
      visitBoundary s T (visitActiveInterval c) J := by
  unfold finiteUnionInternalExit visitBoundary
  rw [visitActiveUnion_carrier, Interval.toFiniteUnion_carrier,
    frontier_inter_open_inter (show IsOpen J.carrier from isOpen_Ioo)]
  rfl

/-- The closed entrance interval has exactly the frontier of its open interior. -/
theorem visitClosedEntrance_frontier (c : Clock) :
    frontier (closure c.entrance) = frontier c.entrance := by
  have ho : c.vbar - c.r / 2 < c.vbar + c.r / 2 := by linarith [c.positive]
  rw [Clock.entrance, closure_Ioo ho.ne, frontier_Icc ho.le, frontier_Ioo ho]

/-- The possibly disconnected waiting union has precisely the incoming internal face. -/
theorem visitWaiting_internalExit (c : Clock) (J : Interval) (s T : ℝ) :
    finiteUnionInternalExit (visitWaitingUnion c J) J.toFiniteUnion s T =
      visitBoundary s T (visitEntranceInterval c) J := by
  unfold finiteUnionInternalExit visitBoundary
  rw [visitWaitingUnion_carrier, Interval.toFiniteUnion_carrier]
  have he : J.carrier \ closure c.entrance = (closure c.entrance)ᶜ ∩ J.carrier := by
    ext v
    simp only [mem_sdiff, mem_inter_iff, mem_compl_iff]
    exact and_comm
  rw [he, frontier_inter_open_inter (show IsOpen J.carrier from isOpen_Ioo), frontier_compl,
    visitClosedEntrance_frontier]
  rfl

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
