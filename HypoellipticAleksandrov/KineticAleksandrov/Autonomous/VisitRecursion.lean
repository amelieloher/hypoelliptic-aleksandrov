module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.Setting
public import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Tactic

/-! # Literal alternating entrance and exit recursion

Index zero represents the source's first entrance measure. The measure sum includes
this initial visit once. The kernels are the Borel exit families consumed from AU-06;
this module makes no assertion that a finite-union exit family has been constructed.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory ProbabilityTheory
open scoped Classical

/-- The active velocity domain, intersected with the outer strip. -/
def visitActiveDomain (Istar J : Interval) : Set ℝ := Istar.carrier ∩ J.carrier

/-- The waiting domain can have two components or be empty. -/
def visitWaitingDomain (I J : Interval) : Set ℝ := J.carrier \ closure I.carrier

/-- Internal velocity boundary in the literal open physical time slab. -/
def visitBoundary (s T : ℝ) (I J : Interval) : Set Point :=
  {p | s < p.time ∧ p.time < T ∧ p.velocity 0 ∈ frontier I.carrier ∩ J.carrier}

/-- The internal boundary is measurable in physical coordinates. -/
theorem measurableSet_visitBoundary (s T : ℝ) (I J : Interval) :
    MeasurableSet (visitBoundary s T I J) := by
  have ht : MeasurableSet {p : Point | p.time ∈ Ioo s T} :=
    isOpen_Ioo.measurableSet.preimage continuous_time.measurable
  have hv : MeasurableSet {p : Point | p.velocity 0 ∈ frontier I.carrier ∩ J.carrier} :=
    (isClosed_frontier.measurableSet.inter isOpen_Ioo.measurableSet).preimage
      ((continuous_apply 0).comp continuous_velocity).measurable
  convert ht.inter hv using 1
  ext p
  simp only [visitBoundary, mem_inter_iff, mem_ofPred_eq, mem_Ioo, and_assoc]

/-- Initial entrance, including the initial point exactly when it is already in the interval. -/
def visitInitial (P : Point) (I : Interval) (Sin : Set Point)
    (exitWaiting : Kernel Point Point) : Measure Point :=
  if P.velocity 0 ∈ closure I.carrier then Measure.dirac P
  else (exitWaiting P).restrict Sin

/-- Entrance measures, with index zero denoting the source's first visit. -/
def visitGamma (P : Point) (I : Interval) (Sin Sout : Set Point)
    (exitActive exitWaiting : Kernel Point Point) : ℕ → Measure Point
  | 0 => visitInitial P I Sin exitWaiting
  | n + 1 => (exitWaiting ∘ₘ ((exitActive ∘ₘ
      visitGamma P I Sin Sout exitActive exitWaiting n).restrict Sout)).restrict Sin

/-- Exit from the active domain onto the internal outgoing face. -/
def visitBeta (P : Point) (I : Interval) (Sin Sout : Set Point)
    (exitActive exitWaiting : Kernel Point Point) (n : ℕ) : Measure Point :=
  (exitActive ∘ₘ visitGamma P I Sin Sout exitActive exitWaiting n).restrict Sout

/-- Counting all entrances, with the initial entrance included once. -/
def visitStarts (P : Point) (I : Interval) (Sin Sout : Set Point)
    (exitActive exitWaiting : Kernel Point Point) : Measure Point :=
  Measure.sum (visitGamma P I Sin Sout exitActive exitWaiting)

/-- The three defining recursion equations, without a mass-one claim on entrances. -/
theorem visit_recursion (P : Point) (I : Interval) (Sin Sout : Set Point)
    (exitActive exitWaiting : Kernel Point Point) :
    visitGamma P I Sin Sout exitActive exitWaiting 0 =
      (if P.velocity 0 ∈ closure I.carrier then Measure.dirac P
        else (exitWaiting P).restrict Sin) ∧
    (∀ n, visitBeta P I Sin Sout exitActive exitWaiting n =
      (exitActive ∘ₘ visitGamma P I Sin Sout exitActive exitWaiting n).restrict Sout) ∧
    (∀ n, visitGamma P I Sin Sout exitActive exitWaiting (n + 1) =
      (exitWaiting ∘ₘ visitBeta P I Sin Sout exitActive exitWaiting n).restrict Sin) :=
  ⟨rfl, fun _ => rfl, fun _ => rfl⟩

/-- Every entrance is finite when both consumed exit kernels are finite. -/
instance visitGamma_isFiniteMeasure (P : Point) (I : Interval) (Sin Sout : Set Point)
    (exitActive exitWaiting : Kernel Point Point)
    [IsFiniteKernel exitActive] [IsFiniteKernel exitWaiting] (n : ℕ) :
    IsFiniteMeasure (visitGamma P I Sin Sout exitActive exitWaiting n) := by
  induction n with
  | zero =>
    dsimp only [visitGamma, visitInitial]
    split <;> infer_instance
  | succ n ih =>
    dsimp only [visitGamma]
    infer_instance

/-- Every active outgoing measure is finite. -/
instance visitBeta_isFiniteMeasure (P : Point) (I : Interval) (Sin Sout : Set Point)
    (exitActive exitWaiting : Kernel Point Point)
    [IsFiniteKernel exitActive] [IsFiniteKernel exitWaiting] (n : ℕ) :
    IsFiniteMeasure (visitBeta P I Sin Sout exitActive exitWaiting n) := by
  dsimp only [visitBeta]
  infer_instance

/-- A finite partial sum of entrance measures, including the initial visit once. -/
def visitPartialStarts (P : Point) (I : Interval) (Sin Sout : Set Point)
    (exitActive exitWaiting : Kernel Point Point) (N : ℕ) : Measure Point :=
  ∑ n ∈ Finset.range N, visitGamma P I Sin Sout exitActive exitWaiting n

/-- Every finite partial visit sum is finite; total visit mass is a separate later result. -/
instance visitPartialStarts_isFiniteMeasure (P : Point) (I : Interval) (Sin Sout : Set Point)
    (exitActive exitWaiting : Kernel Point Point)
    [IsFiniteKernel exitActive] [IsFiniteKernel exitWaiting] (N : ℕ) :
    IsFiniteMeasure (visitPartialStarts P I Sin Sout exitActive exitWaiting N) := by
  dsimp only [visitPartialStarts]
  infer_instance

/-- Evaluation of the full counting measure is the sum of the entrance masses. -/
theorem visitStarts_apply (P : Point) (I : Interval) (Sin Sout : Set Point)
    (exitActive exitWaiting : Kernel Point Point) (B : Set Point) (hB : MeasurableSet B) :
    visitStarts P I Sin Sout exitActive exitWaiting B =
      ∑' n, visitGamma P I Sin Sout exitActive exitWaiting n B :=
  Measure.sum_apply _ hB

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
