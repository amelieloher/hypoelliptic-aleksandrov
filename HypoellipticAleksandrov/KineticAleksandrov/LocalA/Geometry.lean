module

public import HypoellipticAleksandrov.KineticAleksandrov.Geometry
public import HypoellipticAleksandrov.KineticAleksandrov.MovingKernel
public import HypoellipticAleksandrov.Parabolic.Geometry
public import HypoellipticAleksandrov.Geometry.KineticPointMeasure
public import Mathlib.Analysis.Complex.Exponential

/-! # Local velocity-ball geometry

Points retain physical coordinate order (time, position, velocity). Evolution states
instead use (velocity, position); the conversions below expose that permutation.
All balls and increments use the Euclidean geometry of PDEFoundation.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory Parabolic

/-- The open time strip with velocity constrained to a Euclidean ball. -/
def localStrip {d : ℕ} (a T : ℝ) (v₀ : PDE.Vec d) (R : ℝ) :
    Set (KineticPoint d) :=
  {P | a < P.time ∧ P.time < T ∧ P.velocity ∈ PDE.euclideanBall v₀ R}

/-- The closed time strip with velocity constrained to the closed ball. -/
def localClosedStrip {d : ℕ} (a T : ℝ) (v₀ : PDE.Vec d) (R : ℝ) :
    Set (KineticPoint d) :=
  {P | a ≤ P.time ∧ P.time ≤ T ∧ P.velocity ∈ closure (PDE.euclideanBall v₀ R)}

/-- Terminal and lateral velocity faces, including their common corner. -/
def localTrace {d : ℕ} (a T : ℝ) (v₀ : PDE.Vec d) (R : ℝ) :
    Set (KineticPoint d) :=
  {P | (P.time = T ∧ P.velocity ∈ closure (PDE.euclideanBall v₀ R)) ∨
    (a ≤ P.time ∧ P.time ≤ T ∧ P.velocity ∈ frontier (PDE.euclideanBall v₀ R))}

/-- A physical starting point whose velocity is valid for the ball evolution. -/
abbrev LocalBallStart {d : ℕ} (v₀ : PDE.Vec d) (R : ℝ) :=
  {P : KineticPoint d // P.velocity ∈ PDE.euclideanBall v₀ R}

/-- The physical position slice through a spacetime point. -/
def physicalPositionSlice {d : ℕ} (u : KineticPoint d → ℝ) (P : KineticPoint d) :
    PDE.Vec d → ℝ := fun x => u ⟨P.time, x, P.velocity⟩

/-- The source kinetic increment based at the center velocity. -/
def kineticIncrement {d : ℕ} (P₀ P Q : KineticPoint d) : ℝ :=
  |P.time - Q.time| ^ (1 / 2 : ℝ) + PDE.vecEuclideanNorm (P.velocity - Q.velocity) +
    PDE.vecEuclideanNorm
      (P.position - Q.position - (P.time - Q.time) • P₀.velocity) ^ (1 / 3 : ℝ)

/-- Position displacement in the centered free-transport frame, with absolute exit data. -/
def exitCoordinates {d : ℕ} (P : KineticPoint d) (v₀ : PDE.Vec d)
    (Q : KineticPoint d) : PDE.Vec d × TimeVelocity d :=
  (Q.position - P.position - (Q.time - P.time) • v₀, (Q.time, Q.velocity))

/-- Fourier phase of the centered position coordinate, retaining exit time and velocity. -/
def exitPhase {d : ℕ} (ξ : PDE.Vec d) (Q : PDE.Vec d × TimeVelocity d) : ℂ :=
  Complex.exp (-Complex.I * (PDE.vecDot ξ Q.1 : ℂ))

/-- Parabolic time--velocity distance, with Euclidean velocity norm. -/
def parabolicDistance {d : ℕ} (z z' : TimeVelocity d) : ℝ :=
  |z.1 - z'.1| ^ (1 / 2 : ℝ) + PDE.vecEuclideanNorm (z.2 - z'.2)

/-- Membership in the open strip unfolds without a coordinate change. -/
@[simp] theorem mem_localStrip_iff {d : ℕ} {a T R : ℝ} {v₀ : PDE.Vec d}
    {P : KineticPoint d} :
    P ∈ localStrip a T v₀ R ↔
      a < P.time ∧ P.time < T ∧ P.velocity ∈ PDE.euclideanBall v₀ R := Iff.rfl

/-- Membership in the closed strip unfolds without a coordinate change. -/
@[simp] theorem mem_localClosedStrip_iff {d : ℕ} {a T R : ℝ} {v₀ : PDE.Vec d}
    {P : KineticPoint d} :
    P ∈ localClosedStrip a T v₀ R ↔
      a ≤ P.time ∧ P.time ≤ T ∧ P.velocity ∈ closure (PDE.euclideanBall v₀ R) := Iff.rfl

/-- The open strip is open in the ordinary spacetime topology. -/
theorem isOpen_localStrip {d : ℕ} (a T : ℝ) (v₀ : PDE.Vec d) (R : ℝ) :
    IsOpen (localStrip a T v₀ R) :=
  (isOpen_lt continuous_const continuous_time).inter
    ((isOpen_lt continuous_time continuous_const).inter
      ((PDE.isOpen_euclideanBall v₀ R).preimage continuous_velocity))

/-- The closed strip is closed in the ordinary spacetime topology. -/
theorem isClosed_localClosedStrip {d : ℕ} (a T : ℝ) (v₀ : PDE.Vec d) (R : ℝ) :
    IsClosed (localClosedStrip a T v₀ R) :=
  (isClosed_le continuous_const continuous_time).inter
    ((isClosed_le continuous_time continuous_const).inter
      (isClosed_closure.preimage continuous_velocity))

/-- The terminal/lateral trace is closed, including the terminal velocity corner. -/
theorem isClosed_localTrace {d : ℕ} (a T : ℝ) (v₀ : PDE.Vec d) (R : ℝ) :
    IsClosed (localTrace a T v₀ R) :=
  ((isClosed_eq continuous_time continuous_const).inter
    (isClosed_closure.preimage continuous_velocity)).union
    ((isClosed_le continuous_const continuous_time).inter
      ((isClosed_le continuous_time continuous_const).inter
        (isClosed_frontier.preimage continuous_velocity)))

/-- The source strip is a Borel set. -/
theorem measurableSet_localStrip {d : ℕ} (a T : ℝ) (v₀ : PDE.Vec d) (R : ℝ) :
    MeasurableSet (localStrip a T v₀ R) := (isOpen_localStrip a T v₀ R).measurableSet

/-- The closed strip is a Borel set. -/
theorem measurableSet_localClosedStrip {d : ℕ} (a T : ℝ) (v₀ : PDE.Vec d) (R : ℝ) :
    MeasurableSet (localClosedStrip a T v₀ R) :=
  (isClosed_localClosedStrip a T v₀ R).measurableSet

/-- The exit trace is a Borel set. -/
theorem measurableSet_localTrace {d : ℕ} (a T : ℝ) (v₀ : PDE.Vec d) (R : ℝ) :
    MeasurableSet (localTrace a T v₀ R) := (isClosed_localTrace a T v₀ R).measurableSet

/-- Every open-strip point belongs to the closed strip. -/
theorem localStrip_subset_closed {d : ℕ} (a T : ℝ) (v₀ : PDE.Vec d) (R : ℝ) :
    localStrip a T v₀ R ⊆ localClosedStrip a T v₀ R := by
  intro P hP
  exact ⟨hP.1.le, hP.2.1.le, subset_closure hP.2.2⟩

/-- With ordered endpoints, both exit faces belong to the closed strip. -/
theorem localTrace_subset_closed {d : ℕ} {a T : ℝ} (haT : a ≤ T)
    (v₀ : PDE.Vec d) (R : ℝ) :
    localTrace a T v₀ R ⊆ localClosedStrip a T v₀ R := by
  intro P hP
  rcases hP with hP | hP
  · exact ⟨hP.1.symm ▸ haT, hP.1.le, hP.2⟩
  · exact ⟨hP.1, hP.2.1, frontier_subset_closure hP.2.2⟩

/-- A stationary moving domain is the original velocity ball. -/
@[simp] theorem movingDomain_ball_zero {d : ℕ} (v₀ : PDE.Vec d) (R t : ℝ) :
    movingDomain (PDE.euclideanBall v₀ R) (fun _ => 0) t = PDE.euclideanBall v₀ R :=
  PDE.translateSet_zero _

/-- Physical starting coordinates give a valid evolution state. -/
theorem ball_start_state_mem {d : ℕ} {v₀ : PDE.Vec d} {R : ℝ}
    (P : LocalBallStart v₀ R) :
    (P.1.velocity, P.1.position) ∈
      evolutionStateSet (PDE.euclideanBall v₀ R) (fun _ => 0) P.1.time := by
  exact ⟨(movingDomain_ball_zero v₀ R P.1.time).symm ▸ P.2, mem_univ _⟩

/-- A valid evolution state's first coordinate is its physical velocity. -/
theorem ball_state_velocity_mem {d : ℕ} {v₀ : PDE.Vec d} {R : ℝ} (t : ℝ)
    (w : EvolutionState (PDE.euclideanBall v₀ R) (fun _ => 0) t) :
    w.1.1 ∈ PDE.euclideanBall v₀ R := by
  have hw := w.2.1
  rw [movingDomain_ball_zero] at hw
  exact hw

/-- Convert a physical ball start to its (velocity, position) evolution state. -/
def ballStartState {d : ℕ} {v₀ : PDE.Vec d} {R : ℝ} (P : LocalBallStart v₀ R) :
    EvolutionState (PDE.euclideanBall v₀ R) (fun _ => 0) P.1.time :=
  ⟨(P.1.velocity, P.1.position), ball_start_state_mem P⟩

/-- Convert an evolution state at t to a physical point with valid velocity. -/
def ballStateStart {d : ℕ} {v₀ : PDE.Vec d} {R : ℝ} (t : ℝ)
    (w : EvolutionState (PDE.euclideanBall v₀ R) (fun _ => 0) t) :
    LocalBallStart v₀ R :=
  ⟨⟨t, w.1.2, w.1.1⟩, ball_state_velocity_mem t w⟩

/-- Starting-point conversion preserves every physical coordinate. -/
@[simp] theorem ballStateStart_ballStartState {d : ℕ} {v₀ : PDE.Vec d} {R : ℝ}
    (P : LocalBallStart v₀ R) : ballStateStart P.1.time (ballStartState P) = P := rfl

/-- State conversion preserves both terminal coordinates and the valid-fiber proof. -/
@[simp] theorem ballStartState_ballStateStart {d : ℕ} {v₀ : PDE.Vec d} {R : ℝ} (t : ℝ)
    (w : EvolutionState (PDE.euclideanBall v₀ R) (fun _ => 0) t) :
    ballStartState (ballStateStart t w) = w := rfl

/-- Exit coordinates depend continuously on the physical exit point. -/
theorem continuous_exitCoordinates {d : ℕ} (P : KineticPoint d) (v₀ : PDE.Vec d) :
    Continuous (exitCoordinates P v₀) :=
  ((continuous_position.sub continuous_const).sub
    ((continuous_time.sub continuous_const).smul continuous_const)).prodMk
    (continuous_time.prodMk continuous_velocity)

/-- Exit coordinates are measurable for boundary-measure transport. -/
theorem measurable_exitCoordinates {d : ℕ} (P : KineticPoint d) (v₀ : PDE.Vec d) :
    Measurable (exitCoordinates P v₀) := (continuous_exitCoordinates P v₀).measurable

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
