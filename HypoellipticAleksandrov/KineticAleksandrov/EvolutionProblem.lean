module

public import Mathlib.Topology.Algebra.Support
public import HypoellipticAleksandrov.KineticAleksandrov.BoundedBorel
public import HypoellipticAleksandrov.KineticAleksandrov.Geometry
public import HypoellipticAleksandrov.KineticAleksandrov.MovingKernel
public import HypoellipticAleksandrov.KineticAleksandrov.Operator
public import HypoellipticAleksandrov.Parabolic.ScalarClassical
public import PDEFoundation.Geometry.ConvexDomain
public import PDEFoundation.Measure.OneDimensionalCoordinate

/-!
# Terminal evolution problem

This module contains the literal carriers and hypotheses for the author-
terminal-evolution statement.  It records the moving domain, the
classical solution predicate, and the scalar marginal constructions used by
that statement.  It does not prove an existence or uniqueness theorem.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov.Parabolic
open scoped MatrixOrder ProbabilityTheory

namespace HypoellipticAleksandrov.KineticAleksandrov

/-! ## Domains and moving cylinders -/

/-- The base domains allowed by the terminal-evolution conditions. -/
def IsAdmissibleEvolutionDomain {n : ℕ} (Ω : Set (PDE.Vec n)) : Prop :=
  Ω = Set.univ ∨
    (∃ c r, 0 < r ∧ Ω = PDE.euclideanBall c r) ∨
      (∃ hn : n = 1, ∃ a b, a < b ∧
        hn ▸ Ω = PDE.oneDimensionalAxisBox a b)

/-- An admissible base domain is open. -/
theorem isOpen_of_isAdmissibleEvolutionDomain {n : ℕ}
    {Ω : Set (PDE.Vec n)}
    (hΩ : IsAdmissibleEvolutionDomain Ω) : IsOpen Ω := by
  rcases hΩ with hΩ | ⟨c, r, hr, hΩ⟩ | ⟨hn, a, b, hab, hΩ⟩
  · rw [hΩ]
    exact isOpen_univ
  · rw [hΩ]
    exact PDE.isOpen_euclideanBall c r
  · cases hn
    have hΩ' : Ω = PDE.oneDimensionalAxisBox a b := by
      simpa using hΩ
    rw [hΩ']
    simpa [PDE.oneDimensionalAxisBox] using
      (PDE.isOpen_axisBox (fun _ : Fin 1 => a) (fun _ : Fin 1 => b))

/-- An admissible base domain is Borel measurable. -/
theorem measurableSet_of_isAdmissibleEvolutionDomain {n : ℕ}
    {Ω : Set (PDE.Vec n)}
    (hΩ : IsAdmissibleEvolutionDomain Ω) : MeasurableSet Ω :=
  (isOpen_of_isAdmissibleEvolutionDomain hΩ).measurableSet

/-- The moving domain is open for an admissible base domain. -/
theorem isOpen_movingDomain_of_isAdmissibleEvolutionDomain {n : ℕ}
    {Ω : Set (PDE.Vec n)} (γ : ℝ → PDE.Vec n)
    (hΩ : IsAdmissibleEvolutionDomain Ω) (σ : ℝ) :
    IsOpen (movingDomain Ω γ σ) :=
  isOpen_movingDomain (isOpen_of_isAdmissibleEvolutionDomain hΩ) σ

/-- The moving domain is Borel measurable for an admissible base domain. -/
theorem measurableSet_movingDomain_of_isAdmissibleEvolutionDomain {n : ℕ}
    {Ω : Set (PDE.Vec n)} (γ : ℝ → PDE.Vec n)
    (hΩ : IsAdmissibleEvolutionDomain Ω) (σ : ℝ) :
    MeasurableSet (movingDomain Ω γ σ) :=
  measurableSet_movingDomain
    (measurableSet_of_isAdmissibleEvolutionDomain hΩ) σ

/-- A continuous curve that is piecewise `C¹` on every compact subinterval. -/
def IsContinuousPiecewiseC1 {n : ℕ} (γ : ℝ → PDE.Vec n) : Prop :=
  Continuous γ ∧
    ∀ a b, a < b →
      ∃ N : ℕ, ∃ t : Fin (N + 2) → ℝ, StrictMono t ∧ t 0 = a ∧
        t (Fin.last (N + 1)) = b ∧
          ∀ i : Fin (N + 1),
            ContDiffOn ℝ 1 γ (Set.Icc (t i.castSucc) (t i.succ))

/-! ## Coefficient and drift hypotheses -/

/-- Smoothness of a full coefficient in the ordered `(σ,y,z)` variables. -/
def IsSmoothFullKineticCoefficient {n : ℕ}
    (B : FullKineticCoefficient n) : Prop :=
  ∀ i j, ContDiff ℝ (⊤ : ℕ∞)
    (fun q : ℝ × (PDE.Vec n × PDE.Vec n) => B q.1 q.2.1 q.2.2 i j)

/-- Pointwise symmetry of every matrix of a full coefficient. -/
def IsSymmetricFullKineticCoefficient {n : ℕ}
    (B : FullKineticCoefficient n) : Prop :=
  ∀ σ y z, (B σ y z).IsSymm

/-- A full coefficient obeys the source's everywhere Loewner bounds. -/
def HasEverywhereLoewnerBounds {n : ℕ} (lam Lam : ℝ)
    (B : FullKineticCoefficient n) : Prop :=
  ∀ σ y z,
    lam • (1 : PDE.Mat n) ≤ B σ y z ∧
      B σ y z ≤ Lam • (1 : PDE.Mat n)

/-- Smoothness of the drift in the Euclidean vector carrier. -/
def IsSmoothDrift {n : ℕ} (b : PDE.Vec n → PDE.Vec n) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) b

/-- The Euclidean Lipschitz estimate for the drift. -/
def HasEuclideanLipschitzDrift {n : ℕ} (L_b : ℝ)
    (b : PDE.Vec n → PDE.Vec n) : Prop :=
  ∀ y y',
    PDE.vecEuclideanNorm (b y - b y') ≤
      L_b * PDE.vecEuclideanNorm (y - y')

/-- The unit-direction derivative coercivity estimate for the drift. -/
def HasUnitDirectionDriftCoercivity {n : ℕ} (m : ℝ)
    (b : PDE.Vec n → PDE.Vec n) : Prop :=
  ∀ y ξ, PDE.vecEuclideanNorm ξ = 1 →
    m ≤ PDE.vecDot ξ ((fderiv ℝ b y) ξ)

/-! ## Smooth compactly supported terminal data -/

/-- Smooth compactly supported data supported in the terminal state fiber. -/
def IsSmoothCompactTerminalDatum {n : ℕ}
    (Ω : Set (PDE.Vec n)) (γ : ℝ → PDE.Vec n) (τ : ℝ)
    (F : BoundedBorel (EvolutionAmbientState n)) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) F ∧ HasCompactSupport F ∧
    tsupport F ⊆ evolutionStateSet Ω γ τ

/-! ## Operator and classical-solution carriers -/

/-- The one shared real-linear terminal operator family. -/
abbrev TerminalOperatorFamily {n : ℕ} (Ω : Set (PDE.Vec n))
    (γ : ℝ → PDE.Vec n) :=
  ∀ (σ τ : ℝ), σ ≤ τ →
    BoundedBorel (EvolutionState Ω γ τ) →ₗ[ℝ]
      BoundedBorel (EvolutionState Ω γ σ)

/-- The one shared real-linear scalar marginal operator family. -/
abbrev ParabolicOperatorFamily {n : ℕ} (Ω : Set (PDE.Vec n))
    (γ : ℝ → PDE.Vec n) :=
  ∀ (σ τ : ℝ), σ ≤ τ →
    BoundedBorel (EvolutionPosition Ω γ τ) →ₗ[ℝ]
      BoundedBorel (EvolutionPosition Ω γ σ)

/-- The open past moving cylinder, with arbitrary transported coordinate. -/
def evolutionPastOpenCylinder {n : ℕ} (Ω : Set (PDE.Vec n))
    (γ : ℝ → PDE.Vec n) (τ : ℝ) : Set (KineticPoint n) :=
  {p | p.time < τ ∧ p.position ∈ movingDomain Ω γ p.time}

/-- The closed past moving cylinder, with arbitrary transported coordinate. -/
def evolutionPastClosedCylinder {n : ℕ} (Ω : Set (PDE.Vec n))
    (γ : ℝ → PDE.Vec n) (τ : ℝ) : Set (KineticPoint n) :=
  {p | p.time ≤ τ ∧ p.position ∈ closure (movingDomain Ω γ p.time)}

/-- Raw coordinate carrier for interior smoothness of a kinetic solution. -/
def evolutionPastInteriorRaw {n : ℕ} (Ω : Set (PDE.Vec n))
    (γ : ℝ → PDE.Vec n) (τ : ℝ) : Set (ℝ × (PDE.Vec n × PDE.Vec n)) :=
  {q | q.1 < τ ∧ q.2.1 ∈ movingDomain Ω γ q.1}

/-- The terminal face of the closed past moving cylinder. -/
def evolutionTerminalClosure {n : ℕ} (Ω : Set (PDE.Vec n))
    (γ : ℝ → PDE.Vec n) (τ : ℝ) : Set (KineticPoint n) :=
  {p | p.time = τ ∧ p.position ∈ closure (movingDomain Ω γ τ)}

/-- The lateral frontier of the closed past moving cylinder. -/
def evolutionLateralFrontier {n : ℕ} (Ω : Set (PDE.Vec n))
    (γ : ℝ → PDE.Vec n) (τ : ℝ) : Set (KineticPoint n) :=
  {p | p.time ≤ τ ∧ p.position ∈ frontier (movingDomain Ω γ p.time)}

/-- The literal classical terminal-solution predicate for the transported
operator.  It contains regularity, equation, and boundary conditions. -/
def IsClassicalTerminalSolution {n : ℕ}
    (Ω : Set (PDE.Vec n)) (γ : ℝ → PDE.Vec n)
    (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n)
    (τ : ℝ) (F : BoundedBorel (EvolutionAmbientState n))
    (u : KineticPoint n → ℝ) : Prop :=
  (∃ C : ℝ, 0 ≤ C ∧
      ∀ p ∈ evolutionPastClosedCylinder Ω γ τ, abs (u p) ≤ C) ∧
    ContinuousOn u (evolutionPastClosedCylinder Ω γ τ) ∧
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q => u ⟨q.1, q.2.1, q.2.2⟩)
      (evolutionPastInteriorRaw Ω γ τ) ∧
    (∀ p ∈ evolutionPastOpenCylinder Ω γ τ,
      transportedForwardOperator B b u p = 0) ∧
    (∀ p ∈ evolutionTerminalClosure Ω γ τ,
      u p = F (p.position, p.velocity)) ∧
    (∀ p ∈ evolutionLateralFrontier Ω γ τ, u p = 0)

/-- Shift the transported coordinate in an ambient fixed-time state. -/
def evolutionAmbientStateShift {n : ℕ} (h : PDE.Vec n)
    (p : EvolutionAmbientState n) : EvolutionAmbientState n :=
  (p.1, p.2 + h)

/-- Shift the transported coordinate in a moving fiber state. -/
def evolutionStateShift {n : ℕ} (Ω : Set (PDE.Vec n))
    (γ : ℝ → PDE.Vec n) (σ : ℝ) (h : PDE.Vec n)
    (p : EvolutionState Ω γ σ) : EvolutionState Ω γ σ :=
  ⟨evolutionAmbientStateShift h p.1, ⟨p.2.1, mem_univ _⟩⟩

/-- Insert a position and transported coordinate into a moving state fiber. -/
def evolutionStateOfPosition {n : ℕ} (Ω : Set (PDE.Vec n))
    (γ : ℝ → PDE.Vec n) (σ : ℝ)
    (y : EvolutionPosition Ω γ σ) (z : PDE.Vec n) : EvolutionState Ω γ σ :=
  ⟨(y.1, z), ⟨y.2, mem_univ _⟩⟩

/-- The measurable zero-transport-coordinate lift of a position state. -/
def positionStateZero {n : ℕ} (Ω : Set (PDE.Vec n))
    (γ : ℝ → PDE.Vec n) (σ : ℝ) :
    EvolutionPosition Ω γ σ → EvolutionState Ω γ σ :=
  fun y => evolutionStateOfPosition Ω γ σ y 0

/-- Measurability of the zero-transport-coordinate position-state lift. -/
theorem measurable_positionStateZero {n : ℕ} (Ω : Set (PDE.Vec n))
    (γ : ℝ → PDE.Vec n) (σ : ℝ) :
    Measurable (positionStateZero Ω γ σ) := by
  apply Measurable.subtype_mk
  fun_prop

/-- The scalar marginal kernel pulled back from the same fiber kernel. -/
noncomputable def parabolicMarginalKernel {n : ℕ}
    {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n}
    (K : MovingFiberKernel Ω γ) (hΩ : MeasurableSet Ω)
    (σ τ : ℝ) (hστ : σ ≤ τ) :
    ProbabilityTheory.Kernel
      (EvolutionPosition Ω γ σ) (EvolutionPosition Ω γ τ) :=
  ProbabilityTheory.Kernel.comap
    (K.fiberFirstMarginal hΩ σ τ hστ)
    (positionStateZero Ω γ σ)
    (measurable_positionStateZero Ω γ σ)

/-- Evaluation of the scalar marginal pullback at a source position. -/
theorem parabolicMarginalKernel_apply {n : ℕ}
    {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n}
    (K : MovingFiberKernel Ω γ) (hΩ : MeasurableSet Ω)
    (σ τ : ℝ) (hστ : σ ≤ τ) (y : EvolutionPosition Ω γ σ) :
    parabolicMarginalKernel K hΩ σ τ hστ y =
      K.fiberFirstMarginal hΩ σ τ hστ (positionStateZero Ω γ σ y) :=
  rfl

namespace ParabolicProbe

/-- Smooth compactly supported scalar data on the moving terminal domain. -/
def IsSmoothCompactScalarTerminalDatum {n : ℕ}
    (Ω : Set (PDE.Vec n)) (γ : ℝ → PDE.Vec n) (τ : ℝ)
    (F : BoundedBorel (PDE.Vec n)) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) (F : PDE.Vec n → ℝ) ∧
    IsCompact (tsupport (F : PDE.Vec n → ℝ)) ∧
    tsupport (F : PDE.Vec n → ℝ) ⊆ movingDomain Ω γ τ

/-- The open past moving scalar-parabolic cylinder. -/
def scalarPastOpenCylinder {n : ℕ} (Ω : Set (PDE.Vec n))
    (γ : ℝ → PDE.Vec n) (τ : ℝ) : Set (TimeVelocity n) :=
  {p | p.1 < τ ∧ p.2 ∈ movingDomain Ω γ p.1}

/-- The closed past moving scalar-parabolic cylinder. -/
def scalarPastClosedCylinder {n : ℕ} (Ω : Set (PDE.Vec n))
    (γ : ℝ → PDE.Vec n) (τ : ℝ) : Set (TimeVelocity n) :=
  {p | p.1 ≤ τ ∧ p.2 ∈ closure (movingDomain Ω γ p.1)}

/-- The terminal face of the scalar-parabolic cylinder. -/
def scalarTerminalClosure {n : ℕ} (Ω : Set (PDE.Vec n))
    (γ : ℝ → PDE.Vec n) (τ : ℝ) : Set (TimeVelocity n) :=
  {p | p.1 = τ ∧ p.2 ∈ closure (movingDomain Ω γ τ)}

/-- The lateral frontier of the scalar-parabolic cylinder. -/
def scalarLateralFrontier {n : ℕ} (Ω : Set (PDE.Vec n))
    (γ : ℝ → PDE.Vec n) (τ : ℝ) : Set (TimeVelocity n) :=
  {p | p.1 ≤ τ ∧ p.2 ∈ frontier (movingDomain Ω γ p.1)}

/-- The literal classical terminal-solution predicate for the scalar
equation with coefficient `B σ y 0`; no uniqueness package is included. -/
def IsClassicalScalarTerminalSolution {n : ℕ}
    (Ω : Set (PDE.Vec n)) (γ : ℝ → PDE.Vec n)
    (B : FullKineticCoefficient n) (τ : ℝ)
    (F : BoundedBorel (PDE.Vec n)) (V : TimeVelocity n → ℝ) : Prop :=
  (∃ C : ℝ, 0 ≤ C ∧
      ∀ p ∈ scalarPastClosedCylinder Ω γ τ, abs (V p) ≤ C) ∧
    ContinuousOn V (scalarPastClosedCylinder Ω γ τ) ∧
    ContDiffOn ℝ (⊤ : ℕ∞) V (scalarPastOpenCylinder Ω γ τ) ∧
    (∀ p ∈ scalarPastOpenCylinder Ω γ τ,
      scalarParabolicOperator (fun σ y => B σ y 0) 0 V p = 0) ∧
    (∀ p ∈ scalarTerminalClosure Ω γ τ, V p = F p.2) ∧
    (∀ p ∈ scalarLateralFrontier Ω γ τ, V p = 0)

end ParabolicProbe

/-! The query carrier and ambient push-forward used to state the constrained
joint measurability clause for the derived scalar kernel. -/

/-- A query with ordered times and a source position in the moving domain. -/
abbrev ParabolicEvolutionQuery {n : ℕ} (Ω : Set (PDE.Vec n))
    (γ : ℝ → PDE.Vec n) :=
  {q : ℝ × (ℝ × PDE.Vec n) //
    q.1 ≤ q.2.1 ∧ q.2.2 ∈ movingDomain Ω γ q.1}

/-- The source position associated with a parabolic evolution query. -/
def parabolicQuerySource {n : ℕ} {Ω : Set (PDE.Vec n)}
    {γ : ℝ → PDE.Vec n} (q : ParabolicEvolutionQuery Ω γ) :
    EvolutionPosition Ω γ q.1.1 :=
  ⟨q.1.2.2, q.property.2⟩

/-- The ambient spatial measure obtained from the scalar marginal kernel. -/
noncomputable def parabolicMarginalAmbientMeasure {n : ℕ}
    {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n}
    (K : MovingFiberKernel Ω γ) (hΩ : MeasurableSet Ω)
    (q : ParabolicEvolutionQuery Ω γ) : Measure (PDE.Vec n) :=
  Measure.map
    ((↑) : EvolutionPosition Ω γ q.1.2.1 → PDE.Vec n)
    (parabolicMarginalKernel K hΩ q.1.1 q.1.2.1 q.property.1
      (parabolicQuerySource q))

/-- Restriction of ambient terminal data to a terminal state fiber. -/
def terminalStateDatum {n : ℕ} {Ω : Set (PDE.Vec n)}
    {γ : ℝ → PDE.Vec n} {τ : ℝ}
    (F : BoundedBorel (EvolutionAmbientState n)) :
    BoundedBorel (EvolutionState Ω γ τ) :=
  BoundedBorel.restrict (evolutionStateSet Ω γ τ) F

/-- Restriction of scalar terminal data to a moving position fiber. -/
def terminalPositionDatum {n : ℕ} {Ω : Set (PDE.Vec n)}
    {γ : ℝ → PDE.Vec n} {τ : ℝ}
    (F : BoundedBorel (PDE.Vec n)) :
    BoundedBorel (EvolutionPosition Ω γ τ) :=
  BoundedBorel.restrict (movingDomain Ω γ τ) F

end HypoellipticAleksandrov.KineticAleksandrov
