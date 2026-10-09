module

public import Mathlib.Probability.Kernel.Composition.MapComap
public import Mathlib.Probability.Kernel.Composition.Comp
public import Mathlib.MeasureTheory.Measure.Restrict
public import HypoellipticAleksandrov.Ambient.Basic

/-!
# Moving-fiber kernels

This module fixes the carrier for the terminal evolution kernel.  Invalid
time pairs and off-domain source states have no values: the master kernel is
defined only on the corresponding valid-query subtype.  Fixed-time kernels
are obtained from that one master kernel by `Kernel.comap` and
`Kernel.comapRight`.
-/

@[expose] public section

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal ProbabilityTheory

namespace HypoellipticAleksandrov.KineticAleksandrov

/-- The ambient fixed-time state `(y, z)`. -/
abbrev EvolutionAmbientState (n : ℕ) := PDE.Vec n × PDE.Vec n

/-- The moving spatial domain obtained by translating the base domain. -/
def movingDomain {n : ℕ} (Ω : Set (PDE.Vec n)) (γ : ℝ → PDE.Vec n) (σ : ℝ) :
    Set (PDE.Vec n) :=
  PDE.translateSet (γ σ) Ω

/-- The open ambient state fiber at a fixed time. -/
def evolutionStateSet {n : ℕ} (Ω : Set (PDE.Vec n))
    (γ : ℝ → PDE.Vec n) (σ : ℝ) : Set (EvolutionAmbientState n) :=
  movingDomain Ω γ σ ×ˢ Set.univ

/-- A state whose diffused coordinate lies in the moving spatial domain. -/
abbrev EvolutionState {n : ℕ} (Ω : Set (PDE.Vec n))
    (γ : ℝ → PDE.Vec n) (σ : ℝ) :=
  {p : EvolutionAmbientState n // p ∈ evolutionStateSet Ω γ σ}

/-- The diffused-coordinate subtype in a moving spatial fiber. -/
abbrev EvolutionPosition {n : ℕ} (Ω : Set (PDE.Vec n))
    (γ : ℝ → PDE.Vec n) (σ : ℝ) :=
  {y : PDE.Vec n // y ∈ movingDomain Ω γ σ}

/-- The raw `(sigma, (tau, (y, z)))` query carrier. -/
abbrev RawEvolutionQuery (n : ℕ) :=
  ℝ × (ℝ × EvolutionAmbientState n)

/-- A query with valid time order and a source state in the moving fiber. -/
abbrev EvolutionQuery {n : ℕ} (Ω : Set (PDE.Vec n))
    (γ : ℝ → PDE.Vec n) :=
  {q : RawEvolutionQuery n //
    q.1 ≤ q.2.1 ∧ q.2.2 ∈ evolutionStateSet Ω γ q.1}

/-- Measurability of the translated moving spatial domain. -/
theorem measurableSet_movingDomain {n : ℕ} {Ω : Set (PDE.Vec n)}
    {γ : ℝ → PDE.Vec n} (hΩ : MeasurableSet Ω) (σ : ℝ) :
    MeasurableSet (movingDomain Ω γ σ) := by
  rw [movingDomain, ← PDE.preimage_subRight_eq_translateSet]
  exact hΩ.preimage (measurable_id.sub measurable_const)

/-- Openness of the translated moving spatial domain. -/
theorem isOpen_movingDomain {n : ℕ} {Ω : Set (PDE.Vec n)}
    {γ : ℝ → PDE.Vec n} (hΩ : IsOpen Ω) (σ : ℝ) :
    IsOpen (movingDomain Ω γ σ) := by
  rw [movingDomain, ← PDE.preimage_subRight_eq_translateSet]
  exact hΩ.preimage (continuous_id.sub continuous_const)

/-- Measurability of the ambient moving state fiber. -/
theorem measurableSet_evolutionStateSet {n : ℕ} {Ω : Set (PDE.Vec n)}
    {γ : ℝ → PDE.Vec n} (hΩ : MeasurableSet Ω) (σ : ℝ) :
    MeasurableSet (evolutionStateSet Ω γ σ) := by
  exact (measurableSet_movingDomain hΩ σ).prod MeasurableSet.univ

/-- The canonical valid query associated with a fixed-time source state. -/
def evolutionQueryOfState {n : ℕ} (Ω : Set (PDE.Vec n))
    (γ : ℝ → PDE.Vec n) (σ τ : ℝ) (hστ : σ ≤ τ)
    (p : EvolutionState Ω γ σ) : EvolutionQuery Ω γ :=
  ⟨(σ, (τ, p.1)), hστ, p.2⟩

/-- The canonical query lift is measurable on its subtype source. -/
theorem measurable_evolutionQueryOfState {n : ℕ} (Ω : Set (PDE.Vec n))
    (γ : ℝ → PDE.Vec n) (σ τ : ℝ) (hστ : σ ≤ τ) :
    Measurable (evolutionQueryOfState Ω γ σ τ hστ) := by
  apply Measurable.subtype_mk
  fun_prop

/-- One master kernel on all valid source/time queries. -/
structure MovingFiberKernel {n : ℕ} (Ω : Set (PDE.Vec n))
    (γ : ℝ → PDE.Vec n) where
  master : ProbabilityTheory.Kernel
    (EvolutionQuery Ω γ) (EvolutionAmbientState n)
  /-- Every master output is supported on the open terminal state fiber. -/
  terminal_support : ∀ q : EvolutionQuery Ω γ,
    (master q).restrict (evolutionStateSet Ω γ q.1.2.1) = master q
  /-- The master kernel has sub-Markov mass. -/
  mass_le_one : ∀ q : EvolutionQuery Ω γ, master q Set.univ ≤ 1

namespace MovingFiberKernel

/-- Evaluation on a measurable target is jointly measurable in the query. -/
theorem jointlyMeasurable_apply {n : ℕ}
    {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n}
    (K : MovingFiberKernel Ω γ) (E : Set (EvolutionAmbientState n))
    (hE : MeasurableSet E) :
    Measurable (fun q : EvolutionQuery Ω γ => K.master q E) := by
  exact K.master.measurable_coe hE

/-- Derive the fixed-time kernel from the one ambient master kernel. -/
noncomputable def fiberKernel {n : ℕ}
    {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n}
    (K : MovingFiberKernel Ω γ) (hΩ : MeasurableSet Ω)
    (σ τ : ℝ) (hστ : σ ≤ τ) :
    ProbabilityTheory.Kernel
      (EvolutionState Ω γ σ) (EvolutionState Ω γ τ) :=
  ProbabilityTheory.Kernel.comapRight
    (ProbabilityTheory.Kernel.comap K.master
      (evolutionQueryOfState Ω γ σ τ hστ)
      (measurable_evolutionQueryOfState Ω γ σ τ hστ))
    (MeasurableEmbedding.subtype_coe
      (measurableSet_evolutionStateSet hΩ τ))

/-- The derived fiber is the right-measure comap of the master output. -/
theorem fiberKernel_apply {n : ℕ}
    {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n}
    (K : MovingFiberKernel Ω γ) (hΩ : MeasurableSet Ω)
    (σ τ : ℝ) (hστ : σ ≤ τ) (p : EvolutionState Ω γ σ) :
    K.fiberKernel hΩ σ τ hστ p =
      Measure.comap ((↑) : EvolutionState Ω γ τ → EvolutionAmbientState n)
        (K.master (evolutionQueryOfState Ω γ σ τ hστ p)) := by
  rfl

/-- Mapping a derived fiber measure back to the ambient state recovers master. -/
theorem map_fiberKernel_eq_master {n : ℕ}
    {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n}
    (K : MovingFiberKernel Ω γ) (hΩ : MeasurableSet Ω)
    (σ τ : ℝ) (hστ : σ ≤ τ) (p : EvolutionState Ω γ σ) :
    Measure.map
        ((↑) : EvolutionState Ω γ τ → EvolutionAmbientState n)
        (K.fiberKernel hΩ σ τ hστ p) =
      K.master (evolutionQueryOfState Ω γ σ τ hστ p) := by
  rw [MovingFiberKernel.fiberKernel_apply]
  have hmap :
      Measure.map
          ((↑) : {x : EvolutionAmbientState n //
            x ∈ evolutionStateSet Ω γ τ} → EvolutionAmbientState n)
          (Measure.comap
            ((↑) : {x : EvolutionAmbientState n //
              x ∈ evolutionStateSet Ω γ τ} → EvolutionAmbientState n)
            (K.master (evolutionQueryOfState Ω γ σ τ hστ p))) =
        (K.master (evolutionQueryOfState Ω γ σ τ hστ p)).restrict
          (evolutionStateSet Ω γ τ) := by
    simpa only [Subtype.range_coe] using
      (MeasurableEmbedding.subtype_coe
        (measurableSet_evolutionStateSet hΩ τ)).map_comap
        (K.master (evolutionQueryOfState Ω γ σ τ hστ p))
  change Measure.map
      ((↑) : {x : EvolutionAmbientState n //
        x ∈ evolutionStateSet Ω γ τ} → EvolutionAmbientState n)
      (Measure.comap
        ((↑) : {x : EvolutionAmbientState n //
          x ∈ evolutionStateSet Ω γ τ} → EvolutionAmbientState n)
        (K.master (evolutionQueryOfState Ω γ σ τ hστ p))) =
    K.master (evolutionQueryOfState Ω γ σ τ hστ p)
  exact hmap.trans
    (K.terminal_support (evolutionQueryOfState Ω γ σ τ hστ p))

/-- Every derived fiber measure is sub-Markov. -/
theorem fiberKernel_mass_le_one {n : ℕ}
    {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n}
    (K : MovingFiberKernel Ω γ) (hΩ : MeasurableSet Ω)
    (σ τ : ℝ) (hστ : σ ≤ τ) (p : EvolutionState Ω γ σ) :
    K.fiberKernel hΩ σ τ hστ p Set.univ ≤ 1 := by
  rw [MovingFiberKernel.fiberKernel_apply]
  calc
    Measure.comap ((↑) : EvolutionState Ω γ τ → EvolutionAmbientState n)
        (K.master (evolutionQueryOfState Ω γ σ τ hστ p)) Set.univ =
        K.master (evolutionQueryOfState Ω γ σ τ hστ p)
          (((↑) : EvolutionState Ω γ τ → EvolutionAmbientState n) '' Set.univ) := by
            exact (MeasurableEmbedding.subtype_coe
              (measurableSet_evolutionStateSet hΩ τ)).comap_apply _ _
    _ ≤ K.master (evolutionQueryOfState Ω γ σ τ hστ p) Set.univ :=
      measure_mono (Set.subset_univ _)
    _ ≤ 1 := K.mass_le_one (evolutionQueryOfState Ω γ σ τ hστ p)

/-- The first coordinate of a terminal ambient state, with its domain proof. -/
def firstPosition {n : ℕ} (Ω : Set (PDE.Vec n)) (γ : ℝ → PDE.Vec n)
    (τ : ℝ) : EvolutionState Ω γ τ → EvolutionPosition Ω γ τ :=
  fun p => ⟨p.1.1, p.2.1⟩

/-- Measurability of the first-coordinate map between moving fibers. -/
theorem measurable_firstPosition {n : ℕ} (Ω : Set (PDE.Vec n))
    (γ : ℝ → PDE.Vec n) (τ : ℝ) :
    Measurable (firstPosition Ω γ τ) := by
  apply Measurable.subtype_mk
  fun_prop

/-- The master first marginal, defined by Mathlib's `Kernel.fst`. -/
noncomputable def firstMarginal {n : ℕ}
    {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n}
    (K : MovingFiberKernel Ω γ) :
    ProbabilityTheory.Kernel (EvolutionQuery Ω γ) (PDE.Vec n) :=
  K.master.fst

/-- Application of the first marginal is the first-coordinate projection. -/
theorem firstMarginal_apply {n : ℕ}
    {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n}
    (K : MovingFiberKernel Ω γ) (q : EvolutionQuery Ω γ)
    (E : Set (PDE.Vec n)) (hE : MeasurableSet E) :
    K.firstMarginal q E = K.master q {p | p.1 ∈ E} := by
  exact ProbabilityTheory.Kernel.fst_apply' K.master q hE

/-- The fixed-time first marginal derived from the same fiber kernel. -/
noncomputable def fiberFirstMarginal {n : ℕ}
    {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n}
    (K : MovingFiberKernel Ω γ) (hΩ : MeasurableSet Ω)
    (σ τ : ℝ) (hστ : σ ≤ τ) :
    ProbabilityTheory.Kernel
      (EvolutionState Ω γ σ) (EvolutionPosition Ω γ τ) :=
  ProbabilityTheory.Kernel.map
    (K.fiberKernel hΩ σ τ hστ) (firstPosition Ω γ τ)

/-- Mapping the fixed-time first marginal back gives the master first marginal. -/
theorem map_fiberFirstMarginal_eq_firstMarginal {n : ℕ}
    {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n}
    (K : MovingFiberKernel Ω γ) (hΩ : MeasurableSet Ω)
    (σ τ : ℝ) (hστ : σ ≤ τ) (p : EvolutionState Ω γ σ) :
    Measure.map
        ((↑) : EvolutionPosition Ω γ τ → PDE.Vec n)
        (K.fiberFirstMarginal hΩ σ τ hστ p) =
      K.firstMarginal (evolutionQueryOfState Ω γ σ τ hστ p) := by
  rw [MovingFiberKernel.fiberFirstMarginal,
    ProbabilityTheory.Kernel.map_apply _
      (measurable_firstPosition Ω γ τ) p]
  calc
    Measure.map Subtype.val
        (Measure.map (firstPosition Ω γ τ)
          (K.fiberKernel hΩ σ τ hστ p)) =
        Measure.map Prod.fst
          (Measure.map ((↑) : EvolutionState Ω γ τ →
            EvolutionAmbientState n) (K.fiberKernel hΩ σ τ hστ p)) := by
      rw [Measure.map_map measurable_subtype_coe
        (measurable_firstPosition Ω γ τ),
        Measure.map_map measurable_fst measurable_subtype_coe]
      rfl
    _ = Measure.map Prod.fst
          (K.master (evolutionQueryOfState Ω γ σ τ hστ p)) := by
      rw [MovingFiberKernel.map_fiberKernel_eq_master K hΩ σ τ hστ p]
    _ = K.firstMarginal (evolutionQueryOfState Ω γ σ τ hστ p) := by
      rw [MovingFiberKernel.firstMarginal, ProbabilityTheory.Kernel.fst_apply]

/-- Endpoint identity for the derived fixed-time kernel. -/
def HasEndpoint {n : ℕ}
    {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n}
    (K : MovingFiberKernel Ω γ) (hΩ : MeasurableSet Ω) : Prop :=
  ∀ σ : ℝ,
    K.fiberKernel hΩ σ σ le_rfl =
      (ProbabilityTheory.Kernel.id :
        ProbabilityTheory.Kernel (EvolutionState Ω γ σ) (EvolutionState Ω γ σ))

/-- Chapman--Kolmogorov equality for the same derived kernel family. -/
def HasComposition {n : ℕ}
    {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n}
    (K : MovingFiberKernel Ω γ) (hΩ : MeasurableSet Ω) : Prop :=
  ∀ (σ r τ : ℝ) (hσr : σ ≤ r) (hrτ : r ≤ τ),
    K.fiberKernel hΩ σ τ (hσr.trans hrτ) =
      K.fiberKernel hΩ r τ hrτ ∘ₖ K.fiberKernel hΩ σ r hσr

end MovingFiberKernel

/-- Lift a small-domain query to the corresponding large-domain query. -/
def largeQueryOfSmall {n : ℕ}
    {Ωsmall Ωlarge : Set (PDE.Vec n)}
    {γsmall γlarge : ℝ → PDE.Vec n}
    (hsub : ∀ σ, movingDomain Ωsmall γsmall σ ⊆
      movingDomain Ωlarge γlarge σ)
    (q : EvolutionQuery Ωsmall γsmall) : EvolutionQuery Ωlarge γlarge :=
  ⟨q.1, q.2.1, ⟨hsub q.1.1 q.2.2.1, q.2.2.2⟩⟩

namespace MovingFiberKernel

/-- Ambient measure domination after zero extension outside the small fiber. -/
def IsZeroExtensionDominatedBy {n : ℕ}
    {Ωsmall Ωlarge : Set (PDE.Vec n)}
    {γsmall γlarge : ℝ → PDE.Vec n}
    (Ksmall : MovingFiberKernel Ωsmall γsmall)
    (Klarge : MovingFiberKernel Ωlarge γlarge)
    (hsub : ∀ σ, movingDomain Ωsmall γsmall σ ⊆
      movingDomain Ωlarge γlarge σ) : Prop :=
  ∀ q : EvolutionQuery Ωsmall γsmall,
    Ksmall.master q ≤ Klarge.master (largeQueryOfSmall hsub q)

end MovingFiberKernel

end HypoellipticAleksandrov.KineticAleksandrov
