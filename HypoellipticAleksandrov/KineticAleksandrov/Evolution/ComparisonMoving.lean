module

import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonCompact
public import HypoellipticAleksandrov.KineticAleksandrov.MovingKernel

/-!
# Moving slabs and their bounded truncations

Geometry of the moving cylinder `{(σ, y, z) : y ∈ γ(σ) + Ω}` used by the comparison
theorems: closures of moving domains, compactness of bounded truncations of the closed
slab `a ≤ σ ≤ b`, and the one-sided neighbourhood property of the active part.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov Filter Set
open scoped Topology

/-- The squared Euclidean size `|y|² + |z|²` of the spatial coordinates of a kinetic
point. -/
def radialSq {n : ℕ} (p : KineticPoint n) : ℝ :=
  PDE.vecNormSq p.position + PDE.vecNormSq p.velocity

/-- The closed moving slab `{a ≤ σ ≤ b, y ∈ closure (γ(σ) + Ω)}` (all `z`). -/
def movingClosedSlab {n : ℕ} (Ω : Set (PDE.Vec n)) (γ : ℝ → PDE.Vec n) (a b : ℝ) :
    Set (KineticPoint n) :=
  {p | a ≤ p.time ∧ p.time ≤ b ∧ p.position ∈ closure (movingDomain Ω γ p.time)}

/-- The active part `{a ≤ σ < b, y ∈ γ(σ) + Ω}` of the moving slab. -/
def movingActiveSlab {n : ℕ} (Ω : Set (PDE.Vec n)) (γ : ℝ → PDE.Vec n) (a b : ℝ) :
    Set (KineticPoint n) :=
  {p | a ≤ p.time ∧ p.time < b ∧ p.position ∈ movingDomain Ω γ p.time}

/-- A point of the closed moving cylinder lies in `movingClosedSlab` exactly when its
position is in the closure of the moving domain. -/
theorem mem_closure_movingDomain_iff {n : ℕ} {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n}
    {σ : ℝ} {y : PDE.Vec n} :
    y ∈ closure (movingDomain Ω γ σ) ↔ y - γ σ ∈ closure Ω := by
  have h : movingDomain Ω γ σ = (Homeomorph.subRight (γ σ)) ⁻¹' Ω := by
    rw [movingDomain, ← PDE.preimage_subRight_eq_translateSet]
    rfl
  rw [h, ← Homeomorph.preimage_closure]
  rfl

/-- Membership in the moving domain. -/
theorem mem_movingDomain_iff {n : ℕ} {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n}
    {σ : ℝ} {y : PDE.Vec n} : y ∈ movingDomain Ω γ σ ↔ y - γ σ ∈ Ω :=
  PDE.mem_translateSet_iff_sub_mem

/-- The set of kinetic points whose position lies in the moving domain is open. -/
theorem isOpen_setOf_mem_movingDomain {n : ℕ} {Ω : Set (PDE.Vec n)} (hΩ : IsOpen Ω)
    {γ : ℝ → PDE.Vec n} (hγ : Continuous γ) :
    IsOpen {p : KineticPoint n | p.position ∈ movingDomain Ω γ p.time} := by
  have hc : Continuous (fun p : KineticPoint n => p.position - γ p.time) :=
    continuous_position.sub (hγ.comp continuous_time)
  have := hΩ.preimage hc
  convert this using 1
  ext p
  exact mem_movingDomain_iff

/-- The set of kinetic points whose position lies in the closure of the moving domain
is closed. -/
theorem isClosed_setOf_mem_closure_movingDomain {n : ℕ} {Ω : Set (PDE.Vec n)}
    {γ : ℝ → PDE.Vec n} (hγ : Continuous γ) :
    IsClosed {p : KineticPoint n | p.position ∈ closure (movingDomain Ω γ p.time)} := by
  have hc : Continuous (fun p : KineticPoint n => p.position - γ p.time) :=
    continuous_position.sub (hγ.comp continuous_time)
  have := (isClosed_closure (s := Ω)).preimage hc
  convert this using 1
  ext p
  exact mem_closure_movingDomain_iff

/-- Continuity of `|y|² + |z|²`. -/
theorem continuous_radialSq {n : ℕ} : Continuous (@radialSq n) := by
  unfold radialSq PDE.vecNormSq PDE.vecDot
  have h1 : Continuous (@KineticPoint.position n) := continuous_position
  have h2 : Continuous (@KineticPoint.velocity n) := continuous_velocity
  fun_prop

/-- A closed set of kinetic points with bounded times has compact bounded truncations. -/
theorem isCompact_inter_radialSq {n : ℕ} {K : Set (KineticPoint n)} (hK : IsClosed K)
    {a b : ℝ} (hKt : ∀ p ∈ K, a ≤ p.time ∧ p.time ≤ b) (R : ℝ) :
    IsCompact (K ∩ {p | radialSq p ≤ R ^ 2}) := by
  let Kbig : Set (KineticPoint n) :=
    KineticPoint.homeomorphProd n ⁻¹'
      (Icc a b ×ˢ (Metric.closedBall (0 : PDE.Vec n) |R| ×ˢ Metric.closedBall (0 : PDE.Vec n) |R|))
  have hKbig : IsCompact Kbig :=
    (KineticPoint.homeomorphProd n).isCompact_preimage.mpr
      (isCompact_Icc.prod ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)))
  have hclosed : IsClosed (K ∩ {p | radialSq p ≤ R ^ 2}) :=
    hK.inter (isClosed_le continuous_radialSq continuous_const)
  refine hKbig.of_isClosed_subset hclosed ?_
  intro p hp
  obtain ⟨hpK, hr⟩ := hp
  obtain ⟨hat, htb⟩ := hKt p hpK
  have hbound : ∀ x : PDE.Vec n, PDE.vecNormSq x ≤ R ^ 2 →
      x ∈ Metric.closedBall (0 : PDE.Vec n) |R| := by
    intro x hx
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (abs_nonneg R)]
    intro i
    rw [Real.norm_eq_abs]
    have hi := PDE.sq_apply_le_vecNormSq x i
    exact abs_le_of_sq_le_sq (by rw [sq_abs]; exact hi.trans hx) (abs_nonneg R)
  have hr' : radialSq p ≤ R ^ 2 := hr
  have hpos := PDE.vecNormSq_nonneg p.position
  have hvel := PDE.vecNormSq_nonneg p.velocity
  refine ⟨⟨hat, htb⟩, hbound p.position ?_, hbound p.velocity ?_⟩
  · unfold radialSq at hr'; linarith
  · unfold radialSq at hr'; linarith

/-- The closed moving slab is closed. -/
theorem isClosed_movingClosedSlab {n : ℕ} {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n}
    (hγ : Continuous γ) (a b : ℝ) : IsClosed (movingClosedSlab Ω γ a b) := by
  have h1 : IsClosed {p : KineticPoint n | a ≤ p.time} :=
    isClosed_le continuous_const continuous_time
  have h2 : IsClosed {p : KineticPoint n | p.time ≤ b} :=
    isClosed_le continuous_time continuous_const
  have h3 := isClosed_setOf_mem_closure_movingDomain (Ω := Ω) (n := n) hγ
  have := (h1.inter h2).inter h3
  convert this using 1
  ext p
  simp only [movingClosedSlab, mem_inter_iff, Set.mem_ofPred_eq]
  tauto

/-- Bounded truncations of the closed moving slab are compact. -/
theorem isCompact_movingClosedSlab_inter {n : ℕ} {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n}
    (hγ : Continuous γ) (a b R : ℝ) :
    IsCompact (movingClosedSlab Ω γ a b ∩ {p | radialSq p ≤ R ^ 2}) :=
  isCompact_inter_radialSq (isClosed_movingClosedSlab hγ a b) (fun _ hp => ⟨hp.1, hp.2.1⟩) R

/-- The active part of the moving slab has the one-sided neighbourhood property. -/
theorem eventually_future_mem_movingClosedSlab {n : ℕ} {Ω : Set (PDE.Vec n)}
    (hΩ : IsOpen Ω) {γ : ℝ → PDE.Vec n} (hγ : Continuous γ) {a b : ℝ} {p : KineticPoint n}
    (hp : p ∈ movingActiveSlab Ω γ a b) :
    ∀ᶠ q in 𝓝 p, p.time ≤ q.time → q ∈ movingClosedSlab Ω γ a b := by
  obtain ⟨hat, htb, hpm⟩ := hp
  have h1 : ∀ᶠ q in 𝓝 p, q.position ∈ movingDomain Ω γ q.time :=
    (isOpen_setOf_mem_movingDomain hΩ hγ).mem_nhds hpm
  have h2 : ∀ᶠ q in 𝓝 p, q.time < b :=
    (isOpen_lt continuous_time continuous_const).mem_nhds htb
  filter_upwards [h1, h2] with q hq1 hq2 hqt
  exact ⟨hat.trans hqt, hq2.le, subset_closure hq1⟩

/-- A point of the closed moving slab that is not in the active part lies on the
terminal face or the lateral frontier. -/
theorem mem_boundary_of_movingClosedSlab {n : ℕ} {Ω : Set (PDE.Vec n)} (hΩ : IsOpen Ω)
    {γ : ℝ → PDE.Vec n} {a b : ℝ} {p : KineticPoint n}
    (hp : p ∈ movingClosedSlab Ω γ a b) (hnot : p ∉ movingActiveSlab Ω γ a b) :
    p.time = b ∨ p.position ∈ frontier (movingDomain Ω γ p.time) := by
  obtain ⟨hat, htb, hpc⟩ := hp
  by_cases h1 : p.time < b
  · by_cases h2 : p.position ∈ movingDomain Ω γ p.time
    · exact absurd ⟨hat, h1, h2⟩ hnot
    · right
      rw [(isOpen_movingDomain hΩ p.time).frontier_eq]
      exact ⟨hpc, h2⟩
  · left
    exact le_antisymm htb (not_lt.mp h1)

/-- The active part of a bounded truncation has the one-sided neighbourhood property:
every nearby point of no earlier time still lies in the truncated closed slab. -/
theorem eventually_future_mem_truncated {n : ℕ} {Ω : Set (PDE.Vec n)} (hΩ : IsOpen Ω)
    {γ : ℝ → PDE.Vec n} (hγ : Continuous γ) {a b R : ℝ} {p : KineticPoint n}
    (hp : p ∈ movingActiveSlab Ω γ a b ∩ {q | radialSq q < R ^ 2}) :
    ∀ᶠ q in 𝓝 p, p.time ≤ q.time →
      q ∈ movingClosedSlab Ω γ a b ∩ {q | radialSq q ≤ R ^ 2} := by
  obtain ⟨⟨hat, htb, hpm⟩, hr⟩ := hp
  have h1 : ∀ᶠ q in 𝓝 p, q.position ∈ movingDomain Ω γ q.time :=
    (isOpen_setOf_mem_movingDomain hΩ hγ).mem_nhds hpm
  have h2 : ∀ᶠ q in 𝓝 p, q.time < b :=
    (isOpen_lt continuous_time continuous_const).mem_nhds htb
  have h3 : ∀ᶠ q in 𝓝 p, radialSq q < R ^ 2 :=
    (isOpen_lt continuous_radialSq continuous_const).mem_nhds hr
  filter_upwards [h1, h2, h3] with q hq1 hq2 hq3 hqt
  exact ⟨⟨hat.trans hqt, hq2.le, subset_closure hq1⟩, hq3.le⟩

/-- A point of the truncated closed slab that is not in the active part lies on the
terminal face, the lateral frontier, or the artificial radial boundary. -/
theorem mem_boundary_of_truncated {n : ℕ} {Ω : Set (PDE.Vec n)} (hΩ : IsOpen Ω)
    {γ : ℝ → PDE.Vec n} {a b R : ℝ} {p : KineticPoint n}
    (hp : p ∈ movingClosedSlab Ω γ a b ∩ {q | radialSq q ≤ R ^ 2})
    (hnot : p ∉ movingActiveSlab Ω γ a b ∩ {q | radialSq q < R ^ 2}) :
    p.time = b ∨ p.position ∈ frontier (movingDomain Ω γ p.time) ∨ radialSq p = R ^ 2 := by
  obtain ⟨⟨hat, htb, hpc⟩, hr⟩ := hp
  by_cases h1 : p.time < b
  · by_cases h2 : p.position ∈ movingDomain Ω γ p.time
    · right; right
      by_contra h3
      exact hnot ⟨⟨hat, h1, h2⟩, lt_of_le_of_ne hr h3⟩
    · right; left
      have hopen : IsOpen (movingDomain Ω γ p.time) :=
        isOpen_movingDomain hΩ p.time
      rw [hopen.frontier_eq]
      exact ⟨hpc, h2⟩
  · left
    exact le_antisymm htb (not_lt.mp h1)

end HypoellipticAleksandrov.KineticAleksandrov
