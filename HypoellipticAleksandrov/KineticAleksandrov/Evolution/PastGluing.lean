module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.PastGluingFinite
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.PastGluingLocality
import Mathlib.Tactic.Linarith

/-! # Gluing finite-past viscous terminal solutions

Uniqueness identifies the solutions on every overlap. The same uniformly bounded
family then gives one classical solution on the entire past moving cylinder.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set Filter
open scoped Topology MatrixOrder

/-- Evaluate a finite-slab family using a lower time strictly below the query and terminal. -/
def pastGluedFunction {n : ℕ} (τ : ℝ) (u : ℝ → KineticPoint n → ℝ)
    (p : KineticPoint n) : ℝ := u (min (p.time - 1) (τ - 1)) p

section Family
variable {n : ℕ} {Ω : Set (PDE.Vec n)} (hΩ : IsOpen Ω)
variable {γ : ℝ → PDE.Vec n} (hγ : Continuous γ) {lam Lam : ℝ} (hlam : 0 < lam)
variable {B : FullKineticCoefficient n} (hB : HasEverywhereLoewnerBounds lam Lam B)
variable {Lb : ℝ} {b : PDE.Vec n → PDE.Vec n} (hb : HasEuclideanLipschitzDrift Lb b)
variable {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) {τ : ℝ}
variable {F : BoundedBorel (EvolutionAmbientState n)} (u : ℝ → KineticPoint n → ℝ)
variable (hu : ∀ a, a < τ → IsClassicalViscousFiniteSolution Ω γ B b ε a τ F (u a))
include hΩ hγ hlam hB hb hε0 hε1 hu

/-- The glued value equals every finite-slab solution wherever that slab is active in time. -/
theorem pastGluedFunction_eq {a : ℝ} (haτ : a < τ) {p : KineticPoint n}
    (hp : p ∈ evolutionPastClosedCylinder Ω γ τ) (ha : a < p.time) :
    pastGluedFunction τ u p = u a p := by
  have ht : min (p.time - 1) (τ - 1) < τ :=
    lt_of_le_of_lt (min_le_right _ _) (sub_lt_self _ zero_lt_one)
  have hs : min (p.time - 1) (τ - 1) < p.time :=
    lt_of_le_of_lt (min_le_left _ _) (sub_lt_self _ zero_lt_one)
  exact finite_classical_unique hΩ hγ hlam hB hb hε0 hε1
    (hu _ ht) (hu a haτ) p hp hs ha

/-- Gluing preserves the uniform global bound, continuity, smoothness, equation and traces. -/
theorem pastGluedFunction_isClassical {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ a, a < τ → ∀ p ∈ movingClosedSlab Ω γ a τ, |u a p| ≤ C) :
    IsClassicalViscousTerminalSolution Ω γ B b ε τ F (pastGluedFunction τ u) ∧
      (∀ p ∈ evolutionPastClosedCylinder Ω γ τ, |pastGluedFunction τ u p| ≤ C) := by
  have hboundG : ∀ p ∈ evolutionPastClosedCylinder Ω γ τ,
      |pastGluedFunction τ u p| ≤ C := by
    intro p hp
    have ht : min (p.time - 1) (τ - 1) < τ :=
      lt_of_le_of_lt (min_le_right _ _) (sub_lt_self _ zero_lt_one)
    exact hbound _ ht p ⟨(min_le_left _ _).trans (sub_le_self _ zero_le_one), hp⟩
  refine ⟨⟨⟨C, hC, hboundG⟩, ?_, ?_, ?_, ?_, ?_⟩, hboundG⟩
  · intro p hp
    let a := p.time - 1
    have ha : a < p.time := sub_lt_self _ zero_lt_one
    have haτ : a < τ := ha.trans_le hp.1
    have hs : movingClosedSlab Ω γ a τ ∈ 𝓝[evolutionPastClosedCylinder Ω γ τ] p := by
      have ht : ∀ᶠ q : KineticPoint n in 𝓝 p, a < q.time :=
        (isOpen_lt continuous_const continuous_time).mem_nhds ha
      filter_upwards [ht.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with q hq hqp
      exact ⟨hq.le, hqp⟩
    have hc := ((hu a haτ).2.1 p ⟨ha.le, hp⟩).mono_of_mem_nhdsWithin hs
    apply hc.congr_of_eventuallyEq ?_ ?_
    · have ht : ∀ᶠ q : KineticPoint n in 𝓝 p, a < q.time :=
        (isOpen_lt continuous_const continuous_time).mem_nhds ha
      filter_upwards [ht.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with q hq hqp
      exact pastGluedFunction_eq hΩ hγ hlam hB hb hε0 hε1 u hu haτ hqp hq
    · exact pastGluedFunction_eq hΩ hγ hlam hB hb hε0 hε1 u hu haτ hp ha
  · intro q hq
    let a := q.1 - 1
    have ha : a < q.1 := sub_lt_self _ zero_lt_one
    have haτ : a < τ := ha.trans hq.1
    have hmem : q ∈ evolutionFiniteInteriorRaw Ω γ a τ := ⟨ha, hq⟩
    have hn := (isOpen_evolutionFiniteInteriorRaw hΩ hγ a τ).mem_nhds hmem
    have hc := (hu a haτ).2.2.1.contDiffAt hn
    apply ContDiffAt.contDiffWithinAt (hc.congr_of_eventuallyEq ?_)
    filter_upwards [hn] with r hr
    exact pastGluedFunction_eq hΩ hγ hlam hB hb hε0 hε1 u hu haτ
      ⟨hr.2.1.le, subset_closure hr.2.2⟩ hr.1
  · intro p hp
    let a := p.time - 1
    have ha : a < p.time := sub_lt_self _ zero_lt_one
    have haτ : a < τ := ha.trans hp.1
    have he : pastGluedFunction τ u =ᶠ[𝓝 p] u a := by
      have ht : ∀ᶠ q : KineticPoint n in 𝓝 p, a < q.time ∧ q.time < τ :=
        ((isOpen_lt continuous_const continuous_time).inter
          (isOpen_lt continuous_time continuous_const)).mem_nhds ⟨ha, hp.1⟩
      have hd := (isOpen_setOf_mem_movingDomain hΩ hγ).mem_nhds hp.2
      filter_upwards [ht, hd] with q hqt hqd
      exact pastGluedFunction_eq hΩ hγ hlam hB hb hε0 hε1 u hu haτ
        ⟨hqt.2.le, subset_closure hqd⟩ hqt.1
    rw [viscousTransportedOperator_congr_germ B b ε he]
    exact (hu a haτ).2.2.2.1 p ⟨ha.le, hp⟩ ha
  · intro p hp
    have ha : p.time - 1 < p.time := sub_lt_self _ zero_lt_one
    have haτ : p.time - 1 < τ := hp.1 ▸ ha
    rw [pastGluedFunction_eq hΩ hγ hlam hB hb hε0 hε1 u hu haτ
      ⟨hp.1.le, hp.1 ▸ hp.2⟩ ha]
    exact (hu _ haτ).2.2.2.2.1 p hp
  · intro p hp
    have ha : p.time - 1 < p.time := sub_lt_self _ zero_lt_one
    have haτ : p.time - 1 < τ := ha.trans_le hp.1
    have hpc : p ∈ evolutionPastClosedCylinder Ω γ τ :=
      ⟨hp.1, frontier_subset_closure hp.2⟩
    rw [pastGluedFunction_eq hΩ hγ hlam hB hb hε0 hε1 u hu haτ hpc ha]
    exact (hu _ haτ).2.2.2.2.2 p ⟨ha.le, hpc⟩ hp.2

end Family

/-- The PastGluing step consumes actual uniformly bounded solutions on every finite slab.
It does not assert that the exhaustion construction supplying those solutions is complete. -/
theorem exists_viscous_terminalSolution_of_finiteSlabs {n : ℕ}
    {Ω : Set (PDE.Vec n)} (hΩ : IsOpen Ω) {γ : ℝ → PDE.Vec n} (hγ : Continuous γ)
    {lam Lam : ℝ} (hlam : 0 < lam) {B : FullKineticCoefficient n}
    (hB : HasEverywhereLoewnerBounds lam Lam B) {Lb : ℝ}
    {b : PDE.Vec n → PDE.Vec n} (hb : HasEuclideanLipschitzDrift Lb b)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (τ : ℝ)
    (F : BoundedBorel (EvolutionAmbientState n)) (C : ℝ) (hC : 0 ≤ C)
    (hfinite : ∀ a : ℝ, a < τ → ∃ u : KineticPoint n → ℝ,
      IsClassicalViscousFiniteSolution Ω γ B b ε a τ F u ∧
        ∀ p ∈ movingClosedSlab Ω γ a τ, |u p| ≤ C) :
    ∃ u : KineticPoint n → ℝ,
      IsClassicalViscousTerminalSolution Ω γ B b ε τ F u ∧
      (∀ p ∈ evolutionPastClosedCylinder Ω γ τ, |u p| ≤ C) ∧
      (∀ v : KineticPoint n → ℝ,
        IsClassicalViscousTerminalSolution Ω γ B b ε τ F v →
          EqOn v u (evolutionPastClosedCylinder Ω γ τ)) := by
  have hex : ∀ a : ℝ, ∃ u : KineticPoint n → ℝ, a < τ →
      IsClassicalViscousFiniteSolution Ω γ B b ε a τ F u ∧
        ∀ p ∈ movingClosedSlab Ω γ a τ, |u p| ≤ C := by
    intro a
    by_cases ha : a < τ
    · obtain ⟨u, hu⟩ := hfinite a ha
      exact ⟨u, fun _ => hu⟩
    · exact ⟨fun _ => 0, fun h => (ha h).elim⟩
  choose u hu using hex
  obtain ⟨hg, hgb⟩ := pastGluedFunction_isClassical hΩ hγ hlam hB hb hε0 hε1 u
    (fun a ha => (hu a ha).1) hC (fun a ha => (hu a ha).2)
  refine ⟨pastGluedFunction τ u, hg, hgb, ?_⟩
  intro v hv
  exact classical_unique hΩ hγ hlam hB hb hε0 hε1 hv hg

end HypoellipticAleksandrov.KineticAleksandrov
