module

import Mathlib.Tactic.Linarith
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.FiniteSlabBarriersTerminal

/-!
# Whole-space terminal comparison

Companion paper, (A.1), the case `Ω = ℝⁿ`.  There is no lateral boundary, hence no collar and no
curve estimate: for a viscous classical terminal solution `u_ε` with smooth compactly supported
terminal datum `F`, comparison with `F ± (τ - σ) M` on the finite slab `[a, τ]` gives
`|u_ε - F| ≤ (τ - σ) M` wherever `|L_ε F| ≤ M`.  When `Ω = ℝⁿ` the moving domain does not depend
on the curve, so `γ` is an arbitrary function here (it is replaced by the constant curve `0`).
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Filter Set
open scoped Topology MatrixOrder

/-- The moving domain over the whole space is the whole space. -/
theorem movingDomain_univ {n : ℕ} (γ : ℝ → PDE.Vec n) (σ : ℝ) :
    movingDomain (Set.univ : Set (PDE.Vec n)) γ σ = Set.univ := by
  ext y
  simp [mem_movingDomain_iff]

/-- Over the whole space the viscous classical-solution predicate does not depend on the curve. -/
theorem isClassicalViscousTerminalSolution_univ_curve_congr {n : ℕ} (γ γ' : ℝ → PDE.Vec n)
    (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n) (ε τ : ℝ)
    (F : BoundedBorel (EvolutionAmbientState n)) (u : KineticPoint n → ℝ) :
    IsClassicalViscousTerminalSolution (Set.univ : Set (PDE.Vec n)) γ B b ε τ F u ↔
      IsClassicalViscousTerminalSolution (Set.univ : Set (PDE.Vec n)) γ' B b ε τ F u := by
  simp only [IsClassicalViscousTerminalSolution, evolutionPastClosedCylinder,
    evolutionPastInteriorRaw, evolutionPastOpenCylinder, evolutionTerminalClosure,
    evolutionLateralFrontier, movingDomain_univ]

/-- Over the whole space the closed moving slab does not depend on the curve. -/
theorem movingClosedSlab_univ_curve_congr {n : ℕ} (γ γ' : ℝ → PDE.Vec n) (a τ : ℝ) :
    movingClosedSlab (Set.univ : Set (PDE.Vec n)) γ a τ =
      movingClosedSlab (Set.univ : Set (PDE.Vec n)) γ' a τ := by
  simp only [movingClosedSlab, movingDomain_univ]

/-- **Two barriers** (companion paper, (A.1), `Ω = ℝⁿ`).  Whole-space terminal comparison on a
finite slab: `|u_ε - F| ≤ (τ - σ) M` wherever `|L_ε F| ≤ M` on the slab.  There is no lateral
clause. -/
theorem wholeSpace_terminalDatum_bound {n : ℕ} {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n}
    {lam Lam : ℝ} (hlam : 0 < lam) {B : FullKineticCoefficient n}
    (hB : HasEverywhereLoewnerBounds lam Lam B) {Lb : ℝ} {b : PDE.Vec n → PDE.Vec n}
    (hb : HasEuclideanLipschitzDrift Lb b)
    (hwhole : Ω = Set.univ) (a τ : ℝ) (haτ : a < τ)
    (F : BoundedBorel (EvolutionAmbientState n))
    (hF : IsSmoothCompactTerminalDatum Ω γ τ F)
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ p ∈ movingClosedSlab Ω γ a τ,
      |viscousTransportedOperator B b ε
        (fun q => F (q.position, q.velocity)) p| ≤ M)
    (u : KineticPoint n → ℝ)
    (hu : IsClassicalViscousTerminalSolution Ω γ B b ε τ F u) :
    ∀ p ∈ movingClosedSlab Ω γ a τ,
      |u p - F (p.position, p.velocity)| ≤ (τ - p.time) * M := by
  subst hwhole
  obtain ⟨FB, -, hFB⟩ := F.exists_bound
  have hu0 := (isClassicalViscousTerminalSolution_univ_curve_congr γ (fun _ => 0) B b ε τ F u).mp hu
  have hS := movingClosedSlab_univ_curve_congr (n := n) γ (fun _ => 0) a τ
  have hfr : ∀ q : KineticPoint n,
      q.position ∉ frontier (movingDomain (Set.univ : Set (PDE.Vec n)) (fun _ => 0) q.time) := by
    intro q
    rw [movingDomain_univ, frontier_univ]
    exact notMem_empty _
  rw [hS]
  exact classical_sub_terminalDatum_le_core_of_slab isOpen_univ continuous_const hlam hB hb hε
    hε1 hF.1 hFB (a := a) (by rw [hS] at hM; exact hM) hu0 (fun q _ hq => absurd hq (hfr q))

end HypoellipticAleksandrov.KineticAleksandrov
