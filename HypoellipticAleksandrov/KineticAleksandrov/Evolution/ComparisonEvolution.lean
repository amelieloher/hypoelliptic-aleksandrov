module

import Mathlib.Tactic.Linarith
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonPrinciple
public import HypoellipticAleksandrov.KineticAleksandrov.EvolutionProblem

/-!
# Comparison for the viscous terminal problem

Statements for the comparison clauses of Proposition 2.1 and
Proposition 2.1 in the carriers of `EvolutionProblem`.  The viscous
terminal-solution predicate is the one of `IsClassicalTerminalSolution` with `L_ε`
in place of `L`; at `ε = 0` they coincide.

The comparison is carried out in absolute coordinates `(σ, y, z)` on the moving
cylinder `{y ∈ γ(σ) + Ω}`.  This is equivalent to the straightened formulation of the
source (`Y = y - γ(σ)` adds the drift `-γ'(σ) · ∇_Y`) but needs neither piecewise
regularity of `γ` nor any derivative of it: only continuity of `γ` enters.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Filter Set Matrix
open scoped Topology MatrixOrder

/-- Subtraction for the viscous operator at a slice-regular point. -/
theorem viscousTransportedOperator_sub {n : ℕ} {B : FullKineticCoefficient n}
    {b : PDE.Vec n → PDE.Vec n} {ε : ℝ} {u v : KineticPoint n → ℝ} {p : KineticPoint n}
    (hu : IsSliceRegularAt u p) (hv : IsSliceRegularAt v p) :
    viscousTransportedOperator B b ε (fun q => u q - v q) p =
      viscousTransportedOperator B b ε u p - viscousTransportedOperator B b ε v p := by
  have h : (fun q : KineticPoint n => u q - v q) = fun q => u q + (-1) * v q := by
    funext q
    ring
  rw [h, viscousTransportedOperator_add hu (hv.const_mul (-1)),
    viscousTransportedOperator_const_mul (-1) hv]
  ring

/-- A matrix coefficient with a positive lower Loewner bound is positive semidefinite. -/
theorem posSemidef_of_hasEverywhereLoewnerBounds {n : ℕ} {lam Lam : ℝ} (hlam : 0 ≤ lam)
    {B : FullKineticCoefficient n} (hB : HasEverywhereLoewnerBounds lam Lam B)
    (σ : ℝ) (y z : PDE.Vec n) : (B σ y z).PosSemidef := by
  have h0 : (0 : PDE.Mat n) ≤ lam • (1 : PDE.Mat n) := by
    rw [Matrix.nonneg_iff_posSemidef]
    exact Matrix.PosSemidef.one.smul hlam
  exact Matrix.nonneg_iff_posSemidef.mp (h0.trans (hB σ y z).1)

/-- The viscous classical terminal-solution predicate: `IsClassicalTerminalSolution` with
`L_ε = L + ε Δ_z` in the equation. -/
def IsClassicalViscousTerminalSolution {n : ℕ}
    (Ω : Set (PDE.Vec n)) (γ : ℝ → PDE.Vec n)
    (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n) (ε : ℝ)
    (τ : ℝ) (F : BoundedBorel (EvolutionAmbientState n))
    (u : KineticPoint n → ℝ) : Prop :=
  (∃ C : ℝ, 0 ≤ C ∧
      ∀ p ∈ evolutionPastClosedCylinder Ω γ τ, abs (u p) ≤ C) ∧
    ContinuousOn u (evolutionPastClosedCylinder Ω γ τ) ∧
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q => u ⟨q.1, q.2.1, q.2.2⟩)
      (evolutionPastInteriorRaw Ω γ τ) ∧
    (∀ p ∈ evolutionPastOpenCylinder Ω γ τ,
      viscousTransportedOperator B b ε u p = 0) ∧
    (∀ p ∈ evolutionTerminalClosure Ω γ τ,
      u p = F (p.position, p.velocity)) ∧
    (∀ p ∈ evolutionLateralFrontier Ω γ τ, u p = 0)

/-- At `ε = 0` the viscous predicate is `IsClassicalTerminalSolution`. -/
theorem isClassicalViscousTerminalSolution_zero_iff {n : ℕ}
    (Ω : Set (PDE.Vec n)) (γ : ℝ → PDE.Vec n)
    (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n)
    (τ : ℝ) (F : BoundedBorel (EvolutionAmbientState n)) (u : KineticPoint n → ℝ) :
    IsClassicalViscousTerminalSolution Ω γ B b 0 τ F u ↔
      IsClassicalTerminalSolution Ω γ B b τ F u := by
  unfold IsClassicalViscousTerminalSolution IsClassicalTerminalSolution
  simp only [viscousTransportedOperator_zero]

/-- The raw interior of the past moving cylinder is open. -/
theorem isOpen_evolutionPastInteriorRaw {n : ℕ} {Ω : Set (PDE.Vec n)} (hΩ : IsOpen Ω)
    {γ : ℝ → PDE.Vec n} (hγ : Continuous γ) (τ : ℝ) :
    IsOpen (evolutionPastInteriorRaw Ω γ τ) := by
  have h1 : IsOpen {q : ℝ × (PDE.Vec n × PDE.Vec n) | q.1 < τ} :=
    isOpen_lt continuous_fst continuous_const
  have hc : Continuous (fun q : ℝ × (PDE.Vec n × PDE.Vec n) => q.2.1 - γ q.1) :=
    (continuous_fst.comp continuous_snd).sub (hγ.comp continuous_fst)
  have h2 := hΩ.preimage hc
  have := h1.inter h2
  convert this using 1
  ext q
  simp only [evolutionPastInteriorRaw, mem_inter_iff, Set.mem_ofPred_eq, mem_preimage,
    mem_movingDomain_iff]

/-- A viscous classical solution is slice regular at every point of the open cylinder. -/
theorem IsClassicalViscousTerminalSolution.isSliceRegularAt {n : ℕ} {Ω : Set (PDE.Vec n)}
    (hΩ : IsOpen Ω) {γ : ℝ → PDE.Vec n} (hγ : Continuous γ)
    {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n} {ε τ : ℝ}
    {F : BoundedBorel (EvolutionAmbientState n)} {u : KineticPoint n → ℝ}
    (hu : IsClassicalViscousTerminalSolution Ω γ B b ε τ F u)
    {p : KineticPoint n} (hp : p ∈ evolutionPastOpenCylinder Ω γ τ) :
    IsSliceRegularAt u p := by
  apply IsSliceRegularAt.of_contDiffAt
  have hmem : (p.time, p.position, p.velocity) ∈ evolutionPastInteriorRaw Ω γ τ := hp
  have hnhds := (isOpen_evolutionPastInteriorRaw hΩ hγ τ).mem_nhds hmem
  exact (hu.2.2.1.contDiffAt hnhds).of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))

end HypoellipticAleksandrov.KineticAleksandrov
