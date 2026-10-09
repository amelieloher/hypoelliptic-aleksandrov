module

import Mathlib.Tactic.Linarith
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonEvolution

/-!
# Comparison lemmas for Proposition 2.1

* `bounded_comparison` realises Proposition 2.1: the maximum principle for
  `L_ε` (`0 ≤ ε`, including `ε = 0`) on bounded truncations of the moving cylinder.
* `exists_growthConstant` and `growth_comparison` realise Proposition 2.1:
  the Lyapunov function `Φ = exp (C (T - σ)) (1 + |y|² + |z|²)` with `L_ε Φ ≤ -Φ` for all
  `0 ≤ ε ≤ 1`, and comparison for functions that are bounded on the full moving cylinder.
* `classical_comparison` and `classical_unique` apply the growth comparison to viscous
  classical terminal solutions.

All statements are in absolute coordinates; see `ComparisonEvolution` for the relation to
the straightened formulation.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Filter Set Matrix
open scoped Topology MatrixOrder

/-- Proposition 2.1.  Maximum principle for `L_ε`, `ε ≥ 0`, on the bounded
truncation `{a ≤ σ ≤ T, y ∈ closure (γ(σ) + Ω), |y|² + |z|² ≤ R²}` of the moving cylinder:
a subsolution that is nonpositive on the terminal face, the lateral frontier and the
artificial boundary `|y|² + |z|² = R²` is nonpositive. -/
theorem bounded_comparison {n : ℕ} {Ω : Set (PDE.Vec n)} (hΩ : IsOpen Ω)
    {γ : ℝ → PDE.Vec n} (hγ : Continuous γ) {lam Lam : ℝ} (hlam : 0 < lam)
    {B : FullKineticCoefficient n} (hB : HasEverywhereLoewnerBounds lam Lam B)
    {b : PDE.Vec n → PDE.Vec n} {ε : ℝ} (hε : 0 ≤ ε) {a T R : ℝ} {u : KineticPoint n → ℝ}
    (hcont : ContinuousOn u (movingClosedSlab Ω γ a T ∩ {p | radialSq p ≤ R ^ 2}))
    (hreg : ∀ p ∈ movingActiveSlab Ω γ a T ∩ {p | radialSq p < R ^ 2}, IsSliceRegularAt u p)
    (hsub : ∀ p ∈ movingActiveSlab Ω γ a T ∩ {p | radialSq p < R ^ 2},
      0 ≤ viscousTransportedOperator B b ε u p)
    (hterm : ∀ p ∈ movingClosedSlab Ω γ a T ∩ {p | radialSq p ≤ R ^ 2}, p.time = T → u p ≤ 0)
    (hlat : ∀ p ∈ movingClosedSlab Ω γ a T ∩ {p | radialSq p ≤ R ^ 2},
      p.position ∈ frontier (movingDomain Ω γ p.time) → u p ≤ 0)
    (hart : ∀ p ∈ movingClosedSlab Ω γ a T ∩ {p | radialSq p ≤ R ^ 2},
      radialSq p = R ^ 2 → u p ≤ 0) :
    ∀ p ∈ movingClosedSlab Ω γ a T ∩ {p | radialSq p ≤ R ^ 2}, u p ≤ 0 := by
  refine le_zero_of_viscous_nonneg_compact (B := B) (b := b) (ε := ε)
    (K := movingClosedSlab Ω γ a T ∩ {p | radialSq p ≤ R ^ 2})
    (D := movingActiveSlab Ω γ a T ∩ {p | radialSq p < R ^ 2}) (T := T) hε
    (isCompact_movingClosedSlab_inter hγ a T R) (fun p hp => hp.1.2.1) hcont
    (fun p hp => eventually_future_mem_truncated hΩ hγ hp) hreg
    (fun p _ => posSemidef_of_hasEverywhereLoewnerBounds hlam.le hB _ _ _) hsub ?_
  intro p hp hnot
  rcases mem_boundary_of_truncated hΩ hp hnot with h | h | h
  · exact hterm p hp h
  · exact hlat p hp h
  · exact hart p hp h

/-- Proposition 2.1, Lyapunov part.  With the explicit constant
`C = 2 d (|Λ| + 1) + |b 0| + |L_b| + 1`, which depends only on `d`, `Λ`, `b 0` and `L_b`,
the function `Φ = exp (C (T - σ)) (1 + |y|² + |z|²)` satisfies `L_ε Φ ≤ -Φ` for every
`0 ≤ ε ≤ 1` and every terminal time `T`. -/
theorem exists_growthConstant {n : ℕ} {Lam Lb : ℝ} {B : FullKineticCoefficient n}
    {b : PDE.Vec n → PDE.Vec n} (hLam : ∀ σ y z, B σ y z ≤ Lam • (1 : PDE.Mat n))
    (hb : HasEuclideanLipschitzDrift Lb b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ (T : ℝ) (p : KineticPoint n),
      viscousTransportedOperator B b ε (growthBarrier C T) p ≤ -growthBarrier C T p := by
  refine ⟨growthConstant n Lam (PDE.vecEuclideanNorm (b 0)) Lb, ?_, ?_⟩
  · unfold growthConstant
    have : 0 ≤ PDE.vecEuclideanNorm (b 0) := PDE.vecEuclideanNorm_nonneg _
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    positivity
  · intro ε _ hε1 T p
    exact viscousTransportedOperator_growthBarrier_le hε1 hLam hb T p

/-- Proposition 2.1, comparison part.  On the full moving cylinder
`{a ≤ σ ≤ T, y ∈ closure (γ(σ) + Ω)}` (all `z`), a function that is bounded (above),
continuous, slice regular and a subsolution of `L_ε` (`0 ≤ ε ≤ 1`) in the interior, and
nonpositive on the terminal face and the lateral frontier, is nonpositive. -/
theorem growth_comparison {n : ℕ} {Ω : Set (PDE.Vec n)} (hΩ : IsOpen Ω)
    {γ : ℝ → PDE.Vec n} (hγ : Continuous γ) {lam Lam : ℝ} (hlam : 0 < lam)
    {B : FullKineticCoefficient n} (hB : HasEverywhereLoewnerBounds lam Lam B)
    {Lb : ℝ} {b : PDE.Vec n → PDE.Vec n} (hb : HasEuclideanLipschitzDrift Lb b)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) {a T : ℝ} {u : KineticPoint n → ℝ}
    (hbdd : ∃ M, ∀ p ∈ movingClosedSlab Ω γ a T, u p ≤ M)
    (hcont : ContinuousOn u (movingClosedSlab Ω γ a T))
    (hreg : ∀ p ∈ movingActiveSlab Ω γ a T, IsSliceRegularAt u p)
    (hsub : ∀ p ∈ movingActiveSlab Ω γ a T, 0 ≤ viscousTransportedOperator B b ε u p)
    (hterm : ∀ p ∈ movingClosedSlab Ω γ a T, p.time = T → u p ≤ 0)
    (hlat : ∀ p ∈ movingClosedSlab Ω γ a T,
      p.position ∈ frontier (movingDomain Ω γ p.time) → u p ≤ 0) :
    ∀ p ∈ movingClosedSlab Ω γ a T, u p ≤ 0 := by
  refine le_zero_of_viscous_nonneg_growth (B := B) (b := b) (ε := ε) (Lam := Lam) (Lb := Lb)
    (K := movingClosedSlab Ω γ a T) (D := movingActiveSlab Ω γ a T) hε0 hε1
    (fun σ y z => (hB σ y z).2)
    hb (isClosed_movingClosedSlab hγ a T) (fun p hp => ⟨hp.1, hp.2.1⟩)
    (fun p hp => eventually_future_mem_movingClosedSlab hΩ hγ hp) hcont hbdd hreg
    (fun p _ => posSemidef_of_hasEverywhereLoewnerBounds hlam.le hB _ _ _) hsub ?_
  intro p hp hnot
  rcases mem_boundary_of_movingClosedSlab hΩ hp hnot with h | h
  · exact hterm p hp h
  · exact hlat p hp h

/-- Comparison of viscous classical terminal solutions: ordered terminal data give ordered
solutions on the whole past closed cylinder. -/
theorem classical_comparison {n : ℕ} {Ω : Set (PDE.Vec n)} (hΩ : IsOpen Ω)
    {γ : ℝ → PDE.Vec n} (hγ : Continuous γ) {lam Lam : ℝ} (hlam : 0 < lam)
    {B : FullKineticCoefficient n} (hB : HasEverywhereLoewnerBounds lam Lam B)
    {Lb : ℝ} {b : PDE.Vec n → PDE.Vec n} (hb : HasEuclideanLipschitzDrift Lb b)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) {τ : ℝ}
    {F₁ F₂ : BoundedBorel (EvolutionAmbientState n)} {u₁ u₂ : KineticPoint n → ℝ}
    (h₁ : IsClassicalViscousTerminalSolution Ω γ B b ε τ F₁ u₁)
    (h₂ : IsClassicalViscousTerminalSolution Ω γ B b ε τ F₂ u₂)
    (hF : ∀ y z, y ∈ closure (movingDomain Ω γ τ) → F₁ (y, z) ≤ F₂ (y, z)) :
    ∀ p ∈ evolutionPastClosedCylinder Ω γ τ, u₁ p ≤ u₂ p := by
  intro p₀ hp₀
  have hslab : ∀ a, movingClosedSlab Ω γ a τ ⊆ evolutionPastClosedCylinder Ω γ τ :=
    fun a p hp => ⟨hp.2.1, hp.2.2⟩
  have hact : ∀ a, movingActiveSlab Ω γ a τ ⊆ evolutionPastOpenCylinder Ω γ τ :=
    fun a p hp => ⟨hp.2.1, hp.2.2⟩
  obtain ⟨C₁, -, hC₁⟩ := h₁.1
  obtain ⟨C₂, -, hC₂⟩ := h₂.1
  have hp₀slab : p₀ ∈ movingClosedSlab Ω γ p₀.time τ := ⟨le_rfl, hp₀.1, hp₀.2⟩
  have hres := growth_comparison (a := p₀.time) (T := τ) (u := fun q => u₁ q - u₂ q) hΩ hγ hlam
    hB hb hε0 hε1 ?_ ?_ ?_ ?_ ?_ ?_ p₀ hp₀slab
  · linarith
  · refine ⟨C₁ + C₂, fun p hp => ?_⟩
    have h1 := hC₁ p (hslab _ hp)
    have h2 := hC₂ p (hslab _ hp)
    have := le_abs_self (u₁ p)
    have := neg_abs_le (u₂ p)
    linarith
  · exact (h₁.2.1.mono (hslab _)).sub (h₂.2.1.mono (hslab _))
  · intro p hp
    exact (h₁.isSliceRegularAt hΩ hγ (hact _ hp)).sub (h₂.isSliceRegularAt hΩ hγ (hact _ hp))
  · intro p hp
    have hr₁ := h₁.isSliceRegularAt hΩ hγ (hact _ hp)
    have hr₂ := h₂.isSliceRegularAt hΩ hγ (hact _ hp)
    rw [viscousTransportedOperator_sub hr₁ hr₂, h₁.2.2.2.1 p (hact _ hp),
      h₂.2.2.2.1 p (hact _ hp)]
    simp
  · intro p hp hpT
    have hterm : p ∈ evolutionTerminalClosure Ω γ τ := ⟨hpT, hpT ▸ hp.2.2⟩
    have := hF p.position p.velocity hterm.2
    have e1 := h₁.2.2.2.2.1 p hterm
    have e2 := h₂.2.2.2.2.1 p hterm
    show u₁ p - u₂ p ≤ 0
    linarith
  · intro p hp hfr
    have hlat : p ∈ evolutionLateralFrontier Ω γ τ := ⟨hp.2.1, hfr⟩
    show u₁ p - u₂ p ≤ 0
    rw [h₁.2.2.2.2.2 p hlat, h₂.2.2.2.2.2 p hlat]
    simp

/-- Uniqueness of viscous classical terminal solutions for equal terminal data. -/
theorem classical_unique {n : ℕ} {Ω : Set (PDE.Vec n)} (hΩ : IsOpen Ω)
    {γ : ℝ → PDE.Vec n} (hγ : Continuous γ) {lam Lam : ℝ} (hlam : 0 < lam)
    {B : FullKineticCoefficient n} (hB : HasEverywhereLoewnerBounds lam Lam B)
    {Lb : ℝ} {b : PDE.Vec n → PDE.Vec n} (hb : HasEuclideanLipschitzDrift Lb b)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) {τ : ℝ}
    {F : BoundedBorel (EvolutionAmbientState n)} {u₁ u₂ : KineticPoint n → ℝ}
    (h₁ : IsClassicalViscousTerminalSolution Ω γ B b ε τ F u₁)
    (h₂ : IsClassicalViscousTerminalSolution Ω γ B b ε τ F u₂) :
    ∀ p ∈ evolutionPastClosedCylinder Ω γ τ, u₁ p = u₂ p := by
  intro p hp
  exact le_antisymm
    (classical_comparison hΩ hγ hlam hB hb hε0 hε1 h₁ h₂ (fun _ _ _ => le_rfl) p hp)
    (classical_comparison hΩ hγ hlam hB hb hε0 hε1 h₂ h₁ (fun _ _ _ => le_rfl) p hp)

end HypoellipticAleksandrov.KineticAleksandrov
