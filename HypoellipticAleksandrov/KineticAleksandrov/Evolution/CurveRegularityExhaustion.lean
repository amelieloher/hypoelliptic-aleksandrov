module

import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Linarith
public import HypoellipticAleksandrov.KineticAleksandrov.EvolutionProblem
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonMoving

/-!
# Approximating moving balls for the regularised-curve construction

In the construction of Proposition 2.1 (for `Ω = B_{r₀}(c)`), the moving ball `γ + B_{r₀}(c)` is
exhausted by the balls `γ_k + B_{r₀ - α_k}(c)` with smooth curves `γ_k`, where
`α_{k+1} ≤ α_k / 4` and `‖γ_k - γ‖_∞ ≤ α_k / 2`.  This file proves the elementary geometric
facts: the balls lie inside `Ω_σ`, are nested, and exhaust `Ω_σ`.
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov

open Set Filter
open scoped Topology

/-- Membership in the moving ball `γ(σ) + B_R(c)`. -/
theorem mem_movingDomain_euclideanBall_iff_norm_lt {n : ℕ} {c : PDE.Vec n} {R : ℝ}
    (hR : 0 < R) {γ : ℝ → PDE.Vec n} {σ : ℝ} {y : PDE.Vec n} :
    y ∈ movingDomain (PDE.euclideanBall c R) γ σ ↔
      PDE.vecEuclideanNorm (y - (γ σ + c)) < R := by
  rw [mem_movingDomain_iff, PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hR, sub_sub]

/-- Perturbing the centre curve by at most `ε` moves the distance to the centre by at most `ε`. -/
theorem vecEuclideanNorm_sub_add_le {n : ℕ} {c : PDE.Vec n} {γ γ' : ℝ → PDE.Vec n} {σ ε : ℝ}
    (h : PDE.vecEuclideanNorm (γ' σ - γ σ) ≤ ε) (y : PDE.Vec n) :
    PDE.vecEuclideanNorm (y - (γ' σ + c)) ≤ PDE.vecEuclideanNorm (y - (γ σ + c)) + ε := by
  have h1 : y - (γ' σ + c) = (y - (γ σ + c)) + (γ σ - γ' σ) := by abel
  have h2 : PDE.vecEuclideanNorm (γ σ - γ' σ) ≤ ε := by
    rw [PDE.vecEuclideanNorm_sub_comm]
    exact h
  rw [h1]
  exact (PDE.vecEuclideanNorm_add_le _ _).trans (by linarith)

/-- A ball around a curve uniformly `ε`-close to `γ` lies in the larger ball of radius
`r + ε` around `γ`. -/
theorem movingDomain_euclideanBall_subset_of_close {n : ℕ} {c : PDE.Vec n} {r r' ε : ℝ}
    (hr : 0 < r) (hrr : r + ε ≤ r') {γ γ' : ℝ → PDE.Vec n}
    (hγ : ∀ σ, PDE.vecEuclideanNorm (γ' σ - γ σ) ≤ ε) (σ : ℝ) :
    movingDomain (PDE.euclideanBall c r) γ' σ ⊆ movingDomain (PDE.euclideanBall c r') γ σ := by
  intro y hy
  have hε : 0 ≤ ε := (PDE.vecEuclideanNorm_nonneg _).trans (hγ σ)
  rw [mem_movingDomain_euclideanBall_iff_norm_lt hr] at hy
  rw [mem_movingDomain_euclideanBall_iff_norm_lt (by linarith)]
  have h := vecEuclideanNorm_sub_add_le (c := c) (hγ σ) y
  have h' : PDE.vecEuclideanNorm (y - (γ σ + c)) ≤ PDE.vecEuclideanNorm (y - (γ' σ + c)) + ε := by
    have h1 : y - (γ σ + c) = (y - (γ' σ + c)) + (γ' σ - γ σ) := by abel
    rw [h1]
    exact (PDE.vecEuclideanNorm_add_le _ _).trans (by linarith [hγ σ])
  linarith

/-- The approximating moving ball `γ_k + B_{r₀ - α_k}(c)` lies inside `Ω_σ = γ + B_{r₀}(c)`
when `‖γ_k - γ‖ ≤ α_k / 2`. -/
theorem movingDomain_approx_subset {n : ℕ} {c : PDE.Vec n} {r₀ α : ℝ} (hα : α < r₀)
    {γ γ' : ℝ → PDE.Vec n} (hγ : ∀ σ, PDE.vecEuclideanNorm (γ' σ - γ σ) ≤ α / 2)
    (hα0 : 0 ≤ α) (σ : ℝ) :
    movingDomain (PDE.euclideanBall c (r₀ - α)) γ' σ ⊆
      movingDomain (PDE.euclideanBall c r₀) γ σ :=
  movingDomain_euclideanBall_subset_of_close (by linarith) (by linarith) hγ σ

/-- Consecutive approximating balls are nested: if `‖γ_k - γ‖ ≤ α_k / 2`,
`‖γ_{k+1} - γ‖ ≤ α_{k+1} / 2` and `α_{k+1} ≤ α_k / 4`, then
`γ_k + B_{r₀ - α_k}(c) ⊆ γ_{k+1} + B_{r₀ - α_{k+1}}(c)`. -/
theorem movingDomain_approx_mono {n : ℕ} {c : PDE.Vec n} {r₀ α α' : ℝ} (hα : α < r₀)
    (hα'0 : 0 ≤ α') (hαα : α' ≤ α / 4) {γ γ₁ γ₂ : ℝ → PDE.Vec n}
    (h₁ : ∀ σ, PDE.vecEuclideanNorm (γ₁ σ - γ σ) ≤ α / 2)
    (h₂ : ∀ σ, PDE.vecEuclideanNorm (γ₂ σ - γ σ) ≤ α' / 2) (σ : ℝ) :
    movingDomain (PDE.euclideanBall c (r₀ - α)) γ₁ σ ⊆
      movingDomain (PDE.euclideanBall c (r₀ - α')) γ₂ σ := by
  have hd : ∀ s, PDE.vecEuclideanNorm (γ₁ s - γ₂ s) ≤ α / 2 + α' / 2 := by
    intro s
    have h1 : γ₁ s - γ₂ s = (γ₁ s - γ s) + (γ s - γ₂ s) := by abel
    have h2 : PDE.vecEuclideanNorm (γ s - γ₂ s) ≤ α' / 2 := by
      rw [PDE.vecEuclideanNorm_sub_comm]
      exact h₂ s
    rw [h1]
    exact (PDE.vecEuclideanNorm_add_le _ _).trans (add_le_add (h₁ s) h2)
  have hα0 : 0 ≤ α := by
    have := (PDE.vecEuclideanNorm_nonneg (γ₁ σ - γ σ)).trans (h₁ σ)
    linarith
  exact movingDomain_euclideanBall_subset_of_close (by linarith) (by linarith) hd σ

/-- Every point of `Ω_σ = γ + B_{r₀}(c)` lies in all the approximating balls
`γ_k + B_{r₀ - α_k}(c)` from some index on, when `α_k → 0` and
`‖γ_k - γ‖ ≤ α_k / 2`. -/
theorem eventually_mem_movingDomain_approx {n : ℕ} {c : PDE.Vec n} {r₀ : ℝ}
    (hr₀ : 0 < r₀) {α : ℕ → ℝ} (hαlim : Tendsto α atTop (𝓝 0))
    {γ : ℝ → PDE.Vec n} {γs : ℕ → ℝ → PDE.Vec n}
    (hγ : ∀ k σ, PDE.vecEuclideanNorm (γs k σ - γ σ) ≤ α k / 2) {σ : ℝ} {y : PDE.Vec n}
    (hy : y ∈ movingDomain (PDE.euclideanBall c r₀) γ σ) :
    ∀ᶠ k in atTop, y ∈ movingDomain (PDE.euclideanBall c (r₀ - α k)) (γs k) σ := by
  rw [mem_movingDomain_euclideanBall_iff_norm_lt hr₀] at hy
  have hδ : 0 < (r₀ - PDE.vecEuclideanNorm (y - (γ σ + c))) / 2 := by linarith
  have hsmall := (hαlim.eventually (gt_mem_nhds hδ))
  filter_upwards [hsmall] with k hk
  have hrk : 0 < r₀ - α k := by
    have := PDE.vecEuclideanNorm_nonneg (y - (γ σ + c))
    linarith
  rw [mem_movingDomain_euclideanBall_iff_norm_lt hrk]
  have h := vecEuclideanNorm_sub_add_le (c := c) (hγ k σ) y
  linarith

/-- The approximating moving balls exhaust `Ω_σ`. -/
theorem iUnion_movingDomain_approx {n : ℕ} {c : PDE.Vec n} {r₀ : ℝ}
    {α : ℕ → ℝ} (hαpos : ∀ k, 0 < α k) (hαr : ∀ k, α k < r₀)
    (hαlim : Tendsto α atTop (𝓝 0)) {γ : ℝ → PDE.Vec n} {γs : ℕ → ℝ → PDE.Vec n}
    (hγ : ∀ k σ, PDE.vecEuclideanNorm (γs k σ - γ σ) ≤ α k / 2) (σ : ℝ) :
    (⋃ k, movingDomain (PDE.euclideanBall c (r₀ - α k)) (γs k) σ) =
      movingDomain (PDE.euclideanBall c r₀) γ σ := by
  refine Subset.antisymm (iUnion_subset fun k => ?_) fun y hy => ?_
  · exact movingDomain_approx_subset (hαr k) (hγ k) (hαpos k).le σ
  · have hr₀ : 0 < r₀ := lt_trans (hαpos 0) (hαr 0)
    obtain ⟨k, hk⟩ := (eventually_mem_movingDomain_approx hr₀ hαlim hγ hy).exists
    exact mem_iUnion.mpr ⟨k, hk⟩

end HypoellipticAleksandrov.KineticAleksandrov
