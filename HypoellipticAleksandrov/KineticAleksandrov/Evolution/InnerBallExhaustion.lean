module

import Mathlib.Analysis.SpecificLimits.Basic
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.CurveMollification
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.CurveRegularityExhaustion

/-!
# Nested smooth inner balls

Nested curve approximation for the regularized truncations in the proof of the companion
paper, Proposition 2.1.  For a continuous piecewise `C¹` curve `γ` and a finite window `[a, τ]` we
construct smooth curves `g k`, all globally `L`-Lipschitz, with radii `α k = r / 2 · 4⁻ᵏ`, such
that `‖g k - γ‖ ≤ α k / 2` on the window, the balls `B(g k s, r - α k)` are nested and exhaust
`B(γ s, r)`.  The ball geometry reuses `CurveRegularityExhaustion`, applied to constant curves.
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov

open Set Filter
open scoped Topology

/-- A Euclidean ball is the moving ball of the constant curve with that centre. -/
theorem euclideanBall_eq_movingDomain_const {n : ℕ} (x : PDE.Vec n) {R : ℝ} (hR : 0 < R) :
    PDE.euclideanBall x R =
      movingDomain (PDE.euclideanBall (0 : PDE.Vec n) R) (fun _ : ℝ => x) 0 := by
  ext y
  rw [mem_movingDomain_euclideanBall_iff_norm_lt hR,
    PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hR, add_zero]

/-- The geometric radii `α k = r / 2 · (1/4)ᵏ`. -/
noncomputable def innerBallRadius (r : ℝ) (k : ℕ) : ℝ := r / 2 * (1 / 4) ^ k

theorem innerBallRadius_pos {r : ℝ} (hr : 0 < r) (k : ℕ) : 0 < innerBallRadius r k := by
  unfold innerBallRadius; positivity

theorem innerBallRadius_lt {r : ℝ} (hr : 0 < r) (k : ℕ) : innerBallRadius r k < r := by
  unfold innerBallRadius
  have : (1 / 4 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  nlinarith

theorem innerBallRadius_succ (r : ℝ) (k : ℕ) :
    innerBallRadius r (k + 1) = innerBallRadius r k / 4 := by
  unfold innerBallRadius; rw [pow_succ]; ring

theorem tendsto_innerBallRadius (r : ℝ) : Tendsto (innerBallRadius r) atTop (𝓝 0) := by
  have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 4 : ℝ)) (by norm_num)
    (by norm_num)).const_mul (r / 2)
  rw [mul_zero] at this
  exact this

/-- Nested curve approximation for the regularized truncations. -/
theorem exists_nested_smooth_inner_balls
    {n : ℕ} {γ : ℝ → PDE.Vec n} (hγ : IsContinuousPiecewiseC1 γ)
    (a τ r : ℝ) (haτ : a < τ) (hr : 0 < r) :
    ∃ (α : ℕ → ℝ) (g : ℕ → ℝ → PDE.Vec n) (L : ℝ),
      0 ≤ L ∧ (∀ k, 0 < α k ∧ α k < r) ∧
      (∀ k, α (k + 1) ≤ α k / 4) ∧ Tendsto α atTop (nhds 0) ∧
      (∀ k, ContDiff ℝ (⊤ : ℕ∞) (g k)) ∧
      (∀ k s, s ∈ Icc a τ →
        PDE.vecEuclideanNorm (g k s - γ s) ≤ α k / 2) ∧
      (∀ k s t, PDE.vecEuclideanNorm (g k s - g k t) ≤ L * |s - t|) ∧
      (∀ k s, s ∈ Icc a τ →
        PDE.euclideanBall (g k s) (r - α k) ⊆
          PDE.euclideanBall (g (k + 1) s) (r - α (k + 1))) ∧
      (∀ s ∈ Icc a τ,
        (⋃ k, PDE.euclideanBall (g k s) (r - α k)) =
          PDE.euclideanBall (γ s) r) := by
  obtain ⟨L, hL0, hL⟩ := exists_evolution_curve_lipschitzOn hγ a τ haτ
  have hext := slabExtension_lipschitz haτ.le hL0 hL
  have hcont := continuous_slabExtension hγ.1 a τ
  have hα := innerBallRadius_pos hr
  have hex : ∀ k, ∃ g : ℝ → PDE.Vec n, ContDiff ℝ (⊤ : ℕ∞) g ∧
      (∀ s t, PDE.vecEuclideanNorm (g s - g t) ≤ L * |s - t|) ∧
      ∀ s, PDE.vecEuclideanNorm (g s - slabExtension γ a τ s) ≤ innerBallRadius r k / 2 :=
    fun k => exists_smooth_lipschitz_approx hcont hL0 hext (half_pos (hα k))
  choose g hg hgL hgε using hex
  have hclose : ∀ k s, s ∈ Icc a τ →
      PDE.vecEuclideanNorm (g k s - γ s) ≤ innerBallRadius r k / 2 := by
    intro k s hs
    simpa [slabExtension_eq γ hs] using hgε k s
  refine ⟨innerBallRadius r, g, L, hL0, fun k => ⟨hα k, innerBallRadius_lt hr k⟩,
    fun k => (innerBallRadius_succ r k).le, tendsto_innerBallRadius r, hg, hclose, hgL,
    fun k s hs => ?_, fun s hs => ?_⟩
  · have hk : 0 < r - innerBallRadius r k := by linarith [innerBallRadius_lt hr k]
    have hk' : 0 < r - innerBallRadius r (k + 1) := by
      linarith [innerBallRadius_lt hr (k + 1)]
    rw [euclideanBall_eq_movingDomain_const _ hk, euclideanBall_eq_movingDomain_const _ hk']
    exact movingDomain_approx_mono (innerBallRadius_lt hr k) (hα (k + 1)).le
      (innerBallRadius_succ r k).le (γ := fun _ => γ s) (γ₁ := fun _ => g k s)
      (γ₂ := fun _ => g (k + 1) s) (fun _ => hclose k s hs) (fun _ => hclose (k + 1) s hs) 0
  · have hk : ∀ k, 0 < r - innerBallRadius r k := fun k => by
      linarith [innerBallRadius_lt hr k]
    have := iUnion_movingDomain_approx (c := (0 : PDE.Vec n)) (r₀ := r) (hα) (innerBallRadius_lt hr)
      (tendsto_innerBallRadius r) (γ := fun _ => γ s) (γs := fun k _ => g k s)
      (fun k _ => hclose k s hs) 0
    rw [euclideanBall_eq_movingDomain_const (γ s) hr]
    rw [← this]
    refine iUnion_congr fun k => ?_
    exact euclideanBall_eq_movingDomain_const _ (hk k)

end HypoellipticAleksandrov.KineticAleksandrov
