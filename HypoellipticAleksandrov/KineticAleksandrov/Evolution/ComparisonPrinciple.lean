module

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonGrowth

/-!
# Comparison with the growth barrier

The abstract form of Proposition 2.1: on a closed region of kinetic
points with bounded times, a function bounded above, continuous, slice regular on the
active part and a subsolution of `L_ε` there, is `≤ 0` as soon as it is `≤ 0` on the rest of
the region.  The proof compares `u - δ Φ` on bounded truncations and lets `δ ↓ 0`, using
the Lyapunov inequality `L_ε Φ ≤ -Φ`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Filter Set Matrix
open scoped Topology MatrixOrder

/-- Continuity of the growth barrier. -/
theorem continuous_growthBarrier {n : ℕ} (C T : ℝ) : Continuous (growthBarrier (n := n) C T) := by
  unfold growthBarrier
  have := @continuous_radialSq n
  have h2 := @continuous_time n
  fun_prop

/-- Growth comparison on a closed region, for bounded-above functions. -/
theorem le_zero_of_viscous_nonneg_growth {n : ℕ} {B : FullKineticCoefficient n}
    {b : PDE.Vec n → PDE.Vec n} {ε Lam Lb : ℝ} {K D : Set (KineticPoint n)}
    {u : KineticPoint n → ℝ} {a T : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hBLam : ∀ σ y z, B σ y z ≤ Lam • (1 : PDE.Mat n))
    (hb : ∀ y y', PDE.vecEuclideanNorm (b y - b y') ≤ Lb * PDE.vecEuclideanNorm (y - y'))
    (hK : IsClosed K) (hKt : ∀ p ∈ K, a ≤ p.time ∧ p.time ≤ T)
    (hfut : ∀ p ∈ D, ∀ᶠ q in 𝓝 p, p.time ≤ q.time → q ∈ K)
    (hcont : ContinuousOn u K) (hbdd : ∃ M, ∀ p ∈ K, u p ≤ M)
    (hreg : ∀ p ∈ D, IsSliceRegularAt u p)
    (hB : ∀ p ∈ D, (B p.time p.position p.velocity).PosSemidef)
    (hsub : ∀ p ∈ D, 0 ≤ viscousTransportedOperator B b ε u p)
    (hbdry : ∀ p ∈ K, p ∉ D → u p ≤ 0) :
    ∀ p ∈ K, u p ≤ 0 := by
  obtain ⟨M, hM⟩ := hbdd
  obtain ⟨C, hC⟩ : ∃ C, C = growthConstant n Lam (PDE.vecEuclideanNorm (b 0)) Lb := ⟨_, rfl⟩
  have hCpos : 0 ≤ C := by
    rw [hC]
    unfold growthConstant
    have : 0 ≤ PDE.vecEuclideanNorm (b 0) := PDE.vecEuclideanNorm_nonneg _
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    positivity
  have hΦ : ∀ p : KineticPoint n, viscousTransportedOperator B b ε (growthBarrier C T) p ≤
      -growthBarrier C T p := by
    intro p
    rw [hC]
    exact viscousTransportedOperator_growthBarrier_le hε1 hBLam hb T p
  have hR2nn : ∀ (δ : ℝ) (p₀ : KineticPoint n),
      0 ≤ max (max M 0 / δ) (radialSq p₀) := fun δ p₀ =>
    le_trans (add_nonneg (PDE.vecNormSq_nonneg _) (PDE.vecNormSq_nonneg _)) (le_max_right _ _)
  have key : ∀ δ : ℝ, 0 < δ → ∀ p₀ ∈ K, u p₀ ≤ δ * growthBarrier C T p₀ := by
    intro δ hδ p₀ hp₀
    obtain ⟨R2, hR2⟩ : ∃ R2, R2 = max (max M 0 / δ) (radialSq p₀) := ⟨_, rfl⟩
    have hR2nn' : 0 ≤ R2 := hR2 ▸ hR2nn δ p₀
    obtain ⟨R, hR⟩ : ∃ R, R = Real.sqrt R2 := ⟨_, rfl⟩
    have hRsq : R ^ 2 = R2 := by rw [hR]; exact Real.sq_sqrt hR2nn'
    have hMR : max M 0 ≤ δ * R2 := by
      have : max M 0 / δ ≤ R2 := hR2 ▸ le_max_left _ _
      rw [div_le_iff₀ hδ] at this
      linarith
    have hp₀R : radialSq p₀ ≤ R ^ 2 := by rw [hRsq, hR2]; exact le_max_right _ _
    have hKR : IsCompact (K ∩ {p | radialSq p ≤ R ^ 2}) := isCompact_inter_radialSq hK hKt R
    have hw := le_zero_of_strict_viscous_compact (B := B) (b := b) (ε := ε)
      (K := K ∩ {p | radialSq p ≤ R ^ 2}) (D := D ∩ {p | radialSq p < R ^ 2})
      (w := fun q => u q + (-δ) * growthBarrier C T q) hε0 hKR ?_ ?_ ?_ ?_ ?_ ?_
    · have : u p₀ + (-δ) * growthBarrier C T p₀ ≤ 0 := hw p₀ ⟨hp₀, hp₀R⟩
      linarith
    · exact (hcont.mono inter_subset_left).add
        ((continuous_const.mul (continuous_growthBarrier C T)).continuousOn)
    · intro p hp
      have h1 := hfut p hp.1
      have h2 : ∀ᶠ q in 𝓝 p, radialSq q < R ^ 2 :=
        (isOpen_lt continuous_radialSq continuous_const).mem_nhds hp.2
      filter_upwards [h1, h2] with q hq1 hq2 hqt
      exact ⟨hq1 hqt, hq2.le⟩
    · intro p hp
      exact (hreg p hp.1).add ((isSliceRegularAt_growthBarrier C T p).const_mul (-δ))
    · intro p hp
      exact hB p hp.1
    · intro p hp
      rw [viscousTransportedOperator_add (hreg p hp.1)
        ((isSliceRegularAt_growthBarrier C T p).const_mul (-δ)),
        viscousTransportedOperator_const_mul (-δ) (isSliceRegularAt_growthBarrier C T p)]
      have h1 := hsub p hp.1
      have h2 := hΦ p
      have h3 := growthBarrier_pos C T p
      nlinarith
    · intro p hp hnot
      by_cases hpD : p ∈ D
      · have hrad : ¬ radialSq p < R ^ 2 := fun h => hnot ⟨hpD, h⟩
        have heq : R ^ 2 ≤ radialSq p := not_lt.mp hrad
        have hΦge := one_add_radialSq_le_growthBarrier hCpos (hKt p hp.1).2
        have hu := hM p hp.1
        have h1 : δ * (1 + radialSq p) ≤ δ * growthBarrier C T p :=
          mul_le_mul_of_nonneg_left hΦge hδ.le
        have h2 : δ * R ^ 2 ≤ δ * radialSq p := mul_le_mul_of_nonneg_left heq hδ.le
        have h3 := le_max_left M 0
        show u p + (-δ) * growthBarrier C T p ≤ 0
        rw [hRsq] at h2
        nlinarith
      · have h1 := hbdry p hp.1 hpD
        have h3 := growthBarrier_pos C T p
        show u p + (-δ) * growthBarrier C T p ≤ 0
        nlinarith
  intro p₀ hp₀
  by_contra hneg'
  have hneg := not_le.mp hneg'
  have hΦpos := growthBarrier_pos C T p₀
  have hδ : 0 < u p₀ / (2 * growthBarrier C T p₀) := by positivity
  have h := key _ hδ p₀ hp₀
  have : u p₀ / (2 * growthBarrier C T p₀) * growthBarrier C T p₀ = u p₀ / 2 := by
    field_simp
  rw [this] at h
  linarith

end HypoellipticAleksandrov.KineticAleksandrov
