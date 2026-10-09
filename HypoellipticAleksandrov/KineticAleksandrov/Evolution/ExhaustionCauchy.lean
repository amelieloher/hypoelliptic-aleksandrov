module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionCauchyComparison
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionCauchyRadius

/-!
# The source Cauchy bound with inner-ball approximation errors

The source condition 3A/2 < delta gives a common strict diffused-radius gap.
A single transported threshold then works for both actual finite Dirichlet solutions.
The bound is proved, not assumed; the support and containment conditions of the
comparison core are discharged from the inner-ball approximation data.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set
open scoped MatrixOrder

/-- The manuscript Cauchy estimate for actual inner-ball ellipsoid approximants, with
constant independent of both approximation indices and transported truncation radii. -/
theorem exists_transportedRadius_dirichlet_cauchy_bound
    {n : ℕ} {lam Lam Lb : ℝ} {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
    (hlam : 0 < lam) (hB : HasEverywhereLoewnerBounds lam Lam B)
    (hBs : IsSmoothFullKineticCoefficient B) (hbs : IsSmoothDrift b)
    (hb : HasEuclideanLipschitzDrift Lb b)
    {a α τ r0 δ A S d L C ε : ℝ} (haα : a < α) (hατ : α < τ)
    (hA : 0 ≤ A) (hAd : A ≤ d) (hgap : 3 / 2 * A < δ) (hδr : δ < r0)
    (hd : 0 < d) (hdr : d < r0 / 4) (hL : 0 ≤ L)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hC : 0 ≤ C)
    {Γ : ℝ → PDE.Vec n} (hΓ : Continuous Γ)
    (F : BoundedBorel (EvolutionAmbientState n)) (hFC : ∀ q, |F q| ≤ C)
    (hsupp : ∀ q ∈ tsupport (F : EvolutionAmbientState n → ℝ),
      4 * d ≤ r0 - PDE.vecEuclideanNorm (q.1 - Γ τ)) :
    ∃ R0 : ℝ, 0 < R0 ∧ ∀ (β R : Fin 2 → ℝ),
      (∀ i, 0 < β i ∧ β i ≤ A) → (∀ i, R0 ≤ R i) →
      ∀ (g : Fin 2 → ℝ → PDE.Vec n),
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (g i)) →
      (∀ i s t, PDE.vecEuclideanNorm (g i s - g i t) ≤ L * |s - t|) →
      (∀ i s, s ∈ Icc α τ → PDE.vecEuclideanNorm (g i s - Γ s) ≤ β i / 2) →
      ∀ (u : Fin 2 → TimeVelocity (n + n) → ℝ),
      (∀ i, IsClassicalBackwardDirichletSolution a τ
        (openEllipsoid (straightenedEllipsoidMatrix n (r0 - β i) (R i)))
        (straightenedCoefficient B (g i) ε) (straightenedDrift b (g i))
        (fun _ _ => 0) (fun _ _ => 0)
        (fun x => F (g i τ + spatialY x, spatialZ x)) (fun _ => 0) (u i)) →
      ∀ p ∈ movingClosedSlab (PDE.euclideanBall 0 (r0 - δ)) Γ α τ ∩
        {q | radialSq q ≤ S ^ 2},
        |straightenedPullback (g 0) (u 0) p - straightenedPullback (g 1) (u 1) p| ≤
          2 * C * (growthBarrier (growthConstant n Lam (PDE.vecEuclideanNorm (b 0)) Lb) τ p /
            (1 + S ^ 2) + barrierW (collarKappa L lam) (δ + 3 / 2 * A) /
              barrierW (collarKappa L lam) d) := by
  obtain ⟨R0, hR0, hsize⟩ := exists_transportedRadius_common_innerCylinder
    (sub_pos.mpr hδr) (by linarith : 0 ≤ A / 2)
    (by linarith : (r0 - δ) + A / 2 < r0 - A) S
  refine ⟨R0, hR0, ?_⟩
  intro β R hβ hR g hg hgL hclose u hu p hp
  have hr (i : Fin 2) : 0 < r0 - β i := by linarith [(hβ i).2]
  have hd' (i : Fin 2) : d < r0 - β i := by linarith [(hβ i).2]
  have hc (i : Fin 2) (s : ℝ) (hs : s ∈ Icc α τ) :
      PDE.vecEuclideanNorm (g i s - Γ s) ≤ A / 2 :=
    (hclose i s hs).trans (by linarith [(hβ i).2])
  have ht (i : Fin 2) : ∀ q ∈ tsupport (F : EvolutionAmbientState n → ℝ),
      2 * d ≤ (r0 - β i) - PDE.vecEuclideanNorm (q.1 - g i τ) :=
    terminal_support_margin_of_innerBall_close ((hβ i).2.trans hAd) hsupp
      (hclose i τ ⟨hατ.le, le_rfl⟩)
  have he := abs_sub_le_common_innerCylinder_straightened_dirichlet
    hlam hB hBs hbs hb haα hατ (sub_pos.mpr hδr)
    (by linarith : r0 - δ ≤ r0) (by linarith : 0 ≤ A / 2)
    hd hL hε hε1 hC hΓ g (fun i => r0 - β i) R hg hgL hr
    (fun i => hR0.trans_le (hR i)) (fun i => by linarith [(hβ i).1]) hd' hc
    (fun i => hsize _ _ (by linarith [(hβ i).2]) (hR i)) F hFC ht u hu p hp
  have hκ : 0 < collarKappa L lam := div_pos (by linarith) hlam
  have hW := barrierW_pos hκ hd
  have hm : barrierW (collarKappa L lam) (r0 - (r0 - δ) + A / 2) ≤
      barrierW (collarKappa L lam) (δ + 3 / 2 * A) := by
    have hb' : r0 - (r0 - δ) + A / 2 ≤ δ + 3 / 2 * A := by linarith
    rcases hb'.lt_or_eq with h | h
    · exact (barrierW_strictMono hκ h).le
    · rw [h]
  exact he.trans (mul_le_mul_of_nonneg_left
    (add_le_add (le_refl _) (div_le_div_of_nonneg_right hm hW.le)) (by positivity))

end HypoellipticAleksandrov.KineticAleksandrov
