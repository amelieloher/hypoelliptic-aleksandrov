module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarAxis
import Mathlib.Tactic

/-!
# Global scalar growth

Compact middle-interval bounds and the two actual normalized limits control the whole profile.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open Filter Set
open scoped Topology

/-- Continuous real functions with finite normalized limits have a global power bound. -/
theorem scalar_power_growth (f : ℝ → ℝ) (alpha c : ℝ) (hf : Continuous f)
    (ht : Tendsto (fun s => f s / Real.rpow |s| alpha) atTop (𝓝 c))
    (hb : Tendsto (fun s => f s / Real.rpow |s| alpha) atBot (𝓝 c)) :
    ∃ K : ℝ, 0 < K ∧ c ≤ K ∧ ∀ s, |f s| ≤ K * (1 + Real.rpow |s| alpha) := by
  have htc := ht.abs.eventually (Iio_mem_nhds (lt_add_one |c|))
  have hbc := hb.abs.eventually (Iio_mem_nhds (lt_add_one |c|))
  obtain ⟨a, ha⟩ := eventually_atTop.mp htc
  obtain ⟨b, hb⟩ := eventually_atBot.mp hbc
  let R : ℝ := max (max a (-b)) 1
  have hR : 1 ≤ R := le_max_right _ _
  have hRa : a ≤ R := (le_max_left _ _).trans (le_max_left _ _)
  have hRb : -b ≤ R := (le_max_right _ _).trans (le_max_left _ _)
  obtain ⟨M, hM⟩ := (isCompact_Icc.image hf.abs).bddAbove
  let K : ℝ := max (max M (|c| + 1)) 1
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hKM : M ≤ K := (le_max_left _ _).trans (le_max_left _ _)
  have hKc : |c| + 1 ≤ K := (le_max_right _ _).trans (le_max_left _ _)
  refine ⟨K, hK, (le_abs_self c).trans ((le_add_of_nonneg_right zero_le_one).trans hKc), ?_⟩
  intro s
  have hpow : 0 ≤ Real.rpow |s| alpha := Real.rpow_nonneg (abs_nonneg _) _
  by_cases hs : s ∈ Icc (-R) R
  · have hm : |f s| ≤ M := hM (mem_image_of_mem _ hs)
    exact hm.trans (hKM.trans (le_mul_of_one_le_right hK.le (by linarith)))
  · have hs0 : s ≠ 0 := by
      intro hz
      apply hs
      subst s
      constructor <;> linarith
    have hp : 0 < Real.rpow |s| alpha := by
      simpa only [Real.rpow_eq_pow] using Real.rpow_pos_of_pos (abs_pos.mpr hs0) alpha
    have hratio : |f s / Real.rpow |s| alpha| < |c| + 1 := by
      rcases lt_or_ge s (-R) with hleft | hleft
      · exact hb s (by linarith)
      · exact ha s (by
          have hr : R < s := by
            by_contra hn
            exact hs ⟨hleft, le_of_not_gt hn⟩
          linarith)
    rw [abs_div, abs_of_pos hp] at hratio
    have hfs := (div_lt_iff₀ hp).mp hratio
    exact hfs.le.trans ((mul_le_mul_of_nonneg_right hKc hpow).trans
      (mul_le_mul_of_nonneg_left (by linarith) hK.le))

/-- The source similarity function has a uniform global power-growth bound. -/
theorem F_growth (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam)
    (hmatch : Pgamma gamma.1 - Qgamma gamma.1 * Real.rpow Lam (-(1 / 3)) =
      Real.rpow Lam (-gamma.1)) :
    ∃ K : ℝ, 0 < K ∧ Real.rpow (9 * Lam) (-gamma.1) ≤ K ∧
      ∀ s, |F gamma Lam s| ≤ K * (1 + Real.rpow |s| (3 * gamma.1)) :=
  scalar_power_growth _ _ _ (F_contDiff_two gamma Lam hLam).continuous
    (F_ratio_atTop gamma Lam hLam) (F_ratio_atBot gamma Lam hLam hmatch)

/-- Global anisotropic growth of the literal reflected profile. -/
theorem scalarProfile_growth (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam)
    (hmatch : Pgamma gamma.1 - Qgamma gamma.1 * Real.rpow Lam (-(1 / 3)) =
      Real.rpow Lam (-gamma.1)) :
    ∃ K : ℝ, 0 < K ∧ ∀ q : XV 1, |scalarProfile gamma Lam q| ≤
      K * (Real.rpow |q.1 0| gamma.1 + Real.rpow |q.2 0| (3 * gamma.1)) := by
  obtain ⟨K, hK, hKC, hF⟩ := F_growth gamma Lam hLam hmatch
  have hA (x v : ℝ) (hx : 0 < x) : |scalarAnsatz gamma Lam x v| ≤
      K * (Real.rpow x gamma.1 + Real.rpow |v| (3 * gamma.1)) := by
    have hp : 0 < Real.rpow x gamma.1 := by
      simpa only [Real.rpow_eq_pow] using Real.rpow_pos_of_pos hx gamma.1
    have h := mul_le_mul_of_nonneg_left (hF (scalarSimilarity x v)) hp.le
    have he := scalar_similarity_power_cancel gamma x v hx
    change |Real.rpow x gamma.1 * F gamma Lam (scalarSimilarity x v)| ≤ _
    rw [abs_mul, abs_of_pos hp]
    calc
      _ ≤ Real.rpow x gamma.1 * (K * (1 +
          Real.rpow |scalarSimilarity x v| (3 * gamma.1))) := h
      _ = K * (Real.rpow x gamma.1 + Real.rpow |v| (3 * gamma.1)) := by
        rw [← he]
        ring
  refine ⟨K, hK, ?_⟩
  intro q
  rcases lt_trichotomy (q.1 0) 0 with hx | hx | hx
  · simpa only [scalarProfile, not_lt.mpr hx.le, hx, ↓reduceIte,
      abs_of_neg hx, abs_neg] using hA (-q.1 0) (-q.2 0) (neg_pos.mpr hx)
  · simp only [scalarProfile, hx, lt_self_iff_false, ↓reduceIte, abs_zero,
      scalarTrace, abs_mul]
    simp only [Real.rpow_eq_pow, Real.zero_rpow gamma.2.1.ne', zero_add]
    rw [abs_of_pos (by
      simpa only [Real.rpow_eq_pow] using
        Real.rpow_pos_of_pos (mul_pos (by norm_num) hLam) (-gamma.1)),
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact mul_le_mul_of_nonneg_right hKC (Real.rpow_nonneg (abs_nonneg _) _)
  · simpa only [scalarProfile, hx, ↓reduceIte, abs_of_pos hx] using hA _ _ hx

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
