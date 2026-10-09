module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningWeakApproximation
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Passing locally bounded smooth approximations through compact test integrals -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open MeasureTheory Filter Set

/-- Uniform eventual bounds on a compact test support allow dominated convergence of pairings. -/
theorem integral_mul_test_tendsto {d : ℕ} (F : ℕ → XV d → ℝ) (f : XV d → ℝ)
    (hm : ∀ n, AEStronglyMeasurable (F n) volume)
    (hl : ∀ᵐ q ∂volume, Tendsto (fun n => F n q) atTop (nhds (f q)))
    (test : XV d → ℝ) (ht : Continuous test) (hs : HasCompactSupport test)
    (K : Set (XV d)) (hsub : tsupport test ⊆ K)
    (C : ℝ) (_hC : 0 ≤ C) (hb : ∀ᶠ n in atTop, ∀ q ∈ K, ‖F n q‖ ≤ C) :
    Tendsto (fun n => ∫ q, F n q * test q) atTop (nhds (∫ q, f q * test q)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun q => C * ‖test q‖)
  · exact Eventually.of_forall (fun n => (hm n).mul ht.aestronglyMeasurable)
  · filter_upwards [hb] with n hn
    exact Eventually.of_forall (fun q => by
      rw [norm_mul]
      by_cases hq : q ∈ K
      · exact mul_le_mul_of_nonneg_right (hn q hq) (norm_nonneg _)
      · have hz : test q = 0 := image_eq_zero_of_notMem_tsupport (fun hmem => hq (hsub hmem))
        simp only [hz, norm_zero, mul_zero, le_refl])
  · exact (ht.integrable_of_hasCompactSupport hs).norm.const_mul C
  · filter_upwards [hl] with q hq
    exact hq.mul tendsto_const_nhds

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
