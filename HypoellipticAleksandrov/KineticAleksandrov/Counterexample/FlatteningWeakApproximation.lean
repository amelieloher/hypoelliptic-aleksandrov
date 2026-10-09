module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.MollifyWeakJets
public import Mathlib.Topology.MetricSpace.Thickening
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileBounds

/-! # Local bounds for the normalized convolutions used in the weak chain rule

The mollification API is the independently written generic M-lane API. All uses here
are of proved normalized-convolution lemmas, with their ordinary analytic hypotheses.
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open MeasureTheory Filter Set Metric
open scoped Convolution

/-- A local bound on the kernel sampling ball suffices for the normalized convolution bound. -/
theorem spatialMollify_norm_le_on_ball {d : ℕ} (phi : ContDiffBump (0 : XV d))
    (g : XV d → ℝ) (hg : AEStronglyMeasurable g volume) (C : ℝ) (hC : 0 ≤ C)
    (q : XV d) (hb : ∀ y ∈ ball q phi.rOut, ‖g y‖ ≤ C) :
    ‖spatialMollify phi g q‖ ≤ C := by
  have h := dist_convolution_le (μ := volume) (x₀ := q) (z₀ := (0 : ℝ)) hC
    phi.support_normed_eq.subset phi.nonneg_normed phi.integral_normed hg
    (fun y hy => by simpa only [dist_zero_right] using hb y hy)
  simpa only [spatialMollify, dist_zero_right] using h

/-- Compact bounds away from zero give a uniform eventual bound on all sampled convolutions. -/
theorem spatialMollify_eventually_bounded_on_compact {d : ℕ} (g : XV d → ℝ)
    (hg : AEStronglyMeasurable g volume)
    (hb : ∀ L : Set (XV d), IsCompact L → 0 ∉ L →
      ∃ M : ℝ, ∀ q ∈ L, ‖g q‖ ≤ M)
    (K : Set (XV d)) (hK : IsCompact K) (hz : 0 ∉ K) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ n in atTop, ∀ q ∈ K, ‖spatialMollify (standardMollifierSequence n) g q‖ ≤ C := by
  have hsub : K ⊆ ({0}ᶜ : Set (XV d)) := by
    intro q hq
    change q ≠ 0
    intro he
    exact hz (he ▸ hq)
  obtain ⟨delta, hd, hdelta⟩ := hK.exists_cthickening_subset_open
    isOpen_compl_singleton hsub
  have hL : IsCompact (cthickening delta K) := hK.cthickening
  obtain ⟨M, hM⟩ := hb (cthickening delta K) hL
    (fun hmem => (by simpa using hdelta hmem))
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  have he : ∀ᶠ n in atTop, (standardMollifierSequence (G := XV d) n).rOut < delta :=
    standardMollifierSequence_rOut_tendsto.eventually (gt_mem_nhds hd)
  filter_upwards [he] with n hn
  intro q hq
  apply spatialMollify_norm_le_on_ball _ g hg _ (le_max_right _ _) q
  intro y hy
  have hym : y ∈ cthickening delta K :=
    mem_cthickening_of_dist_le y q delta K hq ((mem_ball.mp hy).le.trans hn.le)
  exact (hM y hym).trans (le_max_left _ _)

/-- The standard normalized convolution converges almost everywhere for every locally
integrable scalar function, without a global boundedness assumption. -/
theorem spatialMollify_ae_tendsto {d : ℕ} (g : XV d → ℝ) (hg : LocallyIntegrable g volume) :
    ∀ᵐ q ∂volume,
      Tendsto (fun n => spatialMollify (standardMollifierSequence n) g q) atTop (nhds (g q)) := by
  have h := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (standardMollifierSequence_rOut_tendsto (G := XV d))
    (Eventually.of_forall (standardMollifierSequence_radius_ratio (G := XV d))) hg
  exact h

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
