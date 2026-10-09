module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementApprox
import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.UniquenessMeasure
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.Topology.TietzeExtension

/-! # Smooth approximation of continuous parabolic boundary data

Continuous data on a compact closed carrier are first extended by Tietze's theorem.
Local convolution and a smooth cutoff give actual ambient smooth compact approximants.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Set Metric

/-- Continuous compact-carrier data have smooth compact approximants in any open neighborhood. -/
theorem exists_smooth_compact_boundary_approx
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (w : E → ℝ) (hw : ContinuousOn w K) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧
      tsupport f ⊆ U ∧ ∀ x ∈ K, |f x - w x| < ε := by
  let W : C(K, ℝ) := ⟨fun x => w x, continuousOn_iff_continuous_domRestrict.mp hw⟩
  obtain ⟨G, hG⟩ := W.exists_restrict_eq hK.isClosed
  have heq : ∀ x ∈ K, G x = w x := by
    intro x hx
    exact congrArg (fun F : C(K, ℝ) => F ⟨x, hx⟩) hG
  have huc : UniformContinuousOn G (cthickening 1 K) :=
    hK.cthickening.uniformContinuousOn_of_continuous G.continuous.continuousOn
  obtain ⟨δ, hδ, hGδ⟩ := Metric.uniformContinuousOn_iff.mp huc (ε / 2) (half_pos hε)
  obtain ⟨g, hg, hgc⟩ :=
    G.continuous.exists_contDiff_dist_le_of_forall_mem_ball_dist_le (lt_min one_pos hδ)
  obtain ⟨χ, hχ, hχc, hχU, _, hχK⟩ :=
    KineticAleksandrov.SectionTwo.exists_smooth_cutoff hK hU hKU
  refine ⟨fun x => χ x * g x, hχ.mul hg, hχc.mul_right,
    tsupport_mul_subset_left.trans hχU, ?_⟩
  intro x hx
  change |χ x * g x - w x| < ε
  rw [hχK x hx, one_mul, ← heq x hx, ← Real.dist_eq]
  apply (hgc x (ε / 2) ?_).trans_lt (half_lt_self hε)
  intro y hy
  rw [mem_ball, lt_min_iff] at hy
  exact (hGδ y (mem_cthickening_of_dist_le _ x _ _ hx hy.1.le) x
    (self_subset_cthickening _ hx) hy.2).le

end HypoellipticAleksandrov.Parabolic.LocalHolder
