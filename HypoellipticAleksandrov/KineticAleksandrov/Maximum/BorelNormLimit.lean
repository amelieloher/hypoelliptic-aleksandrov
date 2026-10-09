module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelDominated
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-! # Source norm stability under the vanishing classical coefficient error -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Filter
open scoped Topology

/-- The Lp triangle inequality with finite real-valued norms. -/
theorem borel_real_norm_add_le {E : Type*} [MeasurableSpace E] {μ : Measure E}
    {p : ℝ} (hp : 1 ≤ p) {f g : E → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) μ) (hg : MemLp g (ENNReal.ofReal p) μ) :
    (eLpNorm (f + g) (ENNReal.ofReal p) μ).toReal ≤
      (eLpNorm f (ENNReal.ofReal p) μ).toReal +
      (eLpNorm g (ENNReal.ofReal p) μ).toReal := by
  have ht := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨hf.eLpNorm_ne_top,hg.eLpNorm_ne_top⟩)
    (eLpNorm_add_le (ENNReal.one_le_ofReal.mpr hp) (f := f) (g := g))
  simpa only [ENNReal.toReal_add hf.eLpNorm_ne_top hg.eLpNorm_ne_top] using ht

/-- Vanishing nonnegative error implies convergence of the actual perturbed source norms. -/
theorem borel_source_norm_tendsto {E : Type*} [MeasurableSpace E] {μ : Measure E}
    {p : ℝ} (hp : 1 ≤ p) (F : E → ℝ) (G e : ℕ → E → ℝ)
    (hF : MemLp F (ENNReal.ofReal p) μ)
    (he : ∀ j, MemLp (e j) (ENNReal.ofReal p) μ)
    (hGm : ∀ j, AEStronglyMeasurable (G j) μ)
    (hFn : ∀ᵐ z ∂μ, 0 ≤ F z) (hGn : ∀ j, ∀ᵐ z ∂μ, 0 ≤ G j z)
    (hen : ∀ j, ∀ᵐ z ∂μ, 0 ≤ e j z)
    (hclose : ∀ j, ∀ᵐ z ∂μ, |G j z - F z| ≤ e j z)
    (ht : Tendsto (fun j => (eLpNorm (e j) (ENNReal.ofReal p) μ).toReal) atTop (𝓝 0)) :
    Tendsto (fun j => (eLpNorm (G j) (ENNReal.ofReal p) μ).toReal) atTop
      (𝓝 (eLpNorm F (ENNReal.ofReal p) μ).toReal) := by
  have hdom j : ∀ᵐ z ∂μ, ‖G j z‖ ≤ ‖(F + e j) z‖ := by
    filter_upwards [hFn,hGn j,hen j,hclose j] with z hFz hGz hez hcl
    simp only [Pi.add_apply]
    rw [Real.norm_of_nonneg hGz,Real.norm_of_nonneg (add_nonneg hFz hez)]
    have hab := (abs_le.mp hcl).2
    exact by linarith only [hab]
  have hGp j : MemLp (G j) (ENNReal.ofReal p) μ :=
    (hF.add (he j)).of_le (hGm j) (hdom j)
  have hu j : (eLpNorm (G j) (ENNReal.ofReal p) μ).toReal ≤
      (eLpNorm F (ENNReal.ofReal p) μ).toReal +
      (eLpNorm (e j) (ENNReal.ofReal p) μ).toReal := by
    apply (ENNReal.toReal_mono (hF.add (he j)).eLpNorm_ne_top
      (eLpNorm_mono_ae (hGm j) (hdom j))).trans
    exact borel_real_norm_add_le hp hF (he j)
  have hl j : (eLpNorm F (ENNReal.ofReal p) μ).toReal ≤
      (eLpNorm (G j) (ENNReal.ofReal p) μ).toReal +
      (eLpNorm (e j) (ENNReal.ofReal p) μ).toReal := by
    apply (ENNReal.toReal_mono ((hGp j).add (he j)).eLpNorm_ne_top
      (eLpNorm_mono_ae hF.aestronglyMeasurable ?_)).trans
    · exact borel_real_norm_add_le hp (hGp j) (he j)
    · filter_upwards [hFn,hGn j,hen j,hclose j] with z hFz hGz hez hcl
      simp only [Pi.add_apply]
      rw [Real.norm_of_nonneg hFz,Real.norm_of_nonneg (add_nonneg hGz hez)]
      have hab := (abs_le.mp hcl).1
      linarith only [hab]
  rw [Metric.tendsto_atTop] at ht ⊢
  intro ε hε
  obtain ⟨N,hN⟩ := ht ε hε
  refine ⟨N,fun j hj => ?_⟩
  have hb := hN j hj
  rw [Real.dist_eq,sub_zero,abs_of_nonneg ENNReal.toReal_nonneg] at hb
  rw [Real.dist_eq]
  have ha : |(eLpNorm (G j) (ENNReal.ofReal p) μ).toReal -
      (eLpNorm F (ENNReal.ofReal p) μ).toReal| ≤
      (eLpNorm (e j) (ENNReal.ofReal p) μ).toReal := by
    rw [abs_le]
    constructor <;> linarith only [hu j,hl j]
  exact ha.trans_lt hb

end HypoellipticAleksandrov.KineticAleksandrov
