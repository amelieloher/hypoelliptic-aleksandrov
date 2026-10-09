module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundarySolution
import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.UniquenessMeasure

/-! # Uniqueness from all stipulated ambient smooth compact tests -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory SectionTwo

/-- Finite physical measures are determined by the stipulated smooth product-coordinate tests. -/
theorem boundary_measure_ext {d : ℕ} (μ ν : Measure (KineticPoint d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ φ : KineticPoint d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) (φ ∘ (KineticPoint.equivProd d).symm) →
      HasCompactSupport φ → (∫ P, φ P ∂μ) = ∫ P, φ P ∂ν) : μ = ν := by
  let H := KineticPoint.homeomorphProd d
  have hmap : μ.map H = ν.map H := by
    apply measure_eq_of_smooth_integral_eq isOpen_univ
    · simp only [compl_univ, measure_empty]
    · simp only [compl_univ, measure_empty]
    intro ψ hψ hc _ _
    rw [integral_map H.measurable.aemeasurable hψ.continuous.measurable.aestronglyMeasurable,
      integral_map H.measurable.aemeasurable hψ.continuous.measurable.aestronglyMeasurable]
    apply h (ψ ∘ H)
    · have heq : (ψ ∘ H) ∘ (KineticPoint.equivProd d).symm = ψ := by
        funext q
        exact congrArg ψ (H.apply_symm_apply q)
      rw [heq]
      exact hψ
    · exact hc.comp_homeomorph H
  exact H.measurableEmbedding.map_injective hmap

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
