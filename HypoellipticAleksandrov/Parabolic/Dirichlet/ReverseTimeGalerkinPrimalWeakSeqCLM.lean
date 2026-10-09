module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinPrimalBochner
public import HypoellipticAleksandrov.Parabolic.Dirichlet.HilbertWeakSequentialCompactnessCLM
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Continuous-functional weak subsequence of reverse-time Galerkin primal curves

This module extracts a subsequence of the canonical Bochner-valued reverse-time
Galerkin primal curves that converges under every continuous real linear functional.
It makes no strong convergence, equation-passage, trace, or weak-solution assertion.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open Filter MeasureTheory Set
open scoped ENNReal Matrix Matrix.Norms.Elementwise MatrixOrder RealInnerProductSpace Topology

variable {d : ℕ} {Ω : Set (PDE.Vec d)}
variable
  (r₀ r₁ lam : ℝ) (h₀₁ : r₀ < r₁) (hlam : 0 < lam)
  (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
  (a : CoefficientField d)
  (b : ℝ → PDE.Vec d → PDE.Vec d) (c F : ℝ → PDE.Vec d → ℝ)
  (haSmooth : IsSmoothOnNeighborhood
    (fun z : TimeVelocity d => a z.1 z.2)
    (scalarParabolicClosedCylinder r₀ r₁ Ω))
  (hbSmooth : IsSmoothOnNeighborhood
    (fun z : TimeVelocity d => b z.1 z.2)
    (scalarParabolicClosedCylinder r₀ r₁ Ω))
  (hcSmooth : IsSmoothOnNeighborhood
    (fun z : TimeVelocity d => c z.1 z.2)
    (scalarParabolicClosedCylinder r₀ r₁ Ω))
  (hFSmooth : IsSmoothOnNeighborhood
    (fun z : TimeVelocity d => F z.1 z.2)
    (scalarParabolicClosedCylinder r₀ r₁ Ω))
  (hLower : ∀ z : TimeVelocity d,
    z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
      lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
  (hcNonpos : ∀ z : TimeVelocity d,
    z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → c z.1 z.2 ≤ 0)

/-- The canonical reverse-time Galerkin primal curves possess a strictly monotone
subsequence converging under every continuous real linear functional. -/
theorem exists_strictMono_tendsto_clm_reverseTimeGalerkinPrimal
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    ∃ (U : ReverseTimeL2V hΩ (r₁ - r₀)) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ ell : ReverseTimeL2V hΩ (r₁ - r₀) →L[ℝ] ℝ,
        Tendsto
          (fun n => ell
            (reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
              haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos (φ n) initial))
          atTop
          (𝓝 (ell U)) := by
  letI : TopologicalSpace.SeparableSpace (H10HilbertGraph hΩ) :=
    instSeparableSpaceH10HilbertGraph hΩ
  letI : MeasureTheory.SFinite (reverseTimeVolume (r₁ - r₀)) := by
    dsimp only [reverseTimeVolume]
    infer_instance
  letI : MeasurableSpace.CountablyGenerated ℝ := by infer_instance
  letI : MeasureTheory.IsSeparable (reverseTimeVolume (r₁ - r₀)) := by infer_instance
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  letI : SecondCountableTopology (ReverseTimeL2V hΩ (r₁ - r₀)) :=
    MeasureTheory.Lp.SecondCountableTopology
  letI : TopologicalSpace.SeparableSpace (ReverseTimeL2V hΩ (r₁ - r₀)) :=
    TopologicalSpace.SecondCountableTopology.to_separableSpace
  exact exists_strictMono_tendsto_clm_of_norm_le
    (fun N => reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial)
    (reverseTimeGalerkinPrimalRadius r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial)
    (fun N => norm_reverseTimeGalerkinPrimal_le_radius
      r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial N)

end HypoellipticAleksandrov.Parabolic.Dirichlet
