module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinPrimalBase
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeBochnerEnergy

/-!
# Canonical reverse-time Galerkin Bochner classes

This module packages the selected raw reverse-time Galerkin curves into their
canonical `L²(V)` quotient classes.  It derives an explicit uniform squared
bound and its square-root radius, without making compactness, trace, or weak
solution assertions.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open MeasureTheory Set
open scoped ENNReal Matrix Matrix.Norms.Elementwise MatrixOrder RealInnerProductSpace

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

/-- The canonical quotient-valued representative of the selected raw
reverse-time Galerkin curve. -/
noncomputable def reverseTimeGalerkinPrimal
    (N : ℕ) (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    ReverseTimeL2V hΩ (r₁ - r₀) :=
  reverseTimeL2OfContinuousOn (r₁ - r₀)
    (reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial)
    (continuousOn_reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
      a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial)

/-- The uniform value-energy bound for every selected Galerkin curve. -/
noncomputable def reverseTimeGalerkinPrimalValueBound
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) : ℝ :=
  gronwallBound (‖initial‖ ^ 2)
    (2 * reverseTimeGalerkinPrimalK r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos + 1)
    (reverseTimeGalerkinPrimalM r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos ^ 2)
    (r₁ - r₀)

/-- The uniform gradient-energy bound for every selected Galerkin curve. -/
noncomputable def reverseTimeGalerkinPrimalGradientBound
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) : ℝ :=
  ‖initial‖ ^ 2 +
    (2 * reverseTimeGalerkinPrimalK r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos + 1) * (r₁ - r₀) *
      reverseTimeGalerkinPrimalValueBound r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
        haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial +
    (reverseTimeGalerkinPrimalM r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos ^ 2) * (r₁ - r₀)

/-- The uniform squared `L²(V)` bound for every selected Galerkin curve. -/
noncomputable def reverseTimeGalerkinPrimalNormSqBound
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) : ℝ :=
  (r₁ - r₀) *
      reverseTimeGalerkinPrimalValueBound r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
        haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial +
    reverseTimeGalerkinPrimalGradientBound r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial / lam

/-- The explicit uniform radius associated with the squared Bochner bound. -/
noncomputable def reverseTimeGalerkinPrimalRadius
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) : ℝ :=
  Real.sqrt
    (reverseTimeGalerkinPrimalNormSqBound r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial)

/-- The canonical quotient representative agrees almost everywhere with its
selected raw Galerkin curve. -/
theorem ae_reverseTimeGalerkinPrimal_eq_raw
    (N : ℕ) (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial =ᵐ[
        reverseTimeVolume (r₁ - r₀)]
      reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
        haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial := by
  exact coeFn_reverseTimeL2OfContinuousOn (r₁ - r₀)
    (reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial)
    (continuousOn_reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
      a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial)

private theorem reverseTimeGalerkinPrimal_value_energy_le_bound
    (N : ℕ) (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (t : ℝ) (ht : t ∈ Set.Icc 0 (r₁ - r₀)) :
    ‖valueCLM hΩ
      (reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
        haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial t)‖ ^ 2 ≤
      reverseTimeGalerkinPrimalValueBound r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
        haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial := by
  have hK : 0 ≤ 2 * reverseTimeGalerkinPrimalK r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
      a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos + 1 := by
    nlinarith [reverseTimeGalerkinPrimalK_nonneg r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
      a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos]
  calc
    ‖valueCLM hΩ
        (reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
          haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial t)‖ ^ 2 ≤
        gronwallBound (‖initial‖ ^ 2)
          (2 * reverseTimeGalerkinPrimalK r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
            haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos + 1)
          (reverseTimeGalerkinPrimalM r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
            haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos ^ 2) t :=
      reverseTimeGalerkinPrimal_value_energy r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
        haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial t ht
    _ ≤ gronwallBound (‖initial‖ ^ 2)
          (2 * reverseTimeGalerkinPrimalK r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
            haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos + 1)
          (reverseTimeGalerkinPrimalM r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
            haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos ^ 2) (r₁ - r₀) :=
      gronwallBound_mono (sq_nonneg ‖initial‖) (sq_nonneg _ ) hK ht.2
    _ = reverseTimeGalerkinPrimalValueBound r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
          haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial := rfl

private theorem reverseTimeGalerkinPrimal_gradient_energy_le_bound
    (N : ℕ) (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    lam * ∫ τ in Set.Ioc 0 (r₁ - r₀),
      ‖gradientCLM hΩ
        (reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
          haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial τ)‖ ^ 2 ≤
      reverseTimeGalerkinPrimalGradientBound r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
        haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial := by
  simpa only [reverseTimeGalerkinPrimalGradientBound,
    reverseTimeGalerkinPrimalValueBound] using
    (reverseTimeGalerkinPrimal_gradient_energy r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial (r₁ - r₀)
      ⟨sub_nonneg.mpr h₀₁.le, le_rfl⟩)

/-- The canonical reverse-time Galerkin class satisfies the explicit uniform
squared Bochner bound. -/
theorem norm_sq_reverseTimeGalerkinPrimal_le
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) (N : ℕ) :
    ‖reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial‖ ^ 2 ≤
      reverseTimeGalerkinPrimalNormSqBound r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
        haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial := by
  have hT : 0 < r₁ - r₀ := sub_pos.mpr h₀₁
  obtain ⟨W, hWraw, hWbound⟩ := exists_reverseTimeL2V_of_continuousOn_energy hΩ hT hlam
    (reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial)
    (continuousOn_reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial)
    (reverseTimeGalerkinPrimal_value_energy_le_bound r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
      a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial)
    (reverseTimeGalerkinPrimal_gradient_energy_le_bound r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
      a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial)
  have hW : W = reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial := by
    apply MeasureTheory.Lp.ext
    exact hWraw.trans
      (ae_reverseTimeGalerkinPrimal_eq_raw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
        haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial).symm
  calc
    ‖reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
        haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial‖ ^ 2 = ‖W‖ ^ 2 := by
      rw [hW]
    _ ≤ (r₁ - r₀) *
          reverseTimeGalerkinPrimalValueBound r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
            haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial +
        reverseTimeGalerkinPrimalGradientBound r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
          haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial / lam := hWbound
    _ = reverseTimeGalerkinPrimalNormSqBound r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
          haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial := rfl

private theorem reverseTimeGalerkinPrimalNormSqBound_nonneg
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    0 ≤ reverseTimeGalerkinPrimalNormSqBound r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial := by
  exact (sq_nonneg ‖reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
    haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos 0 initial‖).trans
    (norm_sq_reverseTimeGalerkinPrimal_le r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial 0)

/-- The canonical reverse-time Galerkin class lies in its explicit uniform
Bochner radius. -/
theorem norm_reverseTimeGalerkinPrimal_le_radius
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) (N : ℕ) :
    ‖reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial‖ ≤
      reverseTimeGalerkinPrimalRadius r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
        haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial := by
  apply (Real.le_sqrt (norm_nonneg _)
    (reverseTimeGalerkinPrimalNormSqBound_nonneg r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial)).mpr
  simpa only [reverseTimeGalerkinPrimalRadius] using
    (norm_sq_reverseTimeGalerkinPrimal_le r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial N)

end HypoellipticAleksandrov.Parabolic.Dirichlet
