module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonCalculus
import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementSource
public import HypoellipticAleksandrov.Parabolic.ScalarDirichletSup
import HypoellipticAleksandrov.Parabolic.ScalarDirichletComparison

/-! # Uniform stability under approximation of boundary data

The homogeneous comparison estimate makes uniformly close boundary approximants
uniformly close throughout the whole closed cylinder.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Set

/-- Homogeneous solutions with uniformly close boundary data are uniformly close inside. -/
theorem abs_homogeneous_solution_sub_le_boundary_error {d : ℕ}
    {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (a T : ℝ) (haT : a < T) (A : CoefficientField d)
    (hAc : IsContinuousCoefficient A) (hApsd : ∀ t y, (A t y).PosSemidef)
    (φ₁ φ₂ : PDE.Vec d → ℝ) (b₁ b₂ u v : TimeVelocity d → ℝ)
    (hu : IsClassicalBackwardDirichletSolution a T Ω A
      (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) φ₁ b₁ u)
    (hv : IsClassicalBackwardDirichletSolution a T Ω A
      (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) φ₂ b₂ v)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hφ : ∀ y ∈ closure Ω, |φ₁ y - φ₂ y| ≤ ε)
    (hb : ∀ z ∈ scalarParabolicLateralFace a T Ω, |b₁ z - b₂ z| ≤ ε) :
    ∀ z ∈ scalarParabolicClosedCylinder a T Ω, |u z - v z| ≤ 2 * ε := by
  have huv := isClassicalBackwardDirichletSolution_sub hu hv
  intro z hz
  have h := abs_le_terminal_lateral_source_envelope_of_isClassicalBackwardDirichletSolution
    hΩ hΩb haT A (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => (0 : ℝ) - 0)
    (fun y => φ₁ y - φ₂ y) (fun z => b₁ z - b₂ z) (fun z => u z - v z)
    hAc continuous_const hApsd (fun _ _ => le_rfl) huv
    ε ε 0 hε hε le_rfl hφ hb (fun _ _ => by simp only [sub_self, abs_zero, le_refl]) hz
  simpa only [mul_zero, add_zero, two_mul] using h

end HypoellipticAleksandrov.Parabolic.LocalHolder
