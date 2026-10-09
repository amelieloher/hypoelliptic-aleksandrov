module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.SpatialDerivativesForward
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.InnerCylinderReflection
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelSource

/-! # Reflection preserves spatial derivative norms and the literal cylinder oscillation -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory Parabolic SectionTwo

/-- The backward source data become exactly the local forward homogeneous solution class. -/
theorem spatial_reflected_data {d : ℕ} {lam Lam : ℝ}
    (A : CoefficientField d) (hA : IsSectionTwoCoefficient lam Lam A)
    (P₀ : KineticPoint d) {R : ℝ} (hR : 0 < R) (u : KineticPoint d → ℝ)
    (hc : ContinuousOn u (closure (backwardCylinder P₀ R)))
    (hs : IsKineticC112On u (backwardCylinder P₀ R))
    (he : ∀ᵐ P ∂volume.restrict (backwardCylinder P₀ R),
      backwardOperatorOfTimeVelocityCoefficient A u P = 0) :
    let U := u ∘ kineticReflection
    let Z₀ := kineticReflection P₀
    ContinuousOn U (closure (forwardCylinder Z₀ R hR)) ∧
      IsKineticC112On U (forwardCylinder Z₀ R hR) ∧
      ∀ Q ∈ forwardCylinder Z₀ R hR,
        forwardKineticOperator (ofTimeVelocityCoefficient (kineticReflectedCoefficient A)) U Q =
          0 := by
  dsimp only
  have heq := spatial_backward_equation_pointwise (isOpen_backwardCylinder P₀ R hR)
    A (sectionTwo_coefficient_smooth hA) u hs he
  refine ⟨?_, ?_, ?_⟩
  · rw [← TheoremA.preimage_closure_backwardCylinder_reflection P₀ R hR]
    exact hc.comp (continuous_kineticReflection d).continuousOn (fun _ h => h)
  · rw [← TheoremA.preimage_backwardCylinder_reflection P₀ R hR]
    exact isKineticC112On_kineticReflection u _ hs
  · intro Q hQ
    rw [reflectedKineticOperator_reflection, heq (kineticReflection Q) ?_, neg_zero]
    rw [← TheoremA.preimage_backwardCylinder_reflection P₀ R hR] at hQ
    exact hQ

/-- Reflection preserves the raw oscillation on the exact pair of cylinders. -/
theorem spatial_oscillation_reflection {d : ℕ} (P₀ : KineticPoint d)
    {R : ℝ} (hR : 0 < R) (u : KineticPoint d → ℝ) :
    Holder.oscillationOn (u ∘ kineticReflection)
        (forwardCylinder (kineticReflection P₀) R hR) =
      Holder.oscillationOn u (backwardCylinder P₀ R) := by
  have hi : (u ∘ kineticReflection) '' forwardCylinder (kineticReflection P₀) R hR =
      u '' backwardCylinder P₀ R := by
    rw [image_comp, kineticReflection_image_forwardCylinder, kineticReflection_involutive]
  simp only [Holder.oscillationOn, hi]

/-- The original physical position slice is the reflected slice composed with negation. -/
theorem spatial_slice_reflection {d : ℕ} (u : KineticPoint d → ℝ) (P : KineticPoint d) :
    physicalPositionSlice u P =
      physicalPositionSlice (u ∘ kineticReflection) (kineticReflection P) ∘ Neg.neg := by
  funext x
  simp only [physicalPositionSlice, Function.comp_apply, kineticReflection, neg_neg]

/-- The stipulated spatial derivative norm is unchanged by reflection, at every order. -/
theorem spatial_derivative_norm_reflection {d : ℕ} (u : KineticPoint d → ℝ)
    (P : KineticPoint d) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (physicalPositionSlice u P) P.position‖ =
      ‖iteratedFDeriv ℝ m (physicalPositionSlice (u ∘ kineticReflection)
        (kineticReflection P)) (kineticReflection P).position‖ := by
  rw [spatial_slice_reflection]
  exact (LinearIsometryEquiv.neg ℝ (E := PDE.Vec d)).norm_iteratedFDeriv_comp_right _ _ _

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
