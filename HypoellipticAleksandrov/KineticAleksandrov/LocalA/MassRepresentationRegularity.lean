module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.MassRepresentationCoordinates
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundarySolutionRegularity
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.HomogeneousReconstructionJets

/-! # Actual weak and smooth regularity of source-class homogeneous physical solutions -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory Parabolic Evolution SectionTwo TheoremA Occupation

/-- A physical C112 homogeneous solution satisfies the actual packed weak equation. -/
theorem mass_classical_homogeneous_weak {d : ℕ} {lam Lam : ℝ}
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    {D : Set (KineticPoint d)} (hD : IsOpen D)
    (u : KineticPoint d → ℝ) (hu : IsKineticC112On u D)
    (he : ∀ P ∈ D, forwardKineticOperator (ofTimeVelocityCoefficient B) u P = 0) :
    IsWeakTransportedSolution (zIndependentCoefficient B) (identityDrift d)
      (massPhysicalPoint ⁻¹' D) (u ∘ massPhysicalPoint) (fun _ => 0) := by
  let U := massPhysicalPoint ⁻¹' D
  have hU : IsOpen U := hD.preimage continuous_massPhysicalPoint
  have hc {f : KineticPoint d → ℝ} (hf : ContinuousOn f D) :
      ContinuousOn (f ∘ massPhysicalPoint) U :=
    hf.comp continuous_massPhysicalPoint.continuousOn (fun _ hx => hx)
  have hV (i : Fin d) : ContinuousOn
      (fun x => kineticVelocityGradient u (massPhysicalPoint x) i) U :=
    hc ((continuous_apply i).comp_continuousOn hu.continuousOn_kineticVelocityGradient)
  have hZ (i : Fin d) : ContinuousOn
      (fun x => kineticPositionGradient u (massPhysicalPoint x) i) U :=
    hc ((continuous_apply i).comp_continuousOn hu.continuousOn_kineticPositionGradient)
  have hH (i j : Fin d) : ContinuousOn
      (fun x => kineticVelocityHessian u (massPhysicalPoint x) j i) U :=
    hc ((continuous_apply i).comp_continuousOn
      ((continuous_apply j).comp_continuousOn hu.continuousOn_kineticVelocityHessian))
  refine ⟨(hc hu.continuousOn).locallyIntegrableOn hU.measurableSet, ?_⟩
  intro ψ hψ hcompact hs
  have hi := Autonomous.integral_transportedAdjoint_of_anisotropic_jets
    (zIndependentCoefficient B) (identityDrift d) (sectionTwoCoefficient_fullBounds lam Lam B hB).1
    (identityDrift_smooth d) (u ∘ massPhysicalPoint)
    (kineticTimeDerivative u ∘ massPhysicalPoint)
    (fun i x => kineticVelocityGradient u (massPhysicalPoint x) i)
    (fun i x => kineticPositionGradient u (massPhysicalPoint x) i)
    (fun i j x => kineticVelocityHessian u (massPhysicalPoint x) j i)
    (hc hu.continuousOn) (hc hu.continuousOn_kineticTimeDerivative) hV hZ hH
    (fun _ hx => mass_time_hasLineDerivAt hu hx)
    (fun i _ hx => mass_velocity_hasLineDerivAt hu hx i)
    (fun i _ hx => mass_position_hasLineDerivAt hu hx i)
    (fun i j _ hx => mass_hessian_hasLineDerivAt hu hx i j) ψ hψ hcompact hs
  refine hi.trans ((setIntegral_eq_zero_of_forall_eq_zero ?_).trans ?_)
  · intro x hx
    have hsum : (∑ i, ∑ j,
        B (timeCoord d x) (diffusedCoord d x) i j *
          kineticVelocityHessian u (massPhysicalPoint x) j i) =
        matrixContraction (B (timeCoord d x) (diffusedCoord d x))
          (kineticVelocityHessian u (massPhysicalPoint x)) := by
      rw [matrixContraction, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [(hB.2.2.2.1 (timeCoord d x) (diffusedCoord d x)).apply i j]
    have hp := he (massPhysicalPoint x) hx
    rw [forwardKineticOperator_apply] at hp
    simp only [zIndependentCoefficient, identityDrift, Function.comp_apply, id_eq]
    rw [hsum]
    change (kineticTimeDerivative u (massPhysicalPoint x) +
      matrixContraction (B (timeCoord d x) (diffusedCoord d x))
        (kineticVelocityHessian u (massPhysicalPoint x)) +
      PDE.vecDot (diffusedCoord d x) (kineticPositionGradient u (massPhysicalPoint x))) * ψ x = 0
    have hp' : kineticTimeDerivative u (massPhysicalPoint x) +
        matrixContraction (B (timeCoord d x) (diffusedCoord d x))
          (kineticVelocityHessian u (massPhysicalPoint x)) +
        PDE.vecDot (diffusedCoord d x) (kineticPositionGradient u (massPhysicalPoint x)) = 0 := by
      simpa only [ofTimeVelocityCoefficient, massPhysicalPoint, add_right_comm] using! hp
    rw [hp', zero_mul]
  · simp only [zero_mul, integral_zero]

/-- Hörmander upgrades the exact C112 homogeneous class without a second position premise. -/
theorem mass_classical_homogeneous_smooth
    (hH : HormanderHypoellipticityStatement) {d : ℕ} {lam Lam : ℝ}
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    {D : Set (KineticPoint d)} (hD : IsOpen D)
    (u : KineticPoint d → ℝ) (hu : IsKineticC112On u D)
    (he : ∀ P ∈ D, forwardKineticOperator (ofTimeVelocityCoefficient B) u P = 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) (u ∘ (KineticPoint.equivProd d).symm)
      ((KineticPoint.equivProd d) '' D) := by
  have hw := mass_classical_homogeneous_weak B hB hD u hu he
  have hset : massPhysicalPoint ⁻¹' D =
      evolutionHomeomorph d ⁻¹' (sectionTwoPoint '' D) := by
    ext x
    constructor
    · intro hx
      exact ⟨massPhysicalPoint x, hx, rfl⟩
    · rintro ⟨P, hP, hEq⟩
      have hp : massPhysicalPoint x = P := congrArg sectionTwoPoint hEq.symm
      change massPhysicalPoint x ∈ D
      rw [hp]
      exact hP
  have hc : ContinuousOn (u ∘ massPhysicalPoint) (massPhysicalPoint ⁻¹' D) :=
    hu.continuousOn.comp continuous_massPhysicalPoint.continuousOn (fun _ hx => hx)
  obtain ⟨f, hf, hae⟩ := exists_smooth_representative_transported_source hH hB.1
    (sectionTwoCoefficient_fullBounds lam Lam B hB).1
    (sectionTwoCoefficient_fullBounds lam Lam B hB).2.2
    (identityDrift_smooth d) zero_lt_one (identityDrift_bounds d).2
    (hD.preimage continuous_massPhysicalPoint) hw contDiffOn_const
  have hEq := Measure.eqOn_open_of_ae_eq hae (hD.preimage continuous_massPhysicalPoint)
    hc hf.continuousOn
  have hs := hf.congr (fun x hx => hEq hx)
  apply boundary_native_smooth_to_physical D u
  rw [← hset]
  exact hs

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
