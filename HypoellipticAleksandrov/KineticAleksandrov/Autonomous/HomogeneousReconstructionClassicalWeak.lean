module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.HomogeneousReconstructionCoordinates
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.HomogeneousReconstructionWeak
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ReconstructionTraces

/-! # Weak forcing of physical C112 tests

The forcing is the literal scalar kinetic operator. The directional-jet identity
discharges the weak equation without requiring extra transported derivatives.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Parabolic Evolution SectionTwo MeasureTheory Set

/-- A physical C112 test satisfies its actual weak equation in packed coordinates. -/
theorem reconstruction_test_isWeakTransportedSolution {lam Lam : ℝ}
    (A : SmoothAutonomous lam Lam) {D : Set Point} (hD : IsOpen D)
    {phi : Point → ℝ} (hphi : IsKineticC112On phi D) :
    IsWeakTransportedSolution (evolutionCoefficient A.a) (identityDrift 1)
      (reconstructionPhysicalPoint ⁻¹' D) (phi ∘ reconstructionPhysicalPoint)
      (forwardScalarOperator A.a phi ∘ reconstructionPhysicalPoint) := by
  let U := reconstructionPhysicalPoint ⁻¹' D
  have hU : IsOpen U := hD.preimage continuous_reconstructionPhysicalPoint
  have hc {f : Point → ℝ} (hf : ContinuousOn f D) :
      ContinuousOn (f ∘ reconstructionPhysicalPoint) U :=
    hf.comp continuous_reconstructionPhysicalPoint.continuousOn (fun _ hx => hx)
  have hV (i : Fin 1) : ContinuousOn
      (fun x => kineticVelocityGradient phi (reconstructionPhysicalPoint x) i) U :=
    hc ((continuous_apply i).comp_continuousOn hphi.continuousOn_kineticVelocityGradient)
  have hZ (i : Fin 1) : ContinuousOn
      (fun x => kineticPositionGradient phi (reconstructionPhysicalPoint x) i) U :=
    hc ((continuous_apply i).comp_continuousOn hphi.continuousOn_kineticPositionGradient)
  have hH (i j : Fin 1) : ContinuousOn
      (fun x => kineticVelocityHessian phi (reconstructionPhysicalPoint x) j i) U :=
    hc ((continuous_apply i).comp_continuousOn
      ((continuous_apply j).comp_continuousOn hphi.continuousOn_kineticVelocityHessian))
  refine ⟨(hc hphi.continuousOn).locallyIntegrableOn hU.measurableSet, ?_⟩
  intro ψ hψ hcompact hs
  have h := integral_transportedAdjoint_of_anisotropic_jets
    (evolutionCoefficient A.a) (identityDrift 1) (evolutionCoefficient_smooth A)
    (identityDrift_smooth 1) (phi ∘ reconstructionPhysicalPoint)
    (kineticTimeDerivative phi ∘ reconstructionPhysicalPoint)
    (fun i x => kineticVelocityGradient phi (reconstructionPhysicalPoint x) i)
    (fun i x => kineticPositionGradient phi (reconstructionPhysicalPoint x) i)
    (fun i j x => kineticVelocityHessian phi (reconstructionPhysicalPoint x) j i)
    (hc hphi.continuousOn) (hc hphi.continuousOn_kineticTimeDerivative)
    hV hZ hH
    (fun _ hx => reconstruction_time_hasLineDerivAt hphi hx)
    (fun i _ hx => reconstruction_velocity_hasLineDerivAt hphi hx i)
    (fun i _ hx => reconstruction_position_hasLineDerivAt hphi hx i)
    (fun i j _ hx => reconstruction_hessian_hasLineDerivAt hphi hx i j)
    ψ hψ hcompact hs
  refine h.trans (integral_congr_ae (Filter.Eventually.of_forall ?_))
  intro x
  simp only [Fin.sum_univ_one, evolutionCoefficient, identityDrift,
    Function.comp_def, forwardScalarOperator, reconstructionPhysicalPoint, id_eq]
  ring

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
