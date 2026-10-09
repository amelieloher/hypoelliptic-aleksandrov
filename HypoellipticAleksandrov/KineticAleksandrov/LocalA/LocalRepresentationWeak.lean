module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.MassRepresentationRegularity
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceRestriction

/-! # Classical residuals and cancellation of genuine signed weak sources -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory Parabolic Evolution SectionTwo TheoremA Occupation

/-- Integration by parts for the classical residual of a smooth coefficient. -/
theorem localRepresentation_classical_weak {d : ℕ} {lam Lam : ℝ}
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    {D : Set (KineticPoint d)} (hD : IsOpen D)
    (u : KineticPoint d → ℝ) (hu : IsKineticC112On u D)
    : IsWeakTransportedSolution (zIndependentCoefficient B) (identityDrift d)
      (massPhysicalPoint ⁻¹' D) (u ∘ massPhysicalPoint)
      (forwardKineticOperator (ofTimeVelocityCoefficient B) u ∘ massPhysicalPoint) := by
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
  refine hi.trans (setIntegral_congr_fun hU.measurableSet ?_)
  intro x hx
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
  simp only [zIndependentCoefficient, identityDrift, Function.comp_apply, id_eq]
  rw [hsum]
  simp only [forwardKineticOperator_apply, ofTimeVelocityCoefficient, massPhysicalPoint]
  simp only [PDE.vecDot]
  ring

private theorem localRepresentation_integrable_mul_test {d : ℕ} {D : Set (EvolutionVec d)}
    {u ψ : EvolutionVec d → ℝ} (hu : LocallyIntegrableOn u D volume)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ D) :
    IntegrableOn (fun x => u x * ψ x) D volume := by
  have hi := hu.integrableOn_compact_subset hs hc.isCompact
  have hm := hi.mul_continuousOn hψ.continuousOn hc.isCompact
  have hg : Integrable (fun x => u x * ψ x) volume := by
    apply (integrableOn_iff_integrable_of_support_subset ?_).mp hm
    intro x hx
    exact tsupport_mul_subset_right (subset_closure hx)
  exact hg.integrableOn

/-- Opposite genuine weak sources cancel; this is internal weak-equation calculus. -/
theorem localRepresentation_weak_cancel {d : ℕ}
    (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    (hB : IsSmoothFullKineticCoefficient B) (hb : IsSmoothDrift b)
    (D : Set (EvolutionVec d)) (u w f : EvolutionVec d → ℝ)
    (hu : IsWeakTransportedSolution B b D u f)
    (hw : IsWeakTransportedSolution B b D w (fun x => -f x)) :
    IsWeakTransportedSolution B b D (fun x => u x + w x) (fun _ => 0) := by
  refine ⟨hu.1.add hw.1, ?_⟩
  intro ψ hψ hc hs
  have ha := (contDiff_transportedAdjoint hB hb hψ).continuous
  have hac := hasCompactSupport_transportedAdjoint (B := B) (b := b) hc
  have has : tsupport (transportedAdjoint B b ψ) ⊆ D :=
    (fun x hx => hs (boundedSourceAdjoint_support ψ hx))
  have hiu := localRepresentation_integrable_mul_test hu.1 ha hac has
  have hiw := localRepresentation_integrable_mul_test hw.1 ha hac has
  simp only [add_mul]
  rw [integral_add hiu hiw, hu.2 ψ hψ hc hs, hw.2 ψ hψ hc hs]
  simp only [neg_mul, integral_neg, add_neg_cancel, zero_mul, integral_zero]

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
