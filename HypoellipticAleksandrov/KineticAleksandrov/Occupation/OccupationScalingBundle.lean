module

public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.OccupationScalingTerminal
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.OccupationScalingKernel

/-! # Direct transport of the shared parabolic marginal bundle -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation
open HypoellipticAleksandrov SectionTwo Scaling MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory

/-- The given parabolic marginal bundle transports directly to the constructed scaled kernel. -/
theorem occupation_scaled_marginalBundle {d : ℕ} (σ₀ : ℝ)
    (r : {r : ℝ // 0 < r}) {B : CoefficientField d}
    (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
    (hP : HasParabolicMarginalBundle (wholeSpace d) (fun _ => (0 : PDE.Vec d))
      MeasurableSet.univ (zIndependentCoefficient B) K) :
    HasParabolicMarginalBundle (wholeSpace d) (fun _ => (0 : PDE.Vec d))
      MeasurableSet.univ (zIndependentCoefficient (scaledCoefficient B σ₀ 0 r))
      (KineticAffineScaling.pushKernel (KineticAffineScaling.mapsDomain_wholeSpace
        (KineticAffineScaling.ofRadius σ₀ 0 0 (identityDrift d) r)) K) := by
  intro _hBz
  obtain ⟨Q, -, h2, h3, h4, h5, h6, -, h8, h9, h10⟩ := hP (fun _ _ _ _ => rfl)
  let Φ := KineticAffineScaling.ofRadius σ₀ 0 0 (identityDrift d) r
  let Kt := KineticAffineScaling.pushKernel (KineticAffineScaling.mapsDomain_wholeSpace Φ) K
  refine ⟨occupation_pushParabolicFamily Φ Q, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro σ τ hστ y z
    apply (wholeSpacePositionEquiv d τ).measurableEmbedding.map_injective
    have ha := MovingFiberKernel.map_fiberFirstMarginal_eq_firstMarginal Kt
      MeasurableSet.univ σ τ hστ (positionStateZero (wholeSpace d) (fun _ => 0) σ y)
    have hb := MovingFiberKernel.map_fiberFirstMarginal_eq_firstMarginal Kt
      MeasurableSet.univ σ τ hστ (evolutionStateOfPosition (wholeSpace d) (fun _ => 0) σ y z)
    have hi := occupation_scaled_firstMarginal_independent Φ K hP σ τ hστ y.1 0 z
    exact ha.trans (hi.trans hb.symm)
  · exact occupation_pushParabolicFamily_endpoint Φ Q h2
  · exact occupation_pushParabolicFamily_positive Φ Q h3
  · exact occupation_pushParabolicFamily_contraction Φ Q h4
  · exact occupation_pushParabolicFamily_composition Φ Q h5
  · intro σ τ hστ y f
    let eσ := occupation_positionEquiv Φ σ
    let eτ := occupation_positionEquiv Φ τ
    let f0 := occupation_borelComap eτ.symm eτ.symm.measurable f
    have heval := h6 (Φ.time σ) (Φ.time τ) (Φ.time_le_iff.mpr hστ) (eσ y) f0
    have hc := occupation_parabolicMarginal_conjugate Φ K hP σ τ hστ y
    have hi := congrArg (fun μ => ∫ x, f x ∂μ) hc
    have hm := eτ.symm.measurableEmbedding.integral_map (fun x => f x)
      (μ := parabolicMarginalKernel K MeasurableSet.univ (Φ.time σ) (Φ.time τ)
        (Φ.time_le_iff.mpr hστ) (eσ y))
    exact heval.trans (hi.trans hm).symm
  · exact occupation_parabolicMarginal_measurable Kt
  · intro σ
    have hc := occupation_parabolicKernel_conjugate Φ K hP σ σ le_rfl
    have hident := congrArg (kernelConj (occupation_positionEquiv Φ σ)
      (occupation_positionEquiv Φ σ)) (h8 (Φ.time σ))
    exact hc.trans (hident.trans (kernelConj_id (occupation_positionEquiv Φ σ)))
  · intro σ s τ hσs hsτ
    have hc := occupation_parabolicKernel_conjugate Φ K hP σ τ (hσs.trans hsτ)
    have hcs := occupation_parabolicKernel_conjugate Φ K hP σ s hσs
    have hct := occupation_parabolicKernel_conjugate Φ K hP s τ hsτ
    have hold := congrArg (kernelConj (occupation_positionEquiv Φ σ)
      (occupation_positionEquiv Φ τ))
      (h9 (Φ.time σ) (Φ.time s) (Φ.time τ)
        (Φ.time_le_iff.mpr hσs) (Φ.time_le_iff.mpr hsτ))
    have hcomp := kernelConj_comp (occupation_positionEquiv Φ σ)
      (occupation_positionEquiv Φ s) (occupation_positionEquiv Φ τ)
      (parabolicMarginalKernel K MeasurableSet.univ (Φ.time σ) (Φ.time s)
        (Φ.time_le_iff.mpr hσs))
      (parabolicMarginalKernel K MeasurableSet.univ (Φ.time s) (Φ.time τ)
        (Φ.time_le_iff.mpr hsτ))
    exact hc.trans (hold.trans (hcomp.trans
      (congrArg₂ (fun A B => A ∘ₖ B) hct.symm hcs.symm)))
  · exact occupation_scalarTerminalClause_scale σ₀ r B Q h10

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
