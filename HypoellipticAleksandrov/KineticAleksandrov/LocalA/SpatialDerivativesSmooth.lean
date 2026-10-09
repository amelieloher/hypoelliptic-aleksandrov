module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.LocalRepresentation
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ABPAbstractDefect
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.SmoothEstimateReflection

/-! # Interior spatial smoothness and pointwise equations from the source C112 class -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory Parabolic SectionTwo Evolution
open scoped Matrix.Norms.Elementwise

/-- Entrywise smoothness of the source lift implies smoothness on time-velocity space. -/
theorem sectionTwo_coefficient_smooth {d : ℕ} {lam Lam : ℝ}
    {B : CoefficientField d} (hB : IsSectionTwoCoefficient lam Lam B) :
    IsSmoothCoefficient B := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  exact (hB.2.2.1 i j).comp
    (contDiff_fst.prodMk (contDiff_snd.prodMk (contDiff_const (c := (0 : PDE.Vec d)))))

/-- The full source coefficient class is preserved by the stipulated reflection. -/
theorem sectionTwo_coefficient_reflection {d : ℕ} {lam Lam : ℝ}
    {B : CoefficientField d} (hB : IsSectionTwoCoefficient lam Lam B) :
    IsSectionTwoCoefficient lam Lam (kineticReflectedCoefficient B) := by
  refine ⟨hB.1, hB.2.1, ?_, ?_, ?_, ?_⟩
  · exact TheoremA.isSmoothFullKineticCoefficient_zIndependent
      (isSmoothCoefficient_kineticReflectedCoefficient B (sectionTwo_coefficient_smooth hB))
  · exact isSymmetricCoefficient_kineticReflectedCoefficient B hB.2.2.2.1
  · intro t v
    exact hB.2.2.2.2.1 (-t) v
  · intro t v
    exact hB.2.2.2.2.2 (-t) v

/-- Continuous classical backward residuals equal zero pointwise when zero almost everywhere. -/
theorem spatial_backward_equation_pointwise {d : ℕ} {D : Set (KineticPoint d)}
    (hD : IsOpen D) (A : CoefficientField d) (hA : IsSmoothCoefficient A)
    (u : KineticPoint d → ℝ) (hu : IsKineticC112On u D)
    (he : ∀ᵐ P ∂volume.restrict D, backwardOperatorOfTimeVelocityCoefficient A u P = 0) :
    ∀ P ∈ D, backwardOperatorOfTimeVelocityCoefficient A u P = 0 := by
  have hdot : ContinuousOn (fun P => PDE.vecDot P.velocity (kineticPositionGradient u P)) D := by
    unfold PDE.vecDot
    apply continuousOn_finsetSum
    intro i _
    exact ((continuous_apply i).comp continuous_velocity).continuousOn.mul
      ((continuous_apply i).comp_continuousOn hu.continuousOn_kineticPositionGradient)
  have hc : ContinuousOn (backwardOperatorOfTimeVelocityCoefficient A u) D := by
    change ContinuousOn (fun P => kineticTimeDerivative u P +
      PDE.vecDot P.velocity (kineticPositionGradient u P) -
      matrixContraction (A P.time P.velocity) (kineticVelocityHessian u P)) D
    exact (hu.continuousOn_kineticTimeDerivative.add hdot).sub
      (continuousOn_matrixContraction
        (hA.continuous.comp (continuous_time.prodMk continuous_velocity)).continuousOn
        hu.continuousOn_kineticVelocityHessian)
  exact Evolution.eqOn_of_ae_eq_of_continuousOn_kinetic hD
    (hc.comp (evolutionHomeomorph d).continuous.continuousOn (fun _ h => h))
    continuousOn_const he

/-- Hormander interior regularity gives the stipulated physical spatial slice smoothness. -/
theorem spatial_forward_slice_smooth
    (hH : HormanderHypoellipticityStatement) {d : ℕ} {lam Lam : ℝ}
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (Z₀ : KineticPoint d) {R : ℝ} (hR : 0 < R) (U : KineticPoint d → ℝ)
    (hUs : IsKineticC112On U (forwardCylinder Z₀ R hR))
    (hUe : ∀ Q ∈ forwardCylinder Z₀ R hR,
      forwardKineticOperator (ofTimeVelocityCoefficient B) U Q = 0)
    (P : KineticPoint d) (hP : P ∈ forwardCylinder Z₀ R hR) :
    ContDiffAt ℝ (⊤ : ℕ∞) (physicalPositionSlice U P) P.position := by
  have hs := mass_classical_homogeneous_smooth hH B hB
    (isOpen_forwardCylinder Z₀ R hR) U hUs hUe
  have ho : IsOpen ((KineticPoint.equivProd d) '' forwardCylinder Z₀ R hR) := by
    have h := (KineticPoint.homeomorphProd d).isOpenMap _ (isOpen_forwardCylinder Z₀ R hR)
    simpa only [KineticPoint.homeomorphProd, KineticPoint.isometryEquivProd,
      IsometryEquiv.coe_toHomeomorph, IsometryEquiv.coe_mk] using h
  have hp : ContDiffAt ℝ (⊤ : ℕ∞) (U ∘ (KineticPoint.equivProd d).symm)
      (KineticPoint.equivProd d P) := hs.contDiffAt (ho.mem_nhds ⟨P, hP, rfl⟩)
  change ContDiffAt ℝ (⊤ : ℕ∞) ((U ∘ (KineticPoint.equivProd d).symm) ∘
    fun x => (P.time, (x, P.velocity))) P.position
  exact hp.comp P.position (contDiffAt_const.prodMk
    (contDiffAt_id.prodMk contDiffAt_const))

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
