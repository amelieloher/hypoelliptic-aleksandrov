module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.H10FunctionHilbertGraph
public import PDEFoundation.Sobolev.ClassicalGradient

/-! # Classical jets of smooth zero-boundary Sobolev barriers

Weak derivative uniqueness identifies the stored Sobolev gradient with the classical jet.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open MeasureTheory Dirichlet
open scoped ENNReal

/-- The weak gradient of a smooth H10 representative is its classical gradient. -/
theorem h10Function_grad_ae_classical {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (q : PDE.H10Function Ω)
    (hq : ContDiff ℝ 1 q.toH1Function.toFun) (i : Fin d) :
    (fun x => q.toH1Function.grad x i) =ᵐ[PDE.volumeOn Ω]
      fun x => PDE.classicalGradient q.toH1Function.toFun x i := by
  apply PDE.HasWeakPartialDerivOn.ae_eq hΩ
  · exact locallyIntegrableOn_of_locallyIntegrable_restrict
      ((q.toH1Function.gradMemL2 i).locallyIntegrable (by norm_num))
  · have hc : Continuous (fun x => PDE.classicalGradient q.toH1Function.toFun x i) :=
      (continuous_apply i).comp (PDE.ContDiff.continuous_classicalGradient hq)
    exact hc.continuousOn.locallyIntegrableOn hΩ.measurableSet
  · exact q.toH1Function.hasWeakGradient i
  · exact PDE.HasWeakGradientOn.of_contDiff hq i

/-- The canonical Hilbert graph of a smooth barrier has the classical gradient jet. -/
theorem gradientCoord_h10HilbertGraph_ae_classical {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (q : PDE.H10Function Ω)
    (hq : ContDiff ℝ 1 q.toH1Function.toFun) (i : Fin d) :
    (fun x => PDE.hilbertVectorLpCoord Ω 2 i
      (gradientCLM hΩ (h10HilbertGraphOfH10Function hΩ q)) x)
      =ᵐ[PDE.volumeOn Ω] fun x => PDE.classicalGradient q.toH1Function.toFun x i :=
  (gradientCoord_h10HilbertGraphOfH10Function hΩ q i).trans
    (h10Function_grad_ae_classical hΩ q hq i)

end HypoellipticAleksandrov.Parabolic.LocalHolder
