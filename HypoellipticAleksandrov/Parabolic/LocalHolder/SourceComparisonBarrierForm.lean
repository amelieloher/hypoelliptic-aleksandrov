module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonSobolevJets
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialForm
import HypoellipticAleksandrov.Parabolic.Dirichlet.WeakTestFunctionSobolevJet

/-! # Literal spatial form of a smooth Sobolev barrier

This identifies each quotient-valued pairing with the classical representative integral.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open MeasureTheory Dirichlet
open scoped ENNReal

/-- A smooth H10 barrier evaluates against smooth tests by its classical spatial jets. -/
theorem reverseTimeSpatialForm_smooth_barrier_test {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T τ : ℝ) (A : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (q : PDE.H10Function Ω) (hq : ContDiff ℝ 1 q.toH1Function.toFun)
    (ψ : PDE.WeakTestFunction Ω) :
    reverseTimeSpatialForm hΩ T τ A b c (h10HilbertGraphOfH10Function hΩ q)
      (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ ψ) =
      (∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
        A (T - τ) y i j * PDE.classicalGradient q.toH1Function.toFun y j *
          ψ.partialDeriv i y) +
      (∑ j : Fin d, ∫ y in Ω, reverseTimeDivergenceDrift T A b τ y j *
        PDE.classicalGradient q.toH1Function.toFun y j * ψ y) -
      ∫ y in Ω, reverseTimeScalarCoefficient T c τ y * q.toH1Function.toFun y * ψ y := by
  rw [reverseTimeSpatialForm_apply]
  have hp (i j : Fin d) :
      (∫ y in Ω, A (T - τ) y i j *
        PDE.hilbertVectorLpCoord Ω 2 j
          (gradientCLM hΩ (h10HilbertGraphOfH10Function hΩ q)) y *
        PDE.hilbertVectorLpCoord Ω 2 i
          (gradientCLM hΩ (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ ψ)) y) =
      ∫ y in Ω, A (T - τ) y i j *
        PDE.classicalGradient q.toH1Function.toFun y j * ψ.partialDeriv i y := by
    apply integral_congr_ae
    filter_upwards [gradientCoord_h10HilbertGraph_ae_classical hΩ q hq j,
      PDE.coeFn_hilbertVectorLpCoord Ω 2 i
        (gradientCLM hΩ (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ ψ)),
      ae_gradientCoordCLM_smoothCompactlySupportedH1HilbertGraph hΩ ψ i]
      with y hqj hpi hψi
    rw [hqj, hpi, hψi]
  have hb (j : Fin d) :
      (∫ y in Ω, reverseTimeDivergenceDrift T A b τ y j *
        PDE.hilbertVectorLpCoord Ω 2 j
          (gradientCLM hΩ (h10HilbertGraphOfH10Function hΩ q)) y *
        valueCLM hΩ (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ ψ) y) =
      ∫ y in Ω, reverseTimeDivergenceDrift T A b τ y j *
        PDE.classicalGradient q.toH1Function.toFun y j * ψ y := by
    apply integral_congr_ae
    filter_upwards [gradientCoord_h10HilbertGraph_ae_classical hΩ q hq j,
      ae_valueCLM_smoothCompactlySupportedH1HilbertGraph hΩ ψ] with y hqj hψ
    rw [hqj, hψ]
  have hc :
      (∫ y in Ω, reverseTimeScalarCoefficient T c τ y *
        valueCLM hΩ (h10HilbertGraphOfH10Function hΩ q) y *
        valueCLM hΩ (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ ψ) y) =
      ∫ y in Ω, reverseTimeScalarCoefficient T c τ y * q.toH1Function.toFun y * ψ y := by
    apply integral_congr_ae
    filter_upwards [valueCLM_h10HilbertGraphOfH10Function hΩ q,
      ae_valueCLM_smoothCompactlySupportedH1HilbertGraph hΩ ψ] with y hqv hψ
    rw [hqv, hψ]
  simp_rw [hp, hb, hc]

end HypoellipticAleksandrov.Parabolic.LocalHolder
