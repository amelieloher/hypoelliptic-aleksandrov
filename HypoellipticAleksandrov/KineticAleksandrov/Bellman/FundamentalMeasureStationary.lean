module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureFubini
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureIntegrationByParts
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureDegree
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasurePositive
import Mathlib.Tactic

/-! # The degree-two stationary adjoint witness from the explicit Kolmogorov Gaussian -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- The actual fundamental measure solves the stationary adjoint identity on punctured tests. -/
theorem bellmanFundamentalMeasure_stationary :
    IsBellmanStationaryAdjointPair bellmanFundamentalMeasure bellmanFundamentalMeasure := by
  intro φ hφ hc hs
  let fx : ℝ × ℝ → ℝ := fun q => q.2 * fderiv ℝ φ q (1, 0)
  let fv : ℝ × ℝ → ℝ := fun q =>
    fderiv ℝ (fun z => fderiv ℝ φ z (0, 1)) q (0, 1)
  have hcx : HasCompactSupport fx := (hc.fderiv_apply ℝ (1, 0)).mul_left
  have hcv : HasCompactSupport fv :=
    (hc.fderiv_apply ℝ (0, 1)).fderiv_apply ℝ (0, 1)
  have hx : Continuous fx := continuous_snd.mul
    (bellman_contDiff_direction hφ (1, 0)).continuous
  have hv : Continuous fv :=
    (bellman_contDiff_direction (bellman_contDiff_direction hφ (0, 1)) (0, 1)).continuous
  have hsx : tsupport fx ⊆ {q | q ≠ (0, 0)} :=
    tsupport_mul_subset_right.trans ((tsupport_fderiv_apply_subset ℝ (1, 0)).trans hs)
  have hsv : tsupport fv ⊆ {q | q ≠ (0, 0)} :=
    (tsupport_fderiv_apply_subset ℝ (0, 1)).trans
      ((tsupport_fderiv_apply_subset ℝ (0, 1)).trans hs)
  have hiX := bellman_integrable_fundamental_test hx hcx hsx
  have hiV := bellman_integrable_fundamental_test hv hcv hsv
  change (∫ q, fx q.val ∂bellmanFundamentalMeasure) +
    (∫ q, fv q.val ∂bellmanFundamentalMeasure) = 0
  rw [← integral_add hiX hiV]
  rw [bellmanFundamentalMeasure_integral_test (f := fun q => fx q + fv q) (hx.add hv) (hcx.add hcv)
    ((tsupport_add fx fv).trans (union_subset hsx hsv))]
  have heq (t : BellmanPositiveTime) (q : ℝ × ℝ) :
      -q.2 * fderiv ℝ (bellmanGaussianKernel t) q (1, 0) +
        fderiv ℝ (fun z => fderiv ℝ (bellmanGaussianKernel t) z (0, 1)) q (0, 1) =
      bellmanGaussianTimeCoefficient t.val q * bellmanGaussianKernel t q := by
    rw [bellmanGaussianKernel_fderiv_position, bellmanGaussianKernel_fderiv_velocity_twice]
    dsimp [bellmanGaussianTimeCoefficient]
    field_simp [ne_of_gt t.property]
    ring
  change (∫ t : BellmanPositiveTime, (∫ q : ℝ × ℝ, bellmanGaussianKernel t q *
    (q.2 * fderiv ℝ φ q (1, 0) +
      fderiv ℝ (fun z => fderiv ℝ φ z (0, 1)) q (0, 1)))
    ∂bellmanPositiveTimeVolume) = 0
  simp_rw [bellmanGaussianKernel_integral_generator _ φ hφ hc, heq]
  exact bellmanGaussianTimeDerivative_integral_test_eq_zero hφ.continuous hc hs

/-- The literal fundamental measure is a degree-two adjoint pair at diffusivity one. -/
theorem bellmanFundamentalMeasure_adjointPair :
    IsBellmanAdjointPair 1 1 2 bellmanFundamentalMeasure bellmanFundamentalMeasure := by
  refine ⟨bellmanFundamentalMeasure_radon, bellmanFundamentalMeasure_radon,
    Or.inl bellmanFundamentalMeasure_ne_zero, ?_, ?_,
    bellmanFundamentalMeasure_stationary, bellmanFundamentalMeasure_densityDegree,
    bellmanFundamentalMeasure_densityDegree⟩
  all_goals simp

/-- The explicit Gaussian fundamental measure supplies the degree-two witness at every ratio. -/
theorem two_mem_bellmanAdmissibleDegrees (R : ℝ) (hR : 1 ≤ R) :
    (2 : ℝ) ∈ bellmanAdmissibleDegrees R := by
  rw [mem_bellmanAdmissibleDegrees_iff]
  refine ⟨bellmanFundamentalMeasure, bellmanFundamentalMeasure,
    bellmanFundamentalMeasure_radon, bellmanFundamentalMeasure_radon,
    Or.inl bellmanFundamentalMeasure_ne_zero, ?_, ?_,
    bellmanFundamentalMeasure_stationary, bellmanFundamentalMeasure_densityDegree,
    bellmanFundamentalMeasure_densityDegree⟩
  · simp
  · calc
      bellmanFundamentalMeasure = (1 : ENNReal) • bellmanFundamentalMeasure := by simp
      _ ≤ ENNReal.ofReal R • bellmanFundamentalMeasure := by
        gcongr
        simpa using ENNReal.ofReal_le_ofReal hR

end HypoellipticAleksandrov.KineticAleksandrov
