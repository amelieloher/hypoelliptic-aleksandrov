module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularEquationSetting
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.MeasureDerivativeFunctionals
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.MeasureDerivativePrimitiveWeak
import Mathlib.Tactic

/-! # Constructing the actual angular flux from the angular weak equation -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- The angular equation gives a literal locally integrable flux with a weighted-measure
derivative. -/
theorem bellmanAngularFlux_weak (R β : ℝ) (F H : Measure ℝ)
    (hang : IsBellmanAngularAdjointPair 1 R β F H) :
    ∃ j : ℝ, ∀ φ : BellmanRealTest,
      (∫ x, deriv φ x ∂H) =
        (1 / 3 : ℝ) * (∫ x, x ^ 2 * φ x ∂F) -
          (∫ x, φ x * (j - ((β - 2) / 3) * bellmanMeasurePrimitive F id 0 x)) := by
  let : IsFiniteMeasureOnCompacts F := hang.1
  let : IsFiniteMeasureOnCompacts H := hang.2.2.1
  let A := bellmanMeasurePrimitive F id 0
  have hA : LocallyIntegrable A volume :=
    bellmanMeasurePrimitive_locallyIntegrable F id continuous_id
  have h1H : LocallyIntegrable (fun _ : ℝ => (1 : ℝ)) H :=
    continuous_const.locallyIntegrable
  have h2F : LocallyIntegrable (fun x : ℝ => x ^ 2) F :=
    (continuous_id.pow 2).locallyIntegrable
  let L : BellmanRealTest →ₗ[ℝ] ℝ :=
    (bellmanWeightedTestIntegral H (fun _ => 1)).comp bellmanTestDerivativeLinearMap -
      (1 / 3 : ℝ) • bellmanWeightedTestIntegral F (fun x => x ^ 2) -
      ((β - 2) / 3) • bellmanWeightedTestIntegral volume A
  have hL (φ : BellmanRealTest) : L φ = (∫ x, deriv φ x ∂H) -
      (1 / 3 : ℝ) * (∫ x, φ x * x ^ 2 ∂F) -
      ((β - 2) / 3) * (∫ x, φ x * A x) := by
    change bellmanWeightedTestIntegral H (fun _ => 1) (bellmanTestDerivative φ) -
      (1 / 3 : ℝ) * bellmanWeightedTestIntegral F (fun x => x ^ 2) φ -
      ((β - 2) / 3) * bellmanWeightedTestIntegral volume A φ = _
    rw [bellmanWeightedTestIntegral_apply H _ h1H,
      bellmanWeightedTestIntegral_apply F _ h2F,
      bellmanWeightedTestIntegral_apply volume A hA]
    simp only [bellmanTestDerivative, mul_one]
    rfl
  have hzero : ∀ φ : BellmanRealTest, L (bellmanTestDerivative φ) = 0 := by
    intro φ
    rw [hL]
    change (∫ x, deriv (deriv φ) x ∂H) -
      (1 / 3 : ℝ) * (∫ x, deriv φ x * x ^ 2 ∂F) -
      ((β - 2) / 3) * (∫ x, deriv φ x * A x) = 0
    have he := hang.2.2.2.2.2.2 φ φ.contDiff φ.hasCompactSupport
    have hw := bellmanMeasurePrimitive_weak F id continuous_id φ
      φ.contDiff φ.hasCompactSupport
    have hswap : (∫ x, deriv φ x * A x) = -∫ x, x * φ x ∂F := by
      rw [show (fun x => deriv φ x * A x) = (fun x => A x * deriv φ x) by
        funext x; ring]
      exact hw
    have hswap2 : (∫ x, deriv φ x * x ^ 2 ∂F) = ∫ x, x ^ 2 * deriv φ x ∂F := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => mul_comm _ _
    rw [hswap, hswap2]
    linear_combination he
  obtain ⟨k, hk⟩ := bellman_test_derivative_kernel L hzero
  refine ⟨-k, ?_⟩
  intro φ
  have he := hk φ
  rw [hL] at he
  have hiA : Integrable (fun x => φ x * A x) volume := by
    simpa only [smul_eq_mul] using
      hA.integrable_smul_left_of_hasCompactSupport φ.contDiff.continuous φ.hasCompactSupport
  have hiφ : Integrable (fun x => φ x) volume :=
    φ.contDiff.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have hJI : (∫ x, φ x * (-k - ((β - 2) / 3) * A x)) =
      -k * (∫ x, φ x) - ((β - 2) / 3) * (∫ x, φ x * A x) := by
    rw [show (fun x => φ x * (-k - ((β - 2) / 3) * A x)) =
        (fun x => -k * φ x - ((β - 2) / 3) * (φ x * A x)) by funext x; ring,
      integral_sub (hiφ.const_mul (-k)) (hiA.const_mul _),
      integral_const_mul, integral_const_mul]
  change (∫ x, deriv φ x ∂H) =
    (1 / 3 : ℝ) * (∫ x, x ^ 2 * φ x ∂F) -
      (∫ x, φ x * (-k - ((β - 2) / 3) * A x))
  rw [hJI, show (fun x => x ^ 2 * φ x) = (fun x => φ x * x ^ 2) by funext x; ring]
  linarith

end HypoellipticAleksandrov.KineticAleksandrov
