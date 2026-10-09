module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.MeasureDerivativeRadon
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.MeasureDerivativeLebesguePrimitive
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.MeasureDerivativePrimitiveWeak
import Mathlib.Tactic

/-! # Density recovery from a first measure derivative -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- The explicit primitive of a flux minus a weighted measure is locally integrable. -/
theorem bellman_fluxMeasurePrimitive_locallyIntegrable (F : Measure ℝ)
    [IsFiniteMeasureOnCompacts F] (g J : ℝ → ℝ) (hg : Continuous g)
    (hJ : LocallyIntegrable J volume) (a : ℝ) :
    LocallyIntegrable
      (fun x => (∫ z in 0..x, J z) - a * bellmanMeasurePrimitive F g 0 x) volume := by
  convert!
    (bellman_lebesguePrimitive_continuous J hJ).locallyIntegrable.sub
      ((bellmanMeasurePrimitive_locallyIntegrable F g hg).smul a) using 1

/-- The explicit primitive satisfies the corresponding first weak derivative identity. -/
theorem bellman_fluxMeasurePrimitive_weak (F : Measure ℝ)
    [IsFiniteMeasureOnCompacts F] (g J : ℝ → ℝ) (hg : Continuous g)
    (hJ : LocallyIntegrable J volume) (a : ℝ) (φ : BellmanRealTest) :
    (∫ x, φ x * J x) - a * (∫ x, g x * φ x ∂F) =
      -(∫ x, deriv φ x *
        ((∫ z in 0..x, J z) - a * bellmanMeasurePrimitive F g 0 x)) := by
  have h1 := bellman_lebesguePrimitive_weak J hJ φ φ.contDiff φ.hasCompactSupport
  have h2 := bellmanMeasurePrimitive_weak F g hg φ φ.contDiff φ.hasCompactSupport
  have hd : Continuous (deriv φ) := (contDiff_infty_iff_deriv.mp φ.contDiff).2.continuous
  have hc : HasCompactSupport (deriv φ) := φ.hasCompactSupport.deriv
  have hi1 : Integrable (fun x => deriv φ x * (∫ z in 0..x, J z)) volume := by
    exact LocallyIntegrable.integrable_smul_left_of_hasCompactSupport
      (bellman_lebesguePrimitive_continuous J hJ).locallyIntegrable hd hc
  have hi2 : Integrable (fun x => deriv φ x * bellmanMeasurePrimitive F g 0 x) volume := by
    exact LocallyIntegrable.integrable_smul_left_of_hasCompactSupport
      (bellmanMeasurePrimitive_locallyIntegrable F g hg) hd hc
  rw [show (fun x => deriv φ x *
      ((∫ z in 0..x, J z) - a * bellmanMeasurePrimitive F g 0 x)) =
      (fun x => deriv φ x * (∫ z in 0..x, J z) -
        a * (deriv φ x * bellmanMeasurePrimitive F g 0 x)) by funext x; ring,
    integral_sub hi1 (hi2.const_mul a), integral_const_mul]
  have hs1 : (∫ x, deriv φ x * (∫ z in 0..x, J z)) = -∫ x, φ x * J x := by
    rw [show (fun x => deriv φ x * (∫ z in 0..x, J z)) =
      (fun x => (∫ z in 0..x, J z) * deriv φ x) by funext x; ring, h1]
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ fun x => mul_comm _ _
  have hs2 : (∫ x, deriv φ x * bellmanMeasurePrimitive F g 0 x) =
      -∫ x, g x * φ x ∂F := by
    rw [show (fun x => deriv φ x * bellmanMeasurePrimitive F g 0 x) =
      (fun x => bellmanMeasurePrimitive F g 0 x * deriv φ x) by funext x; ring, h2]
  rw [hs1, hs2]
  ring

/-- A measure with flux minus weighted-measure derivative has an actual explicit density. -/
theorem bellman_measure_density_of_flux (F H : Measure ℝ)
    [IsFiniteMeasureOnCompacts F] [IsFiniteMeasureOnCompacts H]
    (g J : ℝ → ℝ) (hg : Continuous g) (hJ : LocallyIntegrable J volume) (a : ℝ)
    (hw : ∀ φ : BellmanRealTest, (∫ x, deriv φ x ∂H) =
      a * (∫ x, g x * φ x ∂F) - (∫ x, φ x * J x)) :
    ∃ c : ℝ, H = volume.withDensity (fun x => ENNReal.ofReal
      (c + (∫ z in 0..x, J z) - a * bellmanMeasurePrimitive F g 0 x)) ∧
      ∀ᵐ x ∂volume, 0 ≤ c + (∫ z in 0..x, J z) -
        a * bellmanMeasurePrimitive F g 0 x := by
  let p := fun x => (∫ z in 0..x, J z) - a * bellmanMeasurePrimitive F g 0 x
  have hp : LocallyIntegrable p volume :=
    bellman_fluxMeasurePrimitive_locallyIntegrable F g J hg hJ a
  have h1 : LocallyIntegrable (fun _ : ℝ => (1 : ℝ)) H :=
    continuous_const.locallyIntegrable
  let L := bellmanWeightedTestIntegral H (fun _ => 1) - bellmanWeightedTestIntegral volume p
  have hzero : ∀ φ : BellmanRealTest, L (bellmanTestDerivative φ) = 0 := by
    intro φ
    change bellmanWeightedTestIntegral H (fun _ => 1) (bellmanTestDerivative φ) -
      bellmanWeightedTestIntegral volume p (bellmanTestDerivative φ) = 0
    rw [bellmanWeightedTestIntegral_apply H _ h1,
      bellmanWeightedTestIntegral_apply volume p hp]
    change (∫ x, deriv φ x * 1 ∂H) - (∫ x, deriv φ x * p x) = 0
    simp only [mul_one]
    rw [hw φ]
    have he := bellman_fluxMeasurePrimitive_weak F g J hg hJ a φ
    change (∫ x, φ x * J x) - a * (∫ x, g x * φ x ∂F) =
      -(∫ x, deriv φ x * p x) at he
    linarith
  obtain ⟨c, hc⟩ := bellman_test_derivative_kernel L hzero
  refine ⟨c, ?_⟩
  have hm : Measurable p :=
    (bellman_lebesguePrimitive_continuous J hJ).measurable.sub
      (measurable_const.mul
        (bellmanMeasurePrimitive_stronglyMeasurable F g hg.measurable 0).measurable)
  have hcp : LocallyIntegrable (fun x => c + p x) volume :=
    continuous_const.locallyIntegrable.add hp
  have htest : ∀ φ : BellmanRealTest,
      (∫ x, φ x ∂H) = ∫ x, φ x * (c + p x) := by
    intro φ
    have he := hc φ
    change bellmanWeightedTestIntegral H (fun _ => 1) φ -
      bellmanWeightedTestIntegral volume p φ = c * (∫ x, φ x) at he
    rw [bellmanWeightedTestIntegral_apply H _ h1,
      bellmanWeightedTestIntegral_apply volume p hp] at he
    simp only [mul_one] at he
    have hi : Integrable (fun x => φ x * p x) volume := by
      convert! hp.integrable_smul_left_of_hasCompactSupport
        φ.contDiff.continuous φ.hasCompactSupport using 1
    have hiφ : Integrable (fun x => φ x) volume :=
      φ.contDiff.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
    rw [show (fun x => φ x * (c + p x)) =
      (fun x => c * φ x + φ x * p x) by funext x; ring,
      integral_add (hiφ.const_mul c) hi, integral_const_mul]
    linarith
  have hmeasure := bellman_measure_eq_withDensity_of_test_pairing H (fun x => c + p x)
    (measurable_const.add hm) hcp htest
  constructor
  · rw [hmeasure]
    congr 1
    funext x
    congr 1
    dsimp [p]
    ring
  · have hn := bellman_nonneg_of_test_pairing H (fun x => c + p x) hcp htest
    filter_upwards [hn] with x hx
    dsimp [p] at hx
    linarith

end HypoellipticAleksandrov.KineticAleksandrov
