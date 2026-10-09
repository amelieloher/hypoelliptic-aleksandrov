module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.MeasureDerivativeDensity
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularIntegratedCalculus
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.Tactic

/-! # Comparing actual angular densities and converting their measure primitives -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- Measure comparison implies almost everywhere comparison of real nonnegative densities. -/
theorem bellman_density_le_of_measure_le (f h : ℝ → ℝ)
    (hmf : Measurable f) (hnf : ∀ᵐ x ∂volume, 0 ≤ f x)
    (hnh : ∀ᵐ x ∂volume, 0 ≤ h x)
    (hm : volume.withDensity (fun x => ENNReal.ofReal (f x)) ≤
      volume.withDensity (fun x => ENNReal.ofReal (h x))) :
    ∀ᵐ x ∂volume, f x ≤ h x := by
  have he : (fun x => ENNReal.ofReal (f x)) ≤ᵐ[volume]
      (fun x => ENNReal.ofReal (h x)) := by
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite hmf.ennreal_ofReal
    intro s hs _
    simpa only [← withDensity_apply _ hs] using hm s
  filter_upwards [he, hnf, hnh] with x hx hfx hhx
  have ht := ENNReal.toReal_mono (by simp) hx
  simpa only [ENNReal.toReal_ofReal hfx, ENNReal.toReal_ofReal hhx] using ht

/-- The Radon–Nikodym representative is an actual density of an absolutely continuous Radon
measure. -/
theorem bellman_rnDeriv_density (F : Measure ℝ) [IsFiniteMeasureOnCompacts F]
    (hF : F ≪ volume) :
    F = volume.withDensity (fun x => ENNReal.ofReal ((F.rnDeriv volume x).toReal)) := by
  calc
    F = volume.withDensity (F.rnDeriv volume) :=
      (Measure.withDensity_rnDeriv_eq F volume hF).symm
    _ = _ := by
      apply withDensity_congr_ae
      filter_upwards [Measure.rnDeriv_lt_top F volume] with x hx
      exact (ENNReal.ofReal_toReal hx.ne).symm

/-- A weighted measure primitive becomes a literal moment of its Radon–Nikodym density. -/
theorem bellmanMeasurePrimitive_eq_rnMoment (F : Measure ℝ) [IsFiniteMeasureOnCompacts F]
    (hF : F ≪ volume) (g : ℝ → ℝ) (y : ℝ) :
    bellmanMeasurePrimitive F g 0 y =
      ∫ z in 0..y, g z * (F.rnDeriv volume z).toReal := by
  dsimp [bellmanMeasurePrimitive]
  rcases le_total (0 : ℝ) y with hy | hy
  · rw [intervalIntegral.integral_of_le hy, intervalIntegral.integral_of_le hy]
    rw [show (fun z => g z * (F.rnDeriv volume z).toReal) =
      (fun z => (F.rnDeriv volume z).toReal * g z) by funext z; ring]
    exact (setIntegral_toReal_rnDeriv_mul hF measurableSet_Ioc).symm
  · rw [intervalIntegral.integral_of_ge hy, intervalIntegral.integral_of_ge hy]
    congr 1
    rw [show (fun z => g z * (F.rnDeriv volume z).toReal) =
      (fun z => (F.rnDeriv volume z).toReal * g z) by funext z; ring]
    exact (setIntegral_toReal_rnDeriv_mul hF measurableSet_Ioc).symm

end HypoellipticAleksandrov.KineticAleksandrov
