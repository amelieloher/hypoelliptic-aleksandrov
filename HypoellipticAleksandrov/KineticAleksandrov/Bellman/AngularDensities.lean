module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDensitiesFlux
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDensitiesMoments
import Mathlib.Tactic

/-! # Actual absolutely continuous densities of the angular adjoint measures -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- The angular weak equation and ellipticity produce densities and a locally AC flux. -/
theorem angular_has_densities (R β : ℝ) (hR : 1 ≤ R) (F H : Measure ℝ)
    (hang : IsBellmanAngularAdjointPair 1 R β F H) :
    ∃ f h J : ℝ → ℝ,
      F = volume.withDensity (fun y => ENNReal.ofReal (f y)) ∧
      H = volume.withDensity (fun y => ENNReal.ofReal (h y)) ∧
      LocallyIntegrable f volume ∧ (∀ᵐ y ∂volume, 0 ≤ f y) ∧
      (∀ a b : ℝ, a ≤ b → AbsolutelyContinuousOnInterval h a b) ∧
      (∀ a b : ℝ, a ≤ b → AbsolutelyContinuousOnInterval J a b) ∧
      (∀ᵐ y ∂volume, f y ≤ h y ∧ h y ≤ R * f y) ∧
      (∀ᵐ y ∂volume, deriv h y = J y - y ^ 2 * f y / 3) ∧
      (∀ᵐ y ∂volume, deriv J y = -(β - 2) / 3 * y * f y) := by
  let : IsFiniteMeasureOnCompacts F := hang.1
  let : IsFiniteMeasureOnCompacts H := hang.2.2.1
  obtain ⟨j, hj⟩ := bellmanAngularFlux_weak R β F H hang
  let A := bellmanMeasurePrimitive F id 0
  let J := fun x => j - ((β - 2) / 3) * A x
  have hA : LocallyIntegrable A volume :=
    bellmanMeasurePrimitive_locallyIntegrable F id continuous_id
  have hJ : LocallyIntegrable J volume := by
    convert! (continuous_const : Continuous (fun _ : ℝ => j)).locallyIntegrable.sub
      (hA.smul ((β - 2) / 3)) using 1
  obtain ⟨c, hH, hnH⟩ := bellman_measure_density_of_flux F H (fun x => x ^ 2) J
    (continuous_id.pow 2) hJ (1 / 3) hj
  let h := fun x => c + (∫ z in 0..x, J z) -
    (1 / 3 : ℝ) * bellmanMeasurePrimitive F (fun z => z ^ 2) 0 x
  have hFH : F ≤ H := by simpa only [ENNReal.ofReal_one, one_smul] using hang.2.2.2.2.1
  have hFvol : F ≪ volume := hFH.absolutelyContinuous.trans (by
    rw [hH]; exact withDensity_absolutelyContinuous _ _)
  let f := fun x => (F.rnDeriv volume x).toReal
  have hfm : Measurable f := (Measure.measurable_rnDeriv F volume).ennreal_toReal
  have hf : LocallyIntegrable f volume := bellman_rnDeriv_locallyIntegrable F volume
  have hfn : ∀ᵐ x ∂volume, 0 ≤ f x := ae_of_all _ fun _ => ENNReal.toReal_nonneg
  have hF : F = volume.withDensity (fun x => ENNReal.ofReal (f x)) :=
    bellman_rnDeriv_density F hFvol
  have hJeq : J = fun y => j - ((β - 2) / 3) * (∫ z in 0..y, z * f z) := by
    funext y
    dsimp [J, A]
    rw [bellmanMeasurePrimitive_eq_rnMoment F hFvol]
    rfl
  have hheq : h = fun y => c + (∫ z in 0..y, J z) -
      (1 / 3 : ℝ) * (∫ z in 0..y, z ^ 2 * f z) := by
    funext y
    dsimp [h]
    rw [bellmanMeasurePrimitive_eq_rnMoment F hFvol]
  have hhac : ∀ a b : ℝ, a ≤ b → AbsolutelyContinuousOnInterval h a b := by
    intro a b hab
    rw [hheq]
    convert! ((bellman_const_locallyAC c a b).add
      (bellman_lebesguePrimitive_locallyAC J hJ a b hab)).sub
      ((bellman_moment_locallyAC f hf 2 a b hab).const_mul (1 / 3)) using 1
  have hJac : ∀ a b : ℝ, a ≤ b → AbsolutelyContinuousOnInterval J a b := by
    intro a b hab
    rw [hJeq]
    have hi : LocallyIntegrable (fun x => x * f x) volume := by
      simpa only [pow_one] using bellman_polynomial_locallyIntegrable f hf 1
    convert! (bellman_const_locallyAC j a b).sub
      ((bellman_lebesguePrimitive_locallyAC _ hi a b hab).const_mul ((β - 2) / 3)) using 1
  have hhm : Measurable h := (bellman_locallyAC_continuous hhac).measurable
  have hhn : ∀ᵐ x ∂volume, 0 ≤ h x := hnH
  have hfH : ∀ᵐ x ∂volume, f x ≤ h x :=
    bellman_density_le_of_measure_le f h hfm hfn hhn (by rw [← hF, ← hH]; exact hFH)
  have hRf : ∀ᵐ x ∂volume, 0 ≤ R * f x := by
    filter_upwards [hfn] with x hx
    exact mul_nonneg (by linarith) hx
  have hHR : ∀ᵐ x ∂volume, h x ≤ R * f x := by
    apply bellman_density_le_of_measure_le h (fun x => R * f x) hhm hhn hRf
    have he : volume.withDensity (fun x => ENNReal.ofReal (R * f x)) =
        ENNReal.ofReal R • F := by
      rw [show (fun x => ENNReal.ofReal (R * f x)) =
        ENNReal.ofReal R • (fun x => ENNReal.ofReal (f x)) by
          funext x; exact ENNReal.ofReal_mul (by linarith),
        withDensity_smul _ hfm.ennreal_ofReal, ← hF]
    rw [← hH, he]
    exact hang.2.2.2.2.2.1
  refine ⟨f, h, J, hF, hH, hf, hfn, hhac, hJac, ?_, ?_, ?_⟩
  · filter_upwards [hfH, hHR] with x hx hy
    exact ⟨hx, hy⟩
  · rw [hheq]
    exact bellman_momentDensity_deriv f J hf hJ c
  · rw [hJeq]
    filter_upwards [bellman_momentFlux_deriv f hf j ((β - 2) / 3)] with x hx
    rw [hx]
    ring

end HypoellipticAleksandrov.KineticAleksandrov
