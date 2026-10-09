module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularAnnihilationNegativeMoments
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularAnnihilationTailReflection
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularPositiveTailGrowth
import Mathlib.Tactic

/-! # Vanishing of negative angular moments and densities -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set Filter
open scoped Topology

/-- Finite tails force every negative first moment to vanish once the value and flux at zero
vanish. -/
theorem bellmanAngularFirstMoment_negative_zero (R β : ℝ) (hR : 1 ≤ R) (hβ : 3 ≤ β)
    (f h J : ℝ → ℝ) (hf : LocallyIntegrable f volume)
    (hn : ∀ᵐ z ∂volume, 0 ≤ f z) (hcomp : ∀ᵐ y ∂volume, h y ≤ R * f y)
    (h0 : h 0 = 0) (hj0 : J 0 = 0)
    (he : ∀ y : ℝ, h y = h 0 + J 0 * y - ((β - 2) / 3) * y *
      bellmanAngularFirstMoment f y + ((β - 3) / 3) * bellmanAngularSecondMoment f y)
    (htail : IntegrableOn (fun y => f y * |y| ^ (β - 4)) {y : ℝ | 2 < |y|} volume) :
    ∀ a : ℝ, a < 0 → bellmanAngularFirstMoment f a = 0 := by
  intro a ha
  have hnI := bellmanAngularFirstMoment_nonneg_negative hn ha.le
  by_contra hne
  have hIp : 0 < bellmanAngularFirstMoment f a := lt_of_le_of_ne hnI (Ne.symm hne)
  have hRp : 0 < R := by linarith
  let b := max 2 (-a)
  have hb : 2 ≤ b := le_max_left _ _
  have hc : 0 < bellmanAngularFirstMoment f a / (3 * R) := div_pos hIp (by positivity)
  apply bellmanAngularTail_not_power_lower_bound (fun y => f (-y)) β b
    (bellmanAngularFirstMoment f a / (3 * R)) (β - 3)
    (bellmanAngularTail_reflect β f htail) hb hc (by linarith)
  have href := bellmanAngularComparison_reflect R f h hcomp
  filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae href] with y hy hcy
  have hyp : 0 < y := by have : 2 < y := hb.trans_lt hy; linarith
  have hya : -y ≤ a := by have := (le_max_right 2 (-a)).trans hy.le; linarith
  have hm := bellmanAngularFirstMoment_negative_mono hf hn (-y) a hya ha.le
  have hl := bellmanAngularDensity_negative_lower β f h J hβ hf hn h0 hj0 he (-y)
    (by linarith)
  have hfy : (bellmanAngularFirstMoment f a / (3 * R)) * y ≤ f (-y) := by
    have hm' := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ y / 3)
    simp only [neg_neg] at hl
    have hl' : (y / 3) * bellmanAngularFirstMoment f a ≤ h (-y) := by
      simpa only [neg_neg] using hm'.trans hl
    apply le_of_mul_le_mul_left (a := R) _ hRp
    have heq : R * ((bellmanAngularFirstMoment f a / (3 * R)) * y) =
        (y / 3) * bellmanAngularFirstMoment f a := by field_simp
    rw [heq]
    exact hl'.trans hcy
  have hm := mul_le_mul_of_nonneg_right hfy (Real.rpow_nonneg hyp.le (β - 4))
  have hp : y * y ^ (β - 4) = y ^ (β - 3) := by
    calc
      y * y ^ (β - 4) = y ^ (1 : ℝ) * y ^ (β - 4) := by rw [Real.rpow_one]
      _ = y ^ (1 + (β - 4)) := (Real.rpow_add hyp _ _).symm
      _ = y ^ (β - 3) := by congr 1; ring
  calc
    (bellmanAngularFirstMoment f a / (3 * R)) * y ^ (β - 3) =
        ((bellmanAngularFirstMoment f a / (3 * R)) * y) * y ^ (β - 4) := by
      rw [mul_assoc, hp]
    _ ≤ _ := hm

/-- A vanishing first moment on the negative half-line forces its density to vanish there. -/
theorem bellmanAngularDensity_negative_zero (f : ℝ → ℝ)
    (hf : LocallyIntegrable f volume)
    (hz : ∀ y : ℝ, y < 0 → bellmanAngularFirstMoment f y = 0) :
    ∀ᵐ y ∂volume.restrict (Iio 0), f y = 0 := by
  have hi : LocallyIntegrable (fun z => z * f z) volume := by
    simpa only [pow_one] using bellman_polynomial_locallyIntegrable f hf 1
  have hd := _root_.LocallyIntegrable.ae_hasDerivAt_integral hi
  filter_upwards [ae_restrict_of_ae hd, ae_restrict_mem measurableSet_Iio] with y hdy hy
  have he : bellmanAngularFirstMoment f =ᶠ[𝓝 y] (fun _ => 0) := by
    filter_upwards [isOpen_Iio.mem_nhds hy] with z hz'
    exact hz z hz'
  have heder := he.deriv_eq
  rw [deriv_const] at heder
  have hder : deriv (bellmanAngularFirstMoment f) y = y * f y := (hdy 0).deriv
  rw [hder] at heder
  exact (mul_eq_zero.mp heder).resolve_left hy.ne

end HypoellipticAleksandrov.KineticAleksandrov
