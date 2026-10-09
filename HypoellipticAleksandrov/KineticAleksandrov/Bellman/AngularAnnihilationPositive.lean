module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularPositiveTail
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularAnnihilationOrigin
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic

/-! # Vanishing of the actual angular densities on the positive half-line -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set Filter
open scoped Topology

/-- At degree at least three, finite tails force the positive angular density and origin flux
to vanish. -/
theorem angular_positive_vanishes (R β : ℝ) (hR : 1 ≤ R) (hβ : 3 ≤ β)
    (F H : Measure ℝ) (f h J : ℝ → ℝ)
    (hd :
    F = volume.withDensity (fun y => ENNReal.ofReal (f y)) ∧
    H = volume.withDensity (fun y => ENNReal.ofReal (h y)) ∧
    LocallyIntegrable f volume ∧ (∀ᵐ y ∂volume, 0 ≤ f y) ∧
    (∀ a b : ℝ, a ≤ b → AbsolutelyContinuousOnInterval h a b) ∧
    (∀ a b : ℝ, a ≤ b → AbsolutelyContinuousOnInterval J a b) ∧
    (∀ᵐ y ∂volume, f y ≤ h y ∧ h y ≤ R * f y) ∧
    (∀ᵐ y ∂volume, deriv h y = J y - y ^ 2 * f y / 3) ∧
    (∀ᵐ y ∂volume, deriv J y = -(β - 2) / 3 * y * f y))
    (he : ∀ y : ℝ, h y = h 0 + J 0 * y - ((β - 2) / 3) * y *
      bellmanAngularFirstMoment f y + ((β - 3) / 3) * bellmanAngularSecondMoment f y)
    (htail : IntegrableOn (fun y => f y * |y| ^ (β - 4)) {y : ℝ | 2 < |y|} volume) :
    h 0 = 0 ∧ J 0 = 0 ∧ (∀ᵐ y ∂volume.restrict (Ioi 0), f y = 0) ∧
      (∀ y : ℝ, 0 < y → h y = 0) := by
  have hf := hd.2.2.1
  have hn := hd.2.2.2.1
  have hac := hd.2.2.2.2.1
  have hfh := hd.2.2.2.2.2.2.1.mono (fun _ hx => hx.1)
  have hcomp := hd.2.2.2.2.2.2.1.mono (fun _ hx => hx.2)
  have hh := bellmanAngularDensity_nonneg hac hn hfh
  obtain ⟨L, _, hI, _, hj, hlower⟩ :=
    angular_positive_tail_limit R β hR hβ F H f h J hd he htail
  have h0 := bellmanAngularDensity_zero_at_origin R β hR hβ f h (hh 0) hcomp hlower htail
  have hj0 := bellmanAngularFlux_zero_at_origin β f h J hf hn hh h0 he
  have hL0 : L = 0 := by
    have hc : 0 < (β - 2) / 3 := by linarith
    rw [hj0] at hj
    nlinarith
  have hi := bellmanAngularFirstMoment_integrable β f h J hβ hf hn hh he
  have htotal : (∫ z in Ioi 0, z * f z) = 0 := by
    have heq := tendsto_nhds_unique hI (bellmanAngularFirstMoment_tendsto f hi)
    linarith
  have hzn : ∀ᵐ z ∂volume.restrict (Ioi 0), 0 ≤ z * f z := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae hn] with z hz hnz
    exact mul_nonneg hz.le hnz
  have hz := (integral_eq_zero_iff_of_nonneg_ae hzn hi).mp htotal
  have hfzero : ∀ᵐ z ∂volume.restrict (Ioi 0), f z = 0 := by
    filter_upwards [hz, ae_restrict_mem measurableSet_Ioi] with z hz hpos
    exact (mul_eq_zero.mp hz).resolve_left hpos.ne'
  have hhzero : h =ᵐ[volume.restrict (Ioi 0)] (fun _ => 0) := by
    filter_upwards [hfzero, ae_restrict_of_ae hcomp] with z hz hc
    rw [hz, mul_zero] at hc
    exact le_antisymm hc (hh z)
  have heq := Measure.eqOn_open_of_ae_eq hhzero isOpen_Ioi
    (bellman_locallyAC_continuous hac).continuousOn continuous_const.continuousOn
  exact ⟨h0, hj0, hfzero, fun y hy => heq hy⟩

end HypoellipticAleksandrov.KineticAleksandrov
