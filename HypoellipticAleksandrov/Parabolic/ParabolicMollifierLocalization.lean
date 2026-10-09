module

public import Mathlib.Topology.MetricSpace.Thickening
public import HypoellipticAleksandrov.Parabolic.ParabolicMollifierKernel

/-!
# Localization for native-norm parabolic mollifiers

This module turns compact-in-open geometry into eventual support localization
for the right parabolic mollifier.  It uses only the native product
metric on `TimeVelocity d` and has no coefficient or PDE content.
-/

@[expose] public section

open Filter Set

namespace HypoellipticAleksandrov.Parabolic

/-- A compact subset of an open set admits a positive native-metric collar
that contains every sufficiently small mollifier scale. -/
theorem exists_native_kernel_collar
    (d : Nat) (K U : Set (TimeVelocity d))
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ delta : Real, 0 < delta ∧ Metric.cthickening delta K ⊆ U ∧
      ∀ᶠ n in Filter.atTop, parabolicMollifierScale n < delta := by
  obtain ⟨delta, hdelta_pos, hdeltaU⟩ := hK.exists_cthickening_subset_open hU hKU
  refine ⟨delta, hdelta_pos, hdeltaU, ?_⟩
  exact tendsto_parabolicMollifierScale_zero.eventually_lt_const hdelta_pos

/-- Eventually, every point sampled by the translated right mollifier at a
compact carrier lies in the surrounding open set. -/
theorem eventually_translated_parabolicMollifier_support_subset
    (d : Nat) (K U : Set (TimeVelocity d))
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∀ᶠ n in Filter.atTop, ∀ z ∈ K,
      {y | parabolicMollifier d n (z - y) ≠ 0} ⊆ U := by
  obtain ⟨delta, hdelta_pos, hdeltaU, hscale⟩ :=
    exists_native_kernel_collar d K U hK hU hKU
  filter_upwards [hscale] with n hn
  intro z hz y hy
  apply hdeltaU
  apply Metric.mem_cthickening_of_dist_le y z delta K hz
  have hySupport : z - y ∈ Function.support (parabolicMollifier d n) := hy
  rw [support_parabolicMollifier] at hySupport
  have hdist : dist y z < parabolicMollifierScale n := by
    rw [Metric.mem_ball] at hySupport
    simpa only [dist_eq_norm, sub_zero, norm_sub_rev] using hySupport
  exact (hdist.trans hn).le

end HypoellipticAleksandrov.Parabolic
