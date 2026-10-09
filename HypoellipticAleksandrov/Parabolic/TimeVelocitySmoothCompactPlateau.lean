module

public import HypoellipticAleksandrov.Parabolic.Geometry
public import Mathlib.Geometry.Manifold.SmoothApprox
public import Mathlib.Topology.UrysohnsLemma

/-!
# Smooth compact plateaus in time--velocity space

This file constructs a smooth compactly supported plateau on a positive closed
metric thickening of a compact subset of an open time--velocity carrier.
-/

@[expose] public section

open Metric Set
open scoped Topology

namespace HypoellipticAleksandrov.Parabolic

/-- A compact subset of an open time--velocity carrier has a smooth compact
plateau on a positive closed metric thickening. -/
theorem exists_contDiff_one_on_cthickening_tsupport_subset
    {d : ℕ} {U K : Set (TimeVelocity d)}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧
      ∃ b : TimeVelocity d → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) b ∧
          HasCompactSupport b ∧
          tsupport b ⊆ U ∧
          Set.EqOn b 1 (Metric.cthickening δ K) := by
  obtain ⟨r, hr, hrU⟩ := hK.exists_cthickening_subset_open hU hKU
  let δ : ℝ := r / 4
  let L : Set (TimeVelocity d) := Metric.cthickening (r / 2) K
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hL_compact : IsCompact L := by
    exact hK.cthickening
  have hLU : L ⊆ U := by
    exact (Metric.cthickening_mono (by linarith) K).trans hrU
  obtain ⟨f, hf_one, hf_compact, hfU, _⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hL_compact hU hLU
  let S : Set (TimeVelocity d) := Metric.cthickening δ K
  let N : Set (TimeVelocity d) := Metric.thickening δ S
  have hNS : N ∈ 𝓝ˢ S := by
    exact Metric.thickening_mem_nhdsSet S hδ
  have hNL : N ⊆ L := by
    intro z hz
    have hz' : z ∈ Metric.thickening (r / 4 + r / 4) K := by
      exact Metric.thickening_cthickening_subset (r / 4) (by positivity) K hz
    have hradius : r / 4 + r / 4 = r / 2 := by ring
    rw [hradius] at hz'
    dsimp [L]
    exact Metric.thickening_subset_cthickening (r / 2) K hz'
  have hf_smooth_on : ContDiffOn ℝ (⊤ : ℕ∞) (f : TimeVelocity d → ℝ) N := by
    apply (contDiff_const : ContDiff ℝ (⊤ : ℕ∞)
      (fun _ : TimeVelocity d => (1 : ℝ))).contDiffOn.congr
    intro z hz
    exact hf_one (hNL hz)
  obtain ⟨b, hb_smooth, _, hb_one, hb_support⟩ :=
    f.continuous.exists_contDiff_approx_and_eqOn (⊤ : ℕ∞)
      continuous_const (fun _ => one_pos) Metric.isClosed_cthickening hNS hf_smooth_on
  refine ⟨δ, hδ, b, hb_smooth, ?_, ?_, ?_⟩
  · exact HasCompactSupport.of_support_subset_isCompact hf_compact
      (hb_support.trans (subset_tsupport (f : TimeVelocity d → ℝ)))
  · exact (closure_mono hb_support).trans hfU
  · intro z hz
    apply (hb_one hz).trans
    apply hf_one
    change z ∈ Metric.cthickening (r / 2) K
    change z ∈ Metric.cthickening (r / 4) K at hz
    have hquarter : r / 4 ≤ r / 2 := by linarith
    exact Metric.cthickening_mono hquarter K hz

end HypoellipticAleksandrov.Parabolic
