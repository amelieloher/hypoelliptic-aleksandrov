module

public import HypoellipticAleksandrov.Parabolic.Scaling
public import HypoellipticAleksandrov.Parabolic.LocalHarnackGeometry

/-!
# Endpoint continuity for the local parabolic Harnack box

This module transports closed-box scalar continuity through the normalized
parabolic affine map and records the resulting terminal-face limit.
-/

@[expose] public section

open Filter Set

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

/-- Continuous scalar data pulls back along a parabolic affine map when the
map sends the new domain into the old domain. -/
theorem ContinuousOn.pullbackScalar {d : ℕ} {q : TimeVelocity d → ℝ}
    {U V : Set (TimeVelocity d)} {t0 r : ℝ} {v0 : PDE.Vec d}
    (hq : ContinuousOn q U)
    (hmap : MapsTo (parabolicAffine t0 v0 r) V U) :
    ContinuousOn (pullbackScalar q t0 v0 r) V := by
  change ContinuousOn (fun x => q (parabolicAffine t0 v0 r x)) V
  exact
    hq.comp (contDiff_parabolicAffine t0 v0 r).continuous.continuousOn hmap

/-- Closed physical Harnack-box continuity pulls back to closed normalized-box
continuity. -/
theorem ContinuousOn.pullbackScalar_localHarnackClosedBox
    {d : ℕ} {q : TimeVelocity d → ℝ} {t0 r : ℝ} {v0 : PDE.Vec d}
    (hq : ContinuousOn q (parabolicClosedBox 2 r (t0 - r ^ 2) v0))
    (hr : 0 < r) :
    ContinuousOn (HypoellipticAleksandrov.Parabolic.pullbackScalar q (t0 - r ^ 2) v0 (r / 2))
      (parabolicClosedBox 2 2 0 0) := by
  have hmap : MapsTo (parabolicAffine (t0 - r ^ 2) v0 (r / 2))
      (parabolicClosedBox 2 2 0 0)
      (parabolicClosedBox 2 r (t0 - r ^ 2) v0) := by
    rw [← parabolicAffine_preimage_localHarnackClosedBox hr]
    exact mapsTo_preimage _ _
  exact ContinuousOn.pullbackScalar hq hmap

/-- Continuity within the normalized closed Harnack box gives the terminal-face
limit along the interior-time approximation. -/
theorem ContinuousOn.tendsto_localHarnackTerminalApprox
    {d : ℕ} {q : TimeVelocity d → ℝ} {v : PDE.Vec d}
    (hq : ContinuousOn q (parabolicClosedBox 2 2 0 0))
    (hv : v ∈ velocityCube (0 : PDE.Vec d) 1) :
    Tendsto (fun j : ℕ => q (localHarnackTerminalApprox j, v)) atTop
      (_root_.nhds (q (8, v))) := by
  let K : Set (TimeVelocity d) := parabolicClosedBox 2 2 0 0
  let zj : ℕ → TimeVelocity d := fun j => (localHarnackTerminalApprox j, v)
  have hzj : Tendsto zj atTop (_root_.nhds (8, v)) := by
    exact HypoellipticAleksandrov.Parabolic.tendsto_localHarnackTerminalApprox.prodMk_nhds
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => v) atTop (_root_.nhds v))
  have hzjMem : ∀ j : ℕ, zj j ∈ K := by
    intro j
    have hj := localHarnackTerminalApprox_mem_normalizedOpenBox (v := v) j hv
    rw [mem_parabolicBox_iff] at hj
    rw [mem_parabolicClosedBox_iff]
    exact ⟨hj.1.le, hj.2.1.le, fun i => (hj.2.2 i).le⟩
  have hzjWithin : Tendsto zj atTop (_root_.nhdsWithin (8, v) K) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within zj hzj
      (Eventually.of_forall hzjMem)
  have hterminal : (8, v) ∈ K :=
    normalized_terminal_target_mem_normalizedClosedBox hv
  simpa only [Function.comp_def, zj] using
    (hq (8, v) hterminal).tendsto.comp hzjWithin

end

end HypoellipticAleksandrov.Parabolic
