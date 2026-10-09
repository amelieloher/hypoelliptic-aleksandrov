module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.MacroscopicPropagationEndpoints
import Mathlib.Tactic

/-! # Initial cap comparison for physically transported reference corridors -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth

open Set

/-- Affine composition identifies the physical source cap center without coordinate changes. -/
theorem physical_cap_center {d : ℕ} (P0 P : KineticPoint d) (scale r : ℝ) :
    kineticAffine P0 scale
        (⟨stackStartTime P r, stackStartPosition P r, P.velocity⟩ : KineticPoint d) =
      ⟨stackStartTime (kineticAffine P0 scale P) (scale * r),
        stackStartPosition (kineticAffine P0 scale P) (scale * r),
        (kineticAffine P0 scale P).velocity⟩ := by
  rw [← cap_center_affine P r]
  have hc := congrFun (kineticAffine_comp P0 P scale r)
    (⟨-(3 / 16 : ℝ), 0, 0⟩ : KineticPoint d)
  exact hc.trans (cap_center_affine _ _)

/-- The fixed macroscopic initial tube is contained in the cap of any larger sampling radius. -/
theorem macroscopic_initial_subset_cap {d : ℕ} (P0 P : KineticPoint d)
    {scale r0 r : ℝ} (hscale : 0 < scale) (hr0 : 0 < r0) (hr : r0 ≤ r)
    (x v : ℝ → PDE.Vec d)
    (hleft : ∀ s ≤ 0,
      x s = stackStartPosition P r + s • P.velocity ∧ v s = P.velocity) :
    corridor (kineticAffine P0 scale
        (⟨stackStartTime P r, stackStartPosition P r, P.velocity⟩ : KineticPoint d)).time
      (-((r0 ^ 2 / 32) * scale ^ 2)) 0 ((r0 ^ 3 / 1024) * scale ^ 3)
      ((r0 / 16) * scale)
      (physicalPathPosition P0 scale (stackStartTime P r) x)
      (physicalPathVelocity P0 scale v) ⊆
      kineticAffine (kineticAffine P0 scale P) (scale * r) '' cap d := by
  let S : KineticPoint d := ⟨stackStartTime P r, stackStartPosition P r, P.velocity⟩
  have hc := physical_cap_center P0 P scale r
  have ht := congrArg KineticPoint.time hc
  have hx := congrArg KineticPoint.position hc
  have hv := congrArg KineticPoint.velocity hc
  have hrp : 0 < r := hr0.trans_le hr
  have hsq : r0 ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hr0.le hr 2
  have hcube : r0 ^ 3 ≤ r ^ 3 := pow_le_pow_left₀ hr0.le hr 3
  have hleft' (s : ℝ) (hs : s ≤ 0) :=
    physicalPath_initial_tangent P0 S hscale x v hleft s hs
  have hinc := initial_corridor_subset_cap (kineticAffine P0 scale P)
    (mul_pos hscale hrp)
    (physicalPathPosition P0 scale S.time x) (physicalPathVelocity P0 scale v)
    (fun s hs => by simpa only [S, hx, hv] using hleft' s hs)
  rw [ht]
  apply Subset.trans _ hinc
  apply corridor_mono
  · rw [mul_pow]
    nlinarith [mul_le_mul_of_nonneg_right hsq (sq_nonneg scale)]
  · exact le_rfl
  · rw [mul_pow]
    norm_num
    nlinarith [mul_le_mul_of_nonneg_right hcube (pow_nonneg hscale.le 3)]
  · nlinarith [mul_le_mul_of_nonneg_left hr hscale.le]

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth
