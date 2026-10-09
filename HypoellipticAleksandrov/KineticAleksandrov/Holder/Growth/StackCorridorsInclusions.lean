module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.StackCorridorsPaths
import Mathlib.Tactic

/-! # Strict cap margins and uniform comparison-box containment -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth
open Set

/-- The initial tangent corridor lies in the source cap with strict spatial margins. -/
theorem initial_corridor_subset_cap {d : ℕ} (P0 : KineticPoint d) {r : ℝ}
    (hr : 0 < r) (x v : ℝ → PDE.Vec d)
    (hleft : ∀ s ≤ 0, x s = stackStartPosition P0 r+s • P0.velocity ∧
      v s = P0.velocity) :
    corridor (stackStartTime P0 r) (-(r^2/32)) 0 (r^3/(2*8^3)) (r/16) x v ⊆
      kineticAffine P0 r '' cap d := by
  intro Z hZ
  apply (mem_kineticAffine_image_iff P0 Z hr.ne' _).mpr
  have hl := hleft _ hZ.1.2
  have hrel : relativePosition P0 Z = Z.position-x (Z.time-stackStartTime P0 r) := by
    rw [hl.1]
    ext i
    simp only [relativePosition, stackStartTime, stackStartPosition, Pi.sub_apply,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hsq : 0 < r^2 := pow_pos hr 2
  have hcube : 0 < r^3 := pow_pos hr 3
  refine ⟨?_, ?_, ?_, ?_⟩
  · change -(1/4 : ℝ) < (Z.time-P0.time)/r^2
    apply (lt_div_iff₀ hsq).mpr
    have := hZ.1.1
    dsimp [stackStartTime] at this
    nlinarith
  · change (Z.time-P0.time)/r^2 < -(1/8 : ℝ)
    apply (div_lt_iff₀ hsq).mpr
    have := hZ.1.2
    dsimp [stackStartTime] at this
    nlinarith
  · apply (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).mpr
    rw [sub_zero, inverse_position_norm P0 Z hr, hrel]
    apply (div_lt_iff₀ hcube).mpr
    have := hZ.2.1
    norm_num at *
    nlinarith
  · apply (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).mpr
    rw [sub_zero, inverse_velocity_norm P0 Z hr]
    apply (div_lt_iff₀ hr).mpr
    have hv := hZ.2.2
    rw [hl.2] at hv
    linarith

/-- A uniformly bounded path corridor stays in the fixed comparison box. -/
theorem full_corridor_subset_comparison {d : ℕ} (P0 P : KineticPoint d) {r : ℝ}
    (hr : 0 < r) (m : ℕ) (hhi : stackTravelTime P0 P r ≤ ((m : ℝ)+1)*r^2)
    (x v : ℝ → PDE.Vec d)
    (hb : ∀ s ∈ Icc (-(r^2/32)) (stackTravelTime P0 P r),
      PDE.vecEuclideanNorm (x s-stackStartPosition P0 r-s • P0.velocity) ≤
        stackPathBound m*r^3 ∧
      PDE.vecEuclideanNorm (v s-P0.velocity) ≤ stackPathBound m*r) :
    corridor (stackStartTime P0 r) (-(r^2/32)) (stackTravelTime P0 P r)
      (r^3/(2*8^3)) (r/16) x v ⊆ kineticAffine P0 r '' stackComparisonRegion d m := by
  intro Z hZ
  apply (mem_kineticAffine_image_iff P0 Z hr.ne' _).mpr
  have hsq : 0 < r^2 := pow_pos hr 2
  have hcube : 0 < r^3 := pow_pos hr 3
  obtain ⟨hx, hv⟩ := hb _ hZ.1
  have hrel : relativePosition P0 Z =
      (Z.position-x (Z.time-stackStartTime P0 r))+
        (x (Z.time-stackStartTime P0 r)-stackStartPosition P0 r-
          (Z.time-stackStartTime P0 r) • P0.velocity) := by
    rw [← stack_relative_path]
    ext i
    simp only [relativePosition, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hn := PDE.vecEuclideanNorm_add_le
    (Z.position-x (Z.time-stackStartTime P0 r))
    (x (Z.time-stackStartTime P0 r)-stackStartPosition P0 r-
      (Z.time-stackStartTime P0 r) • P0.velocity)
  rw [← hrel] at hn
  have hvn := PDE.vecEuclideanNorm_add_le
    (Z.velocity-v (Z.time-stackStartTime P0 r))
    (v (Z.time-stackStartTime P0 r)-P0.velocity)
  rw [sub_add_sub_cancel] at hvn
  refine ⟨?_, ?_, ?_, ?_⟩
  · change -2 < (Z.time-P0.time)/r^2
    apply (lt_div_iff₀ hsq).mpr
    have := hZ.1.1
    dsimp [stackStartTime] at this
    nlinarith
  · change (Z.time-P0.time)/r^2 < (m : ℝ)+1
    apply (div_lt_iff₀ hsq).mpr
    have := hZ.1.2
    dsimp [stackStartTime] at this
    nlinarith
  · rw [inverse_position_norm P0 Z hr]
    apply (div_lt_iff₀ hcube).mpr
    have := hZ.2.1
    norm_num at this
    nlinarith only [hn, hx, this, hcube]
  · rw [inverse_velocity_norm P0 Z hr]
    apply (div_lt_iff₀ hr).mpr
    have := hZ.2.2
    nlinarith only [hvn, hv, this, hr]

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth
