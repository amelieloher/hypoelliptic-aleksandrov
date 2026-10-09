module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.StackCorridorsGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.SkeletonApproximation
import Mathlib.Tactic

/-! # Tangent-extended Hermite paths with uniform stack bounds -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth
open Set

/-- Increasing the acceleration bound preserves a skeleton. -/
theorem skeleton_mono_bound {d : ℕ} {x v : ℝ → PDE.Vec d} {H K a b : ℝ}
    (hx : IsSkeleton x v H a b) (hHK : H ≤ K) : IsSkeleton x v K a b :=
  ⟨hx.1, hx.2.1, fun s hs t ht => (hx.2.2 s hs t ht).trans
    (mul_le_mul_of_nonneg_right hHK (abs_nonneg _))⟩

/-- The cap-center free-transport displacement equals the path displacement. -/
theorem stack_relative_path {d : ℕ} (P0 : KineticPoint d) (r s : ℝ)
    (z : PDE.Vec d) :
    z-P0.position-(stackStartTime P0 r+s-P0.time) • P0.velocity =
      z-stackStartPosition P0 r-s • P0.velocity := by
  ext i
  simp only [stackStartTime, stackStartPosition, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- A stack endpoint admits a tangent-extended skeleton with uniform path bounds. -/
theorem exists_stack_path {d : ℕ} (P0 P : KineticPoint d) {r : ℝ} (hr : 0 < r)
    (m : ℕ) (hP : P ∈ forwardStack P0 r m) :
    ∃ x v : ℝ → PDE.Vec d,
      IsSkeleton x v (stackAcceleration m/r) (-(r^2/32)) (stackTravelTime P0 P r) ∧
      x 0 = stackStartPosition P0 r ∧ v 0 = P0.velocity ∧
      x (stackTravelTime P0 P r) = P.position ∧
      v (stackTravelTime P0 P r) = P.velocity ∧
      (∀ s ≤ 0, x s = stackStartPosition P0 r+s • P0.velocity ∧ v s = P0.velocity) ∧
      (∀ s ∈ Icc (-(r^2/32)) (stackTravelTime P0 P r),
        PDE.vecEuclideanNorm (x s-stackStartPosition P0 r-s • P0.velocity) ≤
          stackPathBound m*r^3 ∧
        PDE.vecEuclideanNorm (v s-P0.velocity) ≤ stackPathBound m*r) := by
  obtain ⟨hlo, hhi, hpos, hvel⟩ := stack_endpoint_data P0 P hr m hP
  let T := stackTravelTime P0 P r
  have hT : 0 < T := lt_of_lt_of_le (by positivity) hlo
  let xh := hermitePosition T (stackStartPosition P0 r) P0.velocity P.position P.velocity
  let vh := hermiteVelocity T (stackStartPosition P0 r) P0.velocity P.position P.velocity
  let H := 6*PDE.vecEuclideanNorm
    (P.position-stackStartPosition P0 r-T • P0.velocity)/T^2+
    4*PDE.vecEuclideanNorm (P.velocity-P0.velocity)/T
  have hsk : IsSkeleton xh vh H 0 T := hermite_isSkeleton hT _ _ _ _
  have hH : 0 ≤ H := by
    have hn₁ := PDE.vecEuclideanNorm_nonneg
      (P.position-stackStartPosition P0 r-T • P0.velocity)
    have hn₂ := PDE.vecEuclideanNorm_nonneg (P.velocity-P0.velocity)
    dsimp [H]
    positivity
  let x := extendPosition xh vh 0 T hT.le
  let v := extendVelocity vh 0 T hT.le
  have hleft (s : ℝ) (hs : s ≤ 0) :
      x s = stackStartPosition P0 r+s • P0.velocity ∧ v s = P0.velocity := by
    constructor
    · dsimp [x]
      rw [extendPosition_left xh vh hT.le hs]
      simp only [xh, vh, hermitePosition_zero, hermiteVelocity_zero, sub_zero]
    · dsimp [v, extendVelocity]
      rw [projIcc_of_le_left hT.le hs]
      exact hermiteVelocity_zero _ _ _ _ _
  refine ⟨x, v, skeleton_mono_bound
    (extendPosition_isSkeleton hT.le hH hsk _ _)
    (stack_hermite_acceleration hr m hlo _ _ _ _ hpos hvel),
    (by simpa using (hleft 0 le_rfl).1), (hleft 0 le_rfl).2, ?_, ?_, hleft, ?_⟩
  · dsimp [x]
    rw [extendPosition_eq hT.le hsk (right_mem_Icc.mpr hT.le)]
    exact hermitePosition_end hT.ne' _ _ _ _
  · dsimp [v]
    rw [extendVelocity_eq vh hT.le (right_mem_Icc.mpr hT.le)]
    exact hermiteVelocity_end hT.ne' _ _ _ _
  · intro s hs
    by_cases h : s ≤ 0
    · rw [(hleft s h).1, (hleft s h).2]
      simp only [add_sub_cancel_left, sub_self]
      rw [PDE.vecEuclideanNorm_eq_zero_iff.mpr rfl]
      constructor <;> dsimp [stackPathBound] <;> positivity
    · have hs' : s ∈ Icc 0 T := ⟨(not_le.mp h).le, hs.2⟩
      dsimp [x, v]
      rw [extendPosition_eq hT.le hsk hs', extendVelocity_eq vh hT.le hs']
      exact stack_hermite_bounds hr m hlo hhi _ _ _ _ hpos hvel hs'

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth
