module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.MacroscopicPropagationCorridor
import Mathlib.Tactic

/-! # Source cap centers and exact endpoints of physical reference paths -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth

open Set

/-- The literal cap-center point has strict margins in the source cap. -/
theorem reference_cap_center_mem (d : ℕ) :
    (⟨-(3 / 16 : ℝ), 0, 0⟩ : KineticPoint d) ∈ cap d := by
  norm_num [cap, PDE.euclideanBall, PDE.vecEuclideanNorm, PDE.vecNormSq, PDE.vecDot]

/-- The cap-center affine image is exactly the source propagation start. -/
theorem cap_center_affine {d : ℕ} (P : KineticPoint d) (r : ℝ) :
    kineticAffine P r (⟨-(3 / 16 : ℝ), 0, 0⟩ : KineticPoint d) =
      ⟨stackStartTime P r, stackStartPosition P r, P.velocity⟩ := by
  ext i
  all_goals simp only [kineticAffine, stackStartTime, stackStartPosition,
    smul_zero, add_zero, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  all_goals ring

/-- Every sampling subcylinder's cap center is a valid reference-path start. -/
theorem sampling_cap_center_mem {d : ℕ} (m : ℕ) (P : KineticPoint d) {r : ℝ}
    (hr : 0 < r) (hsub : backwardCylinder P r ⊆ samplingCylinder d m) :
    (⟨stackStartTime P r, stackStartPosition P r, P.velocity⟩ : KineticPoint d) ∈
      closure (samplingCylinder d m) := by
  apply subset_closure
  apply hsub
  rw [← cap_center_affine P r]
  apply (kineticAffine_mem_cylinder P _ hr).mpr
  exact (closedCap_subset_unitCylinder d) (cap_subset_closedCap d (reference_cap_center_mem d))

/-- The physical image of an initial tangent is the tangent at the physical initial point. -/
theorem physicalPath_initial_tangent {d : ℕ} (P0 S : KineticPoint d) {scale : ℝ}
    (hscale : 0 < scale) (x v : ℝ → PDE.Vec d)
    (hleft : ∀ s ≤ 0, x s = S.position + s • S.velocity ∧ v s = S.velocity)
    (s : ℝ) (hs : s ≤ 0) :
    physicalPathPosition P0 scale S.time x s =
        (kineticAffine P0 scale S).position + s • (kineticAffine P0 scale S).velocity ∧
      physicalPathVelocity P0 scale v s = (kineticAffine P0 scale S).velocity := by
  have he := hleft (s / scale ^ 2) (div_nonpos_of_nonpos_of_nonneg hs (sq_nonneg scale))
  constructor
  · unfold physicalPathPosition
    rw [he.1]
    ext i
    simp only [kineticAffine, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  · unfold physicalPathVelocity
    rw [he.2]
    rfl

/-- Transported path endpoints match the affine target exactly. -/
theorem physicalPath_endpoint {d : ℕ} (P0 S P : KineticPoint d) {scale : ℝ}
    (hscale : scale ≠ 0) (x v : ℝ → PDE.Vec d)
    (hx : x (P.time - S.time) = P.position) (hv : v (P.time - S.time) = P.velocity) :
    physicalPathPosition P0 scale S.time x (scale ^ 2 * (P.time - S.time)) =
        (kineticAffine P0 scale P).position ∧
      physicalPathVelocity P0 scale v (scale ^ 2 * (P.time - S.time)) =
        (kineticAffine P0 scale P).velocity := by
  have ht : (scale ^ 2 * (P.time - S.time)) / scale ^ 2 = P.time - S.time := by
    field_simp
  constructor
  · unfold physicalPathPosition
    rw [ht, hx]
    ext i
    simp only [kineticAffine, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · unfold physicalPathVelocity
    rw [ht, hv]
    rfl

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth
