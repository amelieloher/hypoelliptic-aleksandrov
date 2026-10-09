module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.MacroscopicPropagationScaling
import Mathlib.Tactic

/-! # Physical corridor inclusion derived from the reference corridor geometry -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth

open Set

/-- A transported unit-width corridor lies in the transported reference region. -/
theorem physical_corridor_subset_image {d : ℕ} (P0 : KineticPoint d) {scale : ℝ}
    (hscale : 0 < scale) (start T : ℝ) (x v : ℝ → PDE.Vec d)
    (G : Set (KineticPoint d)) (hcorr : corridor start (-1) T 1 1 x v ⊆ G) :
    corridor (P0.time + scale ^ 2 * start) (-(scale ^ 2)) (scale ^ 2 * T)
      (scale ^ 3) scale (physicalPathPosition P0 scale start x)
      (physicalPathVelocity P0 scale v) ⊆ kineticAffine P0 scale '' G := by
  intro Q hQ
  let s := Q.time - (P0.time + scale ^ 2 * start)
  let Z := kineticAffineInverse P0 scale Q
  have hs : Z.time - start = s / scale ^ 2 := by
    dsimp only [Z, s, kineticAffineInverse]
    field_simp
    ring
  have hx : Z.position - x (Z.time - start) =
      (scale ^ 3)⁻¹ • (Q.position - physicalPathPosition P0 scale start x s) := by
    rw [hs]
    ext i
    simp only [Z, kineticAffineInverse, physicalPathPosition, relativePosition,
      Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    dsimp only [s]
    field_simp
    ring
  have hv : Z.velocity - v (Z.time - start) =
      scale⁻¹ • (Q.velocity - physicalPathVelocity P0 scale v s) := by
    rw [hs]
    ext i
    simp only [Z, kineticAffineInverse, physicalPathVelocity, relativeVelocity,
      Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  apply (mem_kineticAffine_image_iff P0 Q hscale.ne' G).mpr
  apply hcorr
  refine ⟨?_, ?_, ?_⟩
  · rw [hs]
    constructor
    · apply (le_div_iff₀ (pow_pos hscale 2)).mpr
      simpa only [neg_one_mul] using hQ.1.1
    · exact (div_le_iff₀ (pow_pos hscale 2)).mpr
        (hQ.1.2.trans_eq (mul_comm (scale ^ 2) T))
  · rw [hx, PDE.vecEuclideanNorm_smul, abs_of_pos (inv_pos.mpr (pow_pos hscale 3))]
    have he := mul_le_mul_of_nonneg_left hQ.2.1
      (inv_nonneg.mpr (pow_nonneg hscale.le 3))
    exact he.trans_eq (inv_mul_cancel₀ (pow_ne_zero 3 hscale.ne'))
  · rw [hv, PDE.vecEuclideanNorm_smul, abs_of_pos (inv_pos.mpr hscale)]
    have he := mul_le_mul_of_nonneg_left hQ.2.2 (inv_nonneg.mpr hscale.le)
    exact he.trans_eq (inv_mul_cancel₀ hscale.ne')

/-- Smaller closed intervals and Euclidean widths preserve corridor inclusion. -/
theorem corridor_mono {d : ℕ} (tminus : ℝ) {a a' b b' kx kx' kv kv' : ℝ}
    (ha : a ≤ a') (hb : b' ≤ b) (hx : kx' ≤ kx) (hv : kv' ≤ kv)
    (x v : ℝ → PDE.Vec d) :
    corridor tminus a' b' kx' kv' x v ⊆ corridor tminus a b kx kv x v := by
  intro P hP
  exact ⟨⟨ha.trans hP.1.1, hP.1.2.trans hb⟩, hP.2.1.trans hx, hP.2.2.trans hv⟩

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth
