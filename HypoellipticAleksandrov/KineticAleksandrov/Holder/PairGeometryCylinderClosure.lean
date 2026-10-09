module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.AffineGeometryTopology
import Mathlib.Tactic

/-! # Weak Euclidean coordinate bounds characterize source-cylinder closure -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Set

/-- Every point satisfying the weak unit bounds is an explicit limit of interior points. -/
theorem mem_closure_unitCylinder_of_bounds {d : ℕ} (P : KineticPoint d)
    (htlo : -1 ≤ P.time) (hthi : P.time ≤ 0)
    (hx : PDE.vecEuclideanNorm P.position ≤ 1)
    (hv : PDE.vecEuclideanNorm P.velocity ≤ 1) :
    P ∈ closure (backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1) := by
  let f : ℝ → KineticPoint d := fun e =>
    ⟨(1 - e) * P.time - e / 2, (1 - e) • P.position, (1 - e) • P.velocity⟩
  have hf : Continuous f := KineticPoint.continuous_mk
    ((continuous_const.sub continuous_id).mul continuous_const |>.sub
      (continuous_id.div_const 2))
    ((continuous_const.sub continuous_id).smul continuous_const)
    ((continuous_const.sub continuous_id).smul continuous_const)
  have hsub : f '' Ioo 0 1 ⊆ backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1 := by
    rintro Z ⟨e, he, rfl⟩
    have he1 : 0 < 1 - e := sub_pos.mpr he.2
    refine ⟨?_, ?_, ?_, ?_⟩
    · change 0 - (1 : ℝ) ^ 2 < (1 - e) * P.time - e / 2
      norm_num only [one_pow, zero_sub]
      nlinarith only [mul_le_mul_of_nonneg_left htlo he1.le, he.1]
    · change (1 - e) * P.time - e / 2 < 0
      nlinarith only [mul_nonpos_of_nonneg_of_nonpos he1.le hthi, he.1]
    · apply (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt zero_lt_one).mpr
      change PDE.vecEuclideanNorm ((1 - e) • P.velocity - 0) < 1
      rw [sub_zero, PDE.vecEuclideanNorm_smul, abs_of_pos he1]
      nlinarith only [mul_le_mul_of_nonneg_left hv he1.le, he.1]
    · apply (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt
        (by norm_num : (0 : ℝ) < (1 : ℝ) ^ 3)).mpr
      change PDE.vecEuclideanNorm ((1 - e) • P.position - 0 -
        ((1 - e) * P.time - e / 2 - 0) • 0 - 0) < 1 ^ 3
      rw [smul_zero, sub_zero, sub_zero, sub_zero, PDE.vecEuclideanNorm_smul,
        abs_of_pos he1]
      norm_num only [one_pow]
      nlinarith only [mul_le_mul_of_nonneg_left hx he1.le, he.1]
  have hz : (0 : ℝ) ∈ closure (Ioo 0 1) := by
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact ⟨le_rfl, zero_le_one⟩
  have hp := closure_mono hsub
    (hf.continuousOn.image_closure (mem_image_of_mem f hz))
  simpa only [f, sub_zero, mul_one, one_mul, zero_div, one_smul] using hp

/-- Weak physical time, position and velocity bounds imply cylinder-closure membership. -/
theorem mem_closure_backwardCylinder_of_bounds {d : ℕ} (P0 P : KineticPoint d)
    {r : ℝ} (hr : 0 < r) (htlo : -(r ^ 2) ≤ P.time - P0.time)
    (hthi : P.time - P0.time ≤ 0)
    (hx : PDE.vecEuclideanNorm (relativePosition P0 P) ≤ r ^ 3)
    (hv : PDE.vecEuclideanNorm (relativeVelocity P0 P) ≤ r) :
    P ∈ closure (backwardCylinder P0 r) := by
  have hi : kineticAffineInverse P0 r P ∈
      closure (backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1) := by
    apply mem_closure_unitCylinder_of_bounds
    · change -1 ≤ (P.time - P0.time) / r ^ 2
      exact (le_div_iff₀ (pow_pos hr 2)).mpr (by simpa only [neg_one_mul] using htlo)
    · change (P.time - P0.time) / r ^ 2 ≤ 0
      exact div_nonpos_of_nonpos_of_nonneg hthi (sq_nonneg r)
    · change PDE.vecEuclideanNorm ((r ^ 3)⁻¹ • relativePosition P0 P) ≤ 1
      rw [PDE.vecEuclideanNorm_smul, abs_of_pos (inv_pos.mpr (pow_pos hr 3))]
      exact (mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr (pow_nonneg hr.le 3))).trans_eq
        (inv_mul_cancel₀ (pow_ne_zero 3 hr.ne'))
    · change PDE.vecEuclideanNorm (r⁻¹ • relativeVelocity P0 P) ≤ 1
      rw [PDE.vecEuclideanNorm_smul, abs_of_pos (inv_pos.mpr hr)]
      exact (mul_le_mul_of_nonneg_left hv (inv_nonneg.mpr hr.le)).trans_eq
        (inv_mul_cancel₀ hr.ne')
  have hc := (kineticAffineHomeomorph P0 r hr.ne').image_closure
    (backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1)
  change kineticAffine P0 r '' closure _ = closure (kineticAffine P0 r '' _) at hc
  rw [kineticAffine_image_unitCylinder P0 hr] at hc
  rw [← hc]
  exact ⟨kineticAffineInverse P0 r P, hi, kineticAffine_apply_inverse P0 hr.ne' P⟩

end HypoellipticAleksandrov.KineticAleksandrov.Holder
