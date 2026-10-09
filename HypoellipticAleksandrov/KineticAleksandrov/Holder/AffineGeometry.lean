module

public import HypoellipticAleksandrov.KineticAleksandrov.Geometry
public import HypoellipticAleksandrov.Geometry.KineticPointMeasure
import Mathlib.Tactic

/-! # Inverse and composition of the source kinetic affine map -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Set

/-- The literal inverse in free-transport coordinates, for nonzero radius. -/
def kineticAffineInverse {d : ℕ} (P₀ : KineticPoint d) (R : ℝ) :
    KineticPoint d → KineticPoint d := fun P =>
  ⟨(P.time - P₀.time) / R ^ 2,
    (R ^ 3)⁻¹ • relativePosition P₀ P, R⁻¹ • relativeVelocity P₀ P⟩

/-- Kinetic dilation and Galilean translation compose in the source order. -/
theorem kineticAffine_comp {d : ℕ} (P₀ P : KineticPoint d) (R r : ℝ) :
    kineticAffine P₀ R ∘ kineticAffine P r =
      kineticAffine (kineticAffine P₀ R P) (R * r) := by
  funext Q
  ext i <;> simp [kineticAffine] <;> ring

/-- The literal inverse cancels the affine map. -/
theorem kineticAffineInverse_apply {d : ℕ} (P₀ : KineticPoint d) {R : ℝ}
    (hR : R ≠ 0) (P : KineticPoint d) :
    kineticAffineInverse P₀ R (kineticAffine P₀ R P) = P := by
  ext i
  all_goals simp [kineticAffineInverse, kineticAffine, relativePosition, relativeVelocity]
  all_goals field_simp
  all_goals ring

/-- The affine map cancels its literal inverse. -/
theorem kineticAffine_apply_inverse {d : ℕ} (P₀ : KineticPoint d) {R : ℝ}
    (hR : R ≠ 0) (P : KineticPoint d) :
    kineticAffine P₀ R (kineticAffineInverse P₀ R P) = P := by
  ext i <;>
    simp [kineticAffineInverse, kineticAffine, relativePosition, relativeVelocity] <;>
    field_simp <;> ring

/-- The affine coordinate map is continuous in the existing topology. -/
theorem continuous_kineticAffine {d : ℕ} (P₀ : KineticPoint d) (R : ℝ) :
    Continuous (kineticAffine P₀ R) := by
  have ht : Continuous (fun P : KineticPoint d => P.time) := continuous_time
  have hx : Continuous (fun P : KineticPoint d => P.position) := continuous_position
  have hv : Continuous (fun P : KineticPoint d => P.velocity) := continuous_velocity
  apply KineticPoint.continuous_mk
  · exact continuous_const.add (ht.const_mul (R ^ 2))
  · exact (continuous_const.add ((continuous_const (y := (R ^ 3 : ℝ))).smul hx)).add
      ((ht.const_mul (R ^ 2)).smul continuous_const)
  · exact continuous_const.add ((continuous_const (y := (R : ℝ))).smul hv)

/-- The inverse coordinate map is continuous in the existing topology. -/
theorem continuous_kineticAffineInverse {d : ℕ} (P₀ : KineticPoint d) (R : ℝ) :
    Continuous (kineticAffineInverse P₀ R) := by
  have ht : Continuous (fun P : KineticPoint d => P.time) := continuous_time
  have hx : Continuous (fun P : KineticPoint d => P.position) := continuous_position
  have hv : Continuous (fun P : KineticPoint d => P.velocity) := continuous_velocity
  apply KineticPoint.continuous_mk
  · exact (ht.sub continuous_const).div_const _
  · exact (continuous_const (y := ((R ^ 3)⁻¹ : ℝ))).smul ((hx.sub continuous_const).sub
      ((ht.sub continuous_const).smul continuous_const))
  · exact (continuous_const (y := (R⁻¹ : ℝ))).smul (hv.sub continuous_const)

/-- Nonzero kinetic affine maps are homeomorphisms. -/
def kineticAffineHomeomorph {d : ℕ} (P₀ : KineticPoint d) (R : ℝ) (hR : R ≠ 0) :
    KineticPoint d ≃ₜ KineticPoint d where
  toFun := kineticAffine P₀ R
  invFun := kineticAffineInverse P₀ R
  left_inv := kineticAffineInverse_apply P₀ hR
  right_inv := kineticAffine_apply_inverse P₀ hR
  continuous_toFun := continuous_kineticAffine P₀ R
  continuous_invFun := continuous_kineticAffineInverse P₀ R

/-- Membership in a source cylinder is transported from the unit cylinder. -/
theorem kineticAffine_mem_cylinder {d : ℕ} (P₀ P : KineticPoint d) {R : ℝ}
    (hR : 0 < R) :
    kineticAffine P₀ R P ∈ backwardCylinder P₀ R ↔
      P ∈ backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1 := by
  have hv := PDE.affine_mem_euclideanBall_iff_of_pos P₀.velocity P.velocity hR
  have hx := PDE.affine_mem_euclideanBall_iff_of_pos (0 : PDE.Vec d)
    P.position (pow_pos hR 3)
  simp only [mem_backwardCylinder_iff, kineticAffine_time, kineticAffine_velocity,
    relativePosition_kineticAffine, one_pow]
  simp only [relativePosition, sub_zero, smul_zero]
  rw [add_comm P₀.velocity, hv]
  simp only [add_zero] at hx
  rw [hx]
  have hR2 : 0 < R ^ 2 := sq_pos_of_pos hR
  constructor
  · rintro ⟨ha, hb, hv', hx'⟩
    refine ⟨?_, ?_, hv', hx'⟩ <;> nlinarith
  · rintro ⟨ha, hb, hv', hx'⟩
    refine ⟨?_, ?_, hv', hx'⟩ <;> nlinarith

/-- The kinetic affine image of the unit cylinder is the exact source cylinder. -/
theorem kineticAffine_image_unitCylinder {d : ℕ} (P₀ : KineticPoint d) {R : ℝ}
    (hR : 0 < R) :
    kineticAffine P₀ R '' backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1 =
      backwardCylinder P₀ R := by
  ext P
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    exact (kineticAffine_mem_cylinder P₀ Q hR).mpr hQ
  · intro hP
    refine ⟨kineticAffineInverse P₀ R P, ?_, kineticAffine_apply_inverse P₀ hR.ne' P⟩
    apply (kineticAffine_mem_cylinder P₀ _ hR).mp
    simpa only [kineticAffine_apply_inverse P₀ hR.ne' P] using hP

end HypoellipticAleksandrov.KineticAleksandrov.Holder
