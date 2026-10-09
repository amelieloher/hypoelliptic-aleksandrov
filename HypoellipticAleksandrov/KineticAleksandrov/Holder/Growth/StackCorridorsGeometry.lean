module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.StackCorridorsHermite
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.AffineGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Cap
import Mathlib.Tactic

/-! # Source corridor coordinates and the fixed stack comparison region -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth

open Set

/-- The cap-center start time in physical coordinates. -/
def stackStartTime {d : ℕ} (P0 : KineticPoint d) (r : ℝ) : ℝ := P0.time-3*r^2/16

/-- The cap-center start position in physical coordinates. -/
def stackStartPosition {d : ℕ} (P0 : KineticPoint d) (r : ℝ) : PDE.Vec d :=
  P0.position-(3*r^2/16) • P0.velocity

/-- Travel duration from the cap-center start to a prescribed stack endpoint. -/
def stackTravelTime {d : ℕ} (P0 P : KineticPoint d) (r : ℝ) : ℝ :=
  P.time-stackStartTime P0 r

/-- The fixed source comparison box for a chosen stack height. -/
def stackComparisonRegion (d m : ℕ) : Set (KineticPoint d) :=
  {P | -2 < P.time ∧ P.time < (m : ℝ)+1 ∧
    PDE.vecEuclideanNorm P.position < stackPathBound m+1 ∧
    PDE.vecEuclideanNorm P.velocity < stackPathBound m+1}

/-- Affine-image membership is inverse-coordinate membership. -/
theorem mem_kineticAffine_image_iff {d : ℕ} (P0 Z : KineticPoint d) {r : ℝ}
    (hr : r ≠ 0) (S : Set (KineticPoint d)) :
    Z ∈ kineticAffine P0 r '' S ↔ kineticAffineInverse P0 r Z ∈ S := by
  constructor
  · rintro ⟨Y, hY, rfl⟩
    rwa [kineticAffineInverse_apply P0 hr]
  · intro h
    exact ⟨kineticAffineInverse P0 r Z, h, kineticAffine_apply_inverse P0 hr Z⟩

/-- Native position norm in inverse affine coordinates. -/
theorem inverse_position_norm {d : ℕ} (P0 Z : KineticPoint d) {r : ℝ} (hr : 0 < r) :
    PDE.vecEuclideanNorm (kineticAffineInverse P0 r Z).position =
      PDE.vecEuclideanNorm (relativePosition P0 Z)/r^3 := by
  change PDE.vecEuclideanNorm ((r^3)⁻¹ • relativePosition P0 Z) = _
  rw [PDE.vecEuclideanNorm_smul, abs_of_pos (inv_pos.mpr (pow_pos hr 3))]
  ring

/-- Native velocity norm in inverse affine coordinates. -/
theorem inverse_velocity_norm {d : ℕ} (P0 Z : KineticPoint d) {r : ℝ} (hr : 0 < r) :
    PDE.vecEuclideanNorm (kineticAffineInverse P0 r Z).velocity =
      PDE.vecEuclideanNorm (Z.velocity-P0.velocity)/r := by
  change PDE.vecEuclideanNorm (r⁻¹ • (Z.velocity-P0.velocity)) = _
  rw [PDE.vecEuclideanNorm_smul, abs_of_pos (inv_pos.mpr hr)]
  ring

/-- Travel duration and displacement mismatches supplied by a source stack endpoint. -/
theorem stack_endpoint_data {d : ℕ} (P0 P : KineticPoint d) {r : ℝ} (hr : 0 < r)
    (m : ℕ) (hP : P ∈ forwardStack P0 r m) :
    r^2/8 ≤ stackTravelTime P0 P r ∧
      stackTravelTime P0 P r ≤ ((m : ℝ)+1)*r^2 ∧
      PDE.vecEuclideanNorm (P.position-stackStartPosition P0 r-
        stackTravelTime P0 P r • P0.velocity) ≤ ((m : ℝ)+2)*r^3 ∧
      PDE.vecEuclideanNorm (P.velocity-P0.velocity) ≤ r := by
  have hs := sq_pos_of_pos hr
  have hv := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hr).mp hP.2.2.1
  have hx := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt
    (by positivity : 0 < ((m+2 : ℕ) : ℝ)*r^3)).mp hP.2.2.2
  rw [sub_zero] at hx
  have heq : P.position-stackStartPosition P0 r-stackTravelTime P0 P r • P0.velocity =
      relativePosition P0 P := by
    ext i
    simp only [stackStartPosition, stackTravelTime, stackStartTime, relativePosition,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  refine ⟨?_, ?_, ?_, hv.le⟩
  · unfold stackTravelTime stackStartTime
    nlinarith only [hP.1, hs]
  · unfold stackTravelTime stackStartTime
    nlinarith only [hP.2.1, hs]
  · rw [heq]
    push_cast at hx
    exact hx.le

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth
