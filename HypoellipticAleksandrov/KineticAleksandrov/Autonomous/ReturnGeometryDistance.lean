module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ReturnGeometryBoxes
import Mathlib.Tactic

/-! # Quasi-distance bounds for the positive return neighbourhood -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Parabolic Set Holder

/-- A cylinder of radius `ell` has quasi-distance at most four times its radius from its top. -/
theorem returnCylinder_distance (z p : Point) (ell : ℝ) (hell : 0 < ell)
    (hp : p ∈ closure (backwardCylinder z ell)) : quasiDistance z p ≤ 4 * ell := by
  obtain ⟨ht, hv, hx⟩ := returnCylinder_bounds z p ell hell hp
  have hinv : relativePosition p z = -relativePosition z p +
      (p.time - z.time) • (p.velocity - z.velocity) := by
    unfold relativePosition
    module
  have hxi := PDE.vecEuclideanNorm_add_le (-relativePosition z p)
    ((p.time - z.time) • (p.velocity - z.velocity))
  rw [PDE.vecEuclideanNorm_neg, PDE.vecEuclideanNorm_smul, ← hinv] at hxi
  have hmul := mul_le_mul ht hv (PDE.vecEuclideanNorm_nonneg _) (sq_nonneg ell)
  have hxinv : PDE.vecEuclideanNorm (relativePosition p z) ≤ 2 * ell ^ 3 := by
    nlinarith
  have hmax : max (PDE.vecEuclideanNorm (relativePosition z p))
      (PDE.vecEuclideanNorm (relativePosition p z)) ≤ (2 * ell) ^ 3 := by
    apply max_le <;> nlinarith [pow_pos hell 3]
  have hmax0 : 0 ≤ max (PDE.vecEuclideanNorm (relativePosition z p))
      (PDE.vecEuclideanNorm (relativePosition p z)) :=
    le_max_of_le_left (PDE.vecEuclideanNorm_nonneg _)
  have hroot := Real.rpow_le_rpow hmax0 hmax (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hcube : ((2 * ell) ^ 3) ^ (1 / 3 : ℝ) = 2 * ell := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ 2 * ell)]
    norm_num
  rw [hcube] at hroot
  have htime : Real.sqrt |z.time - p.time| ≤ ell := by
    rw [abs_sub_comm]
    exact (Real.sqrt_le_iff).mpr ⟨hell.le, ht⟩
  unfold quasiDistance
  rw [PDE.vecEuclideanNorm_sub_comm z.velocity p.velocity]
  dsimp only [relativePosition] at hroot
  exact (add_le_add (add_le_add htime hv) hroot).trans_eq (by ring)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
