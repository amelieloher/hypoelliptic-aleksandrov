module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.ReferenceGeometryCylinder
import Mathlib.Tactic

/-! # Exact source acceleration and generous uniform bounds for reference Hermite paths -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth

open Set

/-- The reference endpoint estimates use the Euclidean triangle inequality for differences. -/
theorem reference_norm_sub_le {d : ℕ} (x y : PDE.Vec d) :
    PDE.vecEuclideanNorm (x - y) ≤ PDE.vecEuclideanNorm x + PDE.vecEuclideanNorm y := by
  rw [sub_eq_add_neg]
  simpa only [PDE.vecEuclideanNorm_neg] using PDE.vecEuclideanNorm_add_le x (-y)

/-- A fixed finite spatial reference bound, chosen before the physical scale. -/
def referenceBound (m : ℕ) : ℝ := 16 * stackPathBound m + (m : ℝ) + 20

/-- Reference endpoints give the source travel-time and Hermite displacement bounds. -/
theorem reference_endpoint_bounds {d : ℕ} (m : ℕ) (S P : KineticPoint d)
    (hS : S ∈ closure (samplingCylinder d m))
    (hP : P ∈ backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1) :
    (m : ℝ) + 1 ≤ P.time - S.time ∧ P.time - S.time ≤ (m : ℝ) + 3 ∧
      PDE.vecEuclideanNorm (P.position - S.position - (P.time - S.time) • S.velocity) ≤
        (m : ℝ) + 5 ∧ PDE.vecEuclideanNorm (P.velocity - S.velocity) ≤ 2 := by
  obtain ⟨hstlo, hstup, hsx, hsv⟩ := sampling_closure_bounds d m S hS
  have hpv := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt
    (by norm_num : (0 : ℝ) < 1)).mp hP.2.2.1
  have hpx := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt
    (by norm_num : (0 : ℝ) < 1 ^ 3)).mp hP.2.2.2
  simp only [relativePosition, sub_zero, smul_zero, one_pow] at hpx hpv
  have hptlo : -1 < P.time := by simpa only [one_pow, zero_sub] using hP.1
  have hptup : P.time < 0 := hP.2.1
  have hTlo : (m : ℝ) + 1 ≤ P.time - S.time := by linarith only [hptlo, hstup]
  have hThi : P.time - S.time ≤ (m : ℝ) + 3 := by linarith only [hptup, hstlo]
  have hT : 0 ≤ P.time - S.time := by
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith only [hTlo, hm]
  refine ⟨hTlo, hThi, ?_, ?_⟩
  · apply (reference_norm_sub_le _ _).trans
    rw [PDE.vecEuclideanNorm_smul, abs_of_nonneg hT]
    have hx := reference_norm_sub_le P.position S.position
    have hv := mul_le_mul_of_nonneg_left hsv hT
    linarith only [hx, hpx, hsx, hv, hThi]
  · have hv := reference_norm_sub_le P.velocity S.velocity
    linarith only [hv, hpv, hsv]

/-- The reference Hermite acceleration has exactly the source upper bound. -/
theorem reference_hermite_acceleration {d : ℕ} (m : ℕ) {T : ℝ}
    (hTlo : (m : ℝ) + 1 ≤ T) (x0 v0 x1 v1 : PDE.Vec d)
    (hx : PDE.vecEuclideanNorm (x1 - x0 - T • v0) ≤ (m : ℝ) + 5)
    (hv : PDE.vecEuclideanNorm (v1 - v0) ≤ 2) :
    6 * PDE.vecEuclideanNorm (x1 - x0 - T • v0) / T ^ 2 +
      4 * PDE.vecEuclideanNorm (v1 - v0) / T ≤ 6 * ((m : ℝ) + 5) + 8 := by
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hT : 1 ≤ T := by linarith only [hTlo, hm]
  have hT0 : 0 < T := lt_of_lt_of_le (by norm_num) hT
  have hT2 : 1 ≤ T ^ 2 := by nlinarith only [hT]
  have hx0 := PDE.vecEuclideanNorm_nonneg (x1 - x0 - T • v0)
  have hv0 := PDE.vecEuclideanNorm_nonneg (v1 - v0)
  have he1 : 6 * PDE.vecEuclideanNorm (x1 - x0 - T • v0) / T ^ 2 ≤
      6 * ((m : ℝ) + 5) := by
    apply (div_le_iff₀ (sq_pos_of_pos hT0)).mpr
    have he := mul_le_mul_of_nonneg_left hT2
      (show 0 ≤ 6 * ((m : ℝ) + 5) by positivity)
    nlinarith only [he, hx]
  have he2 : 4 * PDE.vecEuclideanNorm (v1 - v0) / T ≤ 8 := by
    apply (div_le_iff₀ hT0).mpr
    nlinarith only [hv, hT]
  exact add_le_add he1 he2

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth
