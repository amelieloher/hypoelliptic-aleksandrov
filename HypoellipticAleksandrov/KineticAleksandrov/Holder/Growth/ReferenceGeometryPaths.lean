module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.ReferenceGeometryPathBounds
import Mathlib.Tactic

/-! # Constructed Hermite and tangent corridors in the buffered reference region -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth

open Set

/-- Every reference endpoint has an actual source Hermite/tangent path in the buffered box. -/
theorem exists_reference_corridor {d : ℕ} (m : ℕ) (S P : KineticPoint d)
    (hS : S ∈ closure (samplingCylinder d m))
    (hP : P ∈ backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1) :
    ∃ x v : ℝ → PDE.Vec d,
      IsSkeleton x v (6 * ((m : ℝ) + 5) + 8) (-1) (P.time - S.time) ∧
      x 0 = S.position ∧ v 0 = S.velocity ∧
      x (P.time - S.time) = P.position ∧ v (P.time - S.time) = P.velocity ∧
      (∀ s ≤ 0, x s = S.position + s • S.velocity ∧ v s = S.velocity) ∧
      Continuous v ∧ (∀ s, HasDerivAt x (v s) s) ∧
      (∀ s t, PDE.vecEuclideanNorm (v s - v t) ≤
        (6 * ((m : ℝ) + 5) + 8) * |s - t|) ∧
      corridor S.time (-1) (P.time - S.time) 1 1 x v ⊆
        referenceRegion d m (referenceBound m) := by
  obtain ⟨hTlo, hThi, hx, hv⟩ := reference_endpoint_bounds m S P hS hP
  obtain ⟨hstlo, _, hsx, hsv⟩ := sampling_closure_bounds d m S hS
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  let T := P.time - S.time
  have hT : 0 < T := by dsimp only [T]; linarith only [hTlo, hm]
  let xh := hermitePosition T S.position S.velocity P.position P.velocity
  let vh := hermiteVelocity T S.position S.velocity P.position P.velocity
  let H := 6 * PDE.vecEuclideanNorm (P.position - S.position - T • S.velocity) / T ^ 2 +
    4 * PDE.vecEuclideanNorm (P.velocity - S.velocity) / T
  have hH : 0 ≤ H := by
    have hx0 := PDE.vecEuclideanNorm_nonneg (P.position - S.position - T • S.velocity)
    have hv0 := PDE.vecEuclideanNorm_nonneg (P.velocity - S.velocity)
    dsimp only [H]
    positivity
  have hsk : IsSkeleton xh vh H 0 T := hermite_isSkeleton hT _ _ _ _
  let x := extendPosition xh vh 0 T hT.le
  let v := extendVelocity vh 0 T hT.le
  have hleft (s : ℝ) (hs : s ≤ 0) : x s = S.position + s • S.velocity ∧
      v s = S.velocity := by
    constructor
    · dsimp only [x]
      rw [extendPosition_left xh vh hT.le hs]
      simp only [xh, vh, hermitePosition_zero, hermiteVelocity_zero, sub_zero]
    · dsimp only [v, extendVelocity]
      rw [projIcc_of_le_left hT.le hs]
      exact hermiteVelocity_zero _ _ _ _ _
  have hB : 0 ≤ stackPathBound m := by unfold stackPathBound; positivity
  have hbounds : ∀ s ∈ Icc (-1) T,
      PDE.vecEuclideanNorm (x s) ≤ (m : ℝ) + 4 + 8 * stackPathBound m ∧
        PDE.vecEuclideanNorm (v s) ≤ 1 + 2 * stackPathBound m := by
    intro s hs
    by_cases h : s ≤ 0
    · rw [(hleft s h).1, (hleft s h).2]
      have habs : |s| ≤ 1 := by rw [abs_of_nonpos h]; linarith only [hs.1]
      have hvbound := mul_le_mul habs hsv (PDE.vecEuclideanNorm_nonneg _) (by norm_num)
      have hb := PDE.vecEuclideanNorm_add_le S.position (s • S.velocity)
      rw [PDE.vecEuclideanNorm_smul] at hb
      constructor <;> linarith only [hb, hvbound, hsx, hsv, hm, hB]
    · have hs' : s ∈ Icc 0 T := ⟨(lt_of_not_ge h).le, hs.2⟩
      have hb := stack_hermite_bounds (by norm_num : (0 : ℝ) < 2) m
        (by norm_num; linarith only [hTlo, hm] : (2 : ℝ) ^ 2 / 8 ≤ T)
        (by norm_num; linarith only [hThi, hm] : T ≤ ((m : ℝ) + 1) * (2 : ℝ) ^ 2)
        S.position S.velocity P.position P.velocity
        (by norm_num; linarith only [hx, hm]) (by exact hv) hs'
      norm_num only [show (2 : ℝ) ^ 3 = 8 by norm_num] at hb
      have hxs : x s = xh s := extendPosition_eq hT.le hsk hs'
      have hvs : v s = vh s := extendVelocity_eq vh hT.le hs'
      rw [hxs, hvs]
      have heq : xh s = S.position + s • S.velocity +
          (xh s - S.position - s • S.velocity) := by abel
      have hvq : vh s = S.velocity + (vh s - S.velocity) := by abel
      have hsbound : s ≤ (m : ℝ) + 3 := hs.2.trans hThi
      have hvnorm := mul_le_mul_of_nonneg_left hsv hs'.1
      have hxp := PDE.vecEuclideanNorm_add_le S.position (s • S.velocity)
      rw [PDE.vecEuclideanNorm_smul, abs_of_nonneg hs'.1] at hxp
      constructor
      · rw [heq]
        have he := PDE.vecEuclideanNorm_add_le (S.position + s • S.velocity)
          (xh s - S.position - s • S.velocity)
        linarith only [he, hxp, hvnorm, hsx, hsbound, hb.1]
      · rw [hvq]
        have he := PDE.vecEuclideanNorm_add_le S.velocity (vh s - S.velocity)
        linarith only [he, hsv, hb.2]
  refine ⟨x, v, skeleton_mono_bound
    (extendPosition_isSkeleton hT.le hH hsk _ _)
    (reference_hermite_acceleration m hTlo _ _ _ _ hx hv),
    (by simpa only [zero_smul, add_zero] using (hleft 0 le_rfl).1),
    (hleft 0 le_rfl).2, ?_, ?_, hleft,
    continuous_extendVelocity hT.le hsk.1,
    hasDerivAt_extendPosition hT.le hsk, ?_, ?_⟩
  · dsimp only [x]
    rw [extendPosition_eq hT.le hsk (right_mem_Icc.mpr hT.le)]
    exact hermitePosition_end hT.ne' _ _ _ _
  · dsimp only [v]
    rw [extendVelocity_eq vh hT.le (right_mem_Icc.mpr hT.le)]
    exact hermiteVelocity_end hT.ne' _ _ _ _
  · intro s t
    exact (extendVelocity_lipschitz hT.le hH hsk s t).trans
      (mul_le_mul_of_nonneg_right
        (reference_hermite_acceleration m hTlo _ _ _ _ hx hv) (abs_nonneg _))
  · intro Q hQ
    have hb := hbounds (Q.time - S.time) hQ.1
    have hpt : P.time < 0 := hP.2.1
    have hxq : Q.position = (Q.position - x (Q.time - S.time)) +
        x (Q.time - S.time) := by abel
    have hvq : Q.velocity = (Q.velocity - v (Q.time - S.time)) +
        v (Q.time - S.time) := by abel
    refine ⟨by linarith only [hQ.1.1, hstlo],
      by linarith only [hQ.1.2, hpt], ?_, ?_⟩
    · rw [hxq]
      apply (PDE.vecEuclideanNorm_add_le _ _).trans_lt
      dsimp only [referenceBound]
      linarith only [hQ.2.1, hb.1, hB]
    · rw [hvq]
      apply (PDE.vecEuclideanNorm_add_le _ _).trans_lt
      dsimp only [referenceBound]
      linarith only [hQ.2.2, hb.2, hB, hm]

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth
