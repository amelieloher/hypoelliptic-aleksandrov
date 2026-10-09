module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PatchPowerDoubling
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Hermite
import Mathlib.Tactic

/-! # The last fixed-width path in return-time propagation -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Parabolic Set Holder Holder.Growth

/-- A fixed positive patch reaches every endpoint with the indicated bounded displacement.
The displacement is measured relative to the initial transport velocity. -/
theorem return_fixed_patch_path (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hp6 : SmoothAutonomousP6Statement lam Lam) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1 / 8) :
    ∃ c : ℝ, 0 < c ∧ ∀ (A : SmoothAutonomous lam Lam) (u : Point → ℝ),
      IsNonnegativeHomogeneousSolution A u → ∀ (z P : Point) (k : ℝ),
      1 / 2 ≤ z.time → 1 / 2 ≤ P.time - z.time → P.time - z.time ≤ 3 →
      PDE.vecEuclideanNorm (P.position - z.position -
        (P.time - z.time) • z.velocity) ≤ 12 →
      PDE.vecEuclideanNorm (P.velocity - z.velocity) ≤ 4 →
      0 ≤ k → (∀ q ∈ backwardCylinder z r, k ≤ u q) → c * k ≤ u P := by
  obtain ⟨c, hc, _hc1, hprop⟩ := propagation 1 (by omega) lam Lam hlam hLam
    1000 (r ^ 3 / 2) (r / 2) (r ^ 2 / 8) 4
    (by norm_num) (by positivity) (by positivity) (by positivity)
    (by nlinarith [sq_nonneg r])
  obtain ⟨C_A, _hC, hadm⟩ := return_solution_admissible hp6
  refine ⟨c, hc, ?_⟩
  intro A u hu z P k hzt hgap hgap1 hx hv hk hpatch
  let a := r ^ 2 / 8
  let tminus := z.time - a
  let T := P.time - tminus
  let x0 := z.position - a • z.velocity
  let xh := hermitePosition T x0 z.velocity P.position P.velocity
  let vh := hermiteVelocity T x0 z.velocity P.position P.velocity
  have hr2 : r ^ 2 ≤ 1 / 64 := by nlinarith
  have ha : 0 < a := by dsimp [a]; positivity
  have hT : 0 < T := by dsimp [T, tminus]; linarith
  have hTlo : 1 / 2 ≤ T := by dsimp [T, tminus]; linarith
  have hThi : T ≤ 4 := by dsimp [T, tminus, a]; linarith
  have hres : P.position - x0 - T • z.velocity =
      P.position - z.position - (P.time - z.time) • z.velocity := by
    dsimp [x0, T, tminus]
    module
  have hacc : 6 * PDE.vecEuclideanNorm (P.position - x0 - T • z.velocity) / T ^ 2 +
      4 * PDE.vecEuclideanNorm (P.velocity - z.velocity) / T ≤ 1000 := by
    rw [hres]
    have h₁ : 6 * PDE.vecEuclideanNorm
        (P.position - z.position - (P.time - z.time) • z.velocity) / T ^ 2 ≤ 288 := by
      apply (div_le_iff₀ (sq_pos_of_pos hT)).mpr
      nlinarith
    have h₂ : 4 * PDE.vecEuclideanNorm (P.velocity - z.velocity) / T ≤ 32 := by
      apply (div_le_iff₀ hT).mpr
      nlinarith
    linarith
  have hs := hermite_isSkeleton hT x0 z.velocity P.position P.velocity
  let x := extendPosition xh vh 0 T hT.le
  let v := extendVelocity vh 0 T hT.le
  have hacc0 : 0 ≤ 6 * PDE.vecEuclideanNorm (P.position - x0 - T • z.velocity) / T ^ 2 +
      4 * PDE.vecEuclideanNorm (P.velocity - z.velocity) / T :=
    add_nonneg (div_nonneg (mul_nonneg (by norm_num) (PDE.vecEuclideanNorm_nonneg _))
      (sq_nonneg T))
      (div_nonneg (mul_nonneg (by norm_num) (PDE.vecEuclideanNorm_nonneg _)) hT.le)
  have hsk : IsSkeleton x v 1000 (-a) T := by
    apply skeleton_mono_bound (extendPosition_isSkeleton hT.le hacc0 hs (-a) T)
    exact hacc
  have hleft (s : ℝ) (hs : s ≤ 0) : x s = x0 + s • z.velocity ∧ v s = z.velocity := by
    constructor
    · dsimp only [x]
      rw [extendPosition_left xh vh hT.le hs]
      simp only [xh, vh, hermitePosition_zero, hermiteVelocity_zero, sub_zero]
    · dsimp only [v, extendVelocity]
      rw [projIcc_of_le_left hT.le hs]
      exact hermiteVelocity_zero _ _ _ _ _
  have hxend : x T = P.position := by
    rw [show x T = xh T from extendPosition_eq hT.le hs (right_mem_Icc.mpr hT.le)]
    exact hermitePosition_end hT.ne' _ _ _ _
  have hvend : v T = P.velocity := by
    rw [show v T = vh T from extendVelocity_eq vh hT.le (right_mem_Icc.mpr hT.le)]
    exact hermiteVelocity_end hT.ne' _ _ _ _
  have htube : corridor tminus (-a) T (r ^ 3 / 2) (r / 2) x v ⊆
      {q | 0 < q.time} := by
    intro q hq
    change 0 < q.time
    have hqt := hq.1.1
    dsimp [tminus, a] at hqt
    linarith
  apply hprop 6 C_A (by norm_num) _ (autonomous_fullElliptic A)
    _ (isOpen_lt continuous_const continuous_time) tminus P
    (by change 0 < P.time; linarith) (by dsimp [T, tminus]; linarith) hThi
    x v hsk hxend hvend htube k hk u (fun q hq => hu.2.1 q hq) (hadm A u hu).1
  intro q hq hqt
  change q.time - tminus ∈ Icc (-a) T ∧
    PDE.vecEuclideanNorm (q.position - x (q.time - tminus)) ≤ r ^ 3 / 2 ∧
    PDE.vecEuclideanNorm (q.velocity - v (q.time - tminus)) ≤ r / 2 at hq
  have hs0 : q.time - tminus ≤ 0 := sub_nonpos.mpr hqt
  obtain ⟨hxq, hvq⟩ := hleft (q.time - tminus) hs0
  apply hpatch q
  refine ⟨?_, ?_, ?_, ?_⟩
  · have ht := hq.1.1
    dsimp [tminus, a] at ht
    nlinarith [sq_pos_of_pos hr]
  · dsimp [tminus] at hqt
    linarith
  · apply (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hr).mpr
    rw [hvq] at hq
    exact hq.2.2.trans_lt (by linarith)
  · apply (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (pow_pos hr 3)).mpr
    simp only [sub_zero]
    have he : relativePosition z q = q.position - x (q.time - tminus) := by
      rw [hxq]
      dsimp [relativePosition, x0, tminus]
      module
    rw [he]
    exact hq.2.1.trans_lt (by nlinarith [pow_pos hr 3])

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
