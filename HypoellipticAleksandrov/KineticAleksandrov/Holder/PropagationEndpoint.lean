module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.PropagationIteration
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.PropagationEndpointQuadratic
import Mathlib.Tactic

/-! # Endpoint closure of the finite source Gaussian chain -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Set

/-- The source endpoint allowance closes propagation along a smooth approximating path. -/
theorem propagation_smooth_endpoint {d : ℕ} (hd : 1 ≤ d)
    {lam Lam H T0 T1 kx kv h ell TP : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hH : 0 ≤ H) (hT0 : 0 < T0) (hT1 : T0 ≤ T1) (hkx : 0 < kx) (hkv : 0 < kv)
    (hh : 0 < h) (hhstar : h ≤ stepSize d lam Lam H T0 T1 kx kv) (hell : 0 ≤ ell)
    (n : ℕ) (hn : 0 < n) (hnTP : (n : ℝ) * h = TP)
    (A : FullKineticCoefficient d) (hA : FullElliptic lam Lam A)
    (O : Set (KineticPoint d)) (tminus : ℝ)
    {x v : ℝ → PDE.Vec d} (hx : ContDiff ℝ (⊤ : ℕ∞) x)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hkin : ∀ s, HasDerivAt x (v s) s)
    (hLip : ∀ s t, PDE.vecEuclideanNorm (v s - v t) ≤ H * |s - t|)
    (htube : corridor tminus (-T0) TP (kx / 2) (kv / 2) x v ⊆ O)
    {p C_A : ℝ} (u : KineticPoint d → ℝ) (hnonneg : ∀ P ∈ O, 0 ≤ u P)
    (hu : IsAdmissibleSupersolution A O p C_A u)
    (hinitial : ∀ Q ∈ corridor tminus (-T0) TP (kx / 2) (kv / 2) x v,
      Q.time ≤ tminus → ell ≤ u Q)
    (P : KineticPoint d) (htime : P.time = tminus + TP)
    (hposition : PDE.vecEuclideanNorm (P.position - x TP) ≤
      (barrierL d lam Lam H T1 * Real.sqrt lam / 8) * h ^ (3 / 2 : ℝ))
    (hvelocity : PDE.vecEuclideanNorm (P.velocity - v TP) ≤
      (barrierL d lam Lam H T1 * Real.sqrt lam / 8) * Real.sqrt h) :
    (barrierGamma (barrierL d lam Lam H T1)) ^ n * ell ≤ u P := by
  let L := barrierL d lam Lam H T1
  let W := barrierW d lam Lam H T1
  let C := L * Real.sqrt lam / 8
  let a := (barrierGamma L) ^ (n - 1) * Real.exp (-L ^ 2 / 512) * ell
  have hL : 0 < L := barrierL_pos hd hlam hLam (hT0.le.trans hT1)
  have hg := (barrierGamma_bounds hL).1
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hW : 2 ≤ W := two_le_barrierW hH
  have hCW : C < W := by
    have he : 0 ≤ L * Real.sqrt lam := mul_nonneg hL.le (Real.sqrt_nonneg _)
    dsimp only [C, W, barrierW]
    linarith only [he, mul_nonneg hH (Real.sqrt_nonneg T1)]
  have hcube : W ≤ W ^ 3 := by
    have hw : 0 ≤ W := by linarith only [hW]
    have hw2 : 1 ≤ W ^ 2 := by nlinarith only [hW]
    nlinarith only [mul_nonneg hw (sub_nonneg.mpr hw2)]
  have hR : 0 < W * Real.sqrt h := mul_pos (by linarith only [hW])
    (Real.sqrt_pos.mpr hh)
  have hnstep : ((n - 1 : ℕ) : ℝ) * h + h = TP := by
    have he : n - 1 + 1 = n := Nat.sub_add_cancel hn
    have he' := congrArg (fun k : ℕ => (k : ℝ) * h) he
    push_cast at he'
    linarith only [he', hnTP]
  have hclosure : P ∈ closure (backwardCylinder
      ⟨tminus + ((n - 1 : ℕ) : ℝ) * h + h,
        x (((n - 1 : ℕ) : ℝ) * h + h), v (((n - 1 : ℕ) : ℝ) * h + h)⟩
      (W * Real.sqrt h)) := by
    rw [add_assoc tminus, hnstep]
    apply mem_closure_backwardCylinder_of_strict_spatial _ P hR
    · change tminus + TP - (W * Real.sqrt h) ^ 2 < P.time
      rw [htime]
      nlinarith only [sq_pos_of_pos hR]
    · change P.time ≤ tminus + TP
      exact htime.le
    · apply (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hR).mpr
      exact hvelocity.trans_lt (mul_lt_mul_of_pos_right hCW (Real.sqrt_pos.mpr hh))
    · apply (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (pow_pos hR 3)).mpr
      have hrel : relativePosition ⟨tminus + TP, x TP, v TP⟩ P = P.position - x TP := by
        simp only [relativePosition, htime, sub_self, zero_smul, sub_zero]
      rw [hrel, sub_zero, propagation_block_radius_cube hh.le]
      exact hposition.trans_lt
        (mul_lt_mul_of_pos_right (hCW.trans_le hcube) (Real.rpow_pos_of_pos hh _))
  have hcomparison := propagation_overlap_induction hd hlam hLam hH hT0 hT1 hkx hkv
    hh hhstar hell n hnTP.le A hA O tminus hx hv hkin hLip htube u hnonneg hu
    hinitial (n - 1) (Nat.sub_lt hn (by norm_num)) P hclosure
  have hbudget := propagation_step_damping hd hlam hLam hH hT0 hT1 hh hhstar
  have hs : P.time - tminus - ((n - 1 : ℕ) : ℝ) * h = h := by
    linarith only [htime, hnstep]
  have hPt : P.time - tminus = TP := by linarith only [htime]
  have hq := qform_endpoint_half hlam hh hL.le
    (P.position - x TP) (P.velocity - v TP) hposition hvelocity
  have hlower := gaussianBarrier_terminal_lower hh Lam H L a tminus
    (((n - 1 : ℕ) : ℝ) * h) ha (Xi_nonneg d (H := H) hlam hLam hh)
    hbudget x v P (by rw [hs]; exact hh.le) (by rw [hs]) (by rw [hs, hPt]; exact hq)
  have heq : a * barrierCb L = (barrierGamma L) ^ n * ell := by
    have hn' : n = (n - 1) + 1 := (Nat.sub_add_cancel hn).symm
    rw [hn', pow_succ]
    dsimp only [a, barrierGamma]
    ring
  exact (heq.symm ▸ hlower).trans hcomparison

end HypoellipticAleksandrov.KineticAleksandrov.Holder
