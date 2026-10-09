module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.PropagationIterationBarrier
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.PropagationIterationGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.PropagationIterationSpatial
import Mathlib.Tactic

/-! # The preceding Gaussian dominates each positive initial-strip point -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Set

/-- The source overlap contraction gives both preceding-block membership and height control. -/
theorem gaussianBarrier_overlap_compare {d : ℕ} (hd : 1 ≤ d)
    {lam Lam H T0 T1 kx kv h ell : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hH : 0 ≤ H) (hT0 : 0 < T0) (hT1 : T0 ≤ T1) (hh : 0 < h)
    (hhstar : h ≤ stepSize d lam Lam H T0 T1 kx kv) (hell : 0 ≤ ell)
    (tminus sblock : ℝ) {x v : ℝ → PDE.Vec d} (hv : Continuous v)
    (hkin : ∀ t, HasDerivAt x (v t) t)
    (hLip : ∀ s t, PDE.vecEuclideanNorm (v s - v t) ≤ H * |s - t|)
    (P : KineticPoint d) (ht : P.time - tminus - sblock ≤ 0)
    (hp : 0 < gaussianBarrier lam Lam H h (barrierL d lam Lam H T1)
      (barrierGamma (barrierL d lam Lam H T1) * ell) tminus sblock x v P) :
    P ∈ closure (backwardCylinder ⟨tminus + sblock, x sblock, v sblock⟩
      (barrierW d lam Lam H T1 * Real.sqrt h)) ∧
      gaussianBarrier lam Lam H h (barrierL d lam Lam H T1)
        (barrierGamma (barrierL d lam Lam H T1) * ell) tminus sblock x v P ≤
      gaussianBarrier lam Lam H h (barrierL d lam Lam H T1)
        ell tminus (sblock - h) x v P := by
  let L := barrierL d lam Lam H T1
  let W := barrierW d lam Lam H T1
  let sigma := P.time - tminus - sblock
  have hL : 0 < L := barrierL_pos hd hlam hLam (hT0.le.trans hT1)
  have hgamma := (barrierGamma_bounds hL).1
  have hell' : 0 ≤ barrierGamma L * ell := mul_nonneg hgamma.le hell
  have hbudget := propagation_step_damping hd hlam hLam hH hT0 hT1 hh hhstar
  obtain ⟨hs, hq⟩ := gaussianBarrier_pos_quadratic hlam hh Lam H L
    (barrierGamma L * ell) tminus sblock hLam hell' hbudget x v P hp
  obtain ⟨hvball, hxball⟩ := gaussianBarrier_initial_previous_spatial hd hlam hLam
    hH hT0 hT1 hh hhstar hell' tminus sblock hv hkin hLip P ht hp
  have hW := two_le_barrierW (d := d) (lam := lam) (Lam := Lam) (T1 := T1) hH
  have hR : 0 < W * Real.sqrt h := mul_pos (by linarith only [hW])
    (Real.sqrt_pos.mpr hh)
  constructor
  · apply mem_closure_backwardCylinder_of_strict_spatial _ P hR _ _ hvball hxball
    · rw [propagation_block_radius_sq hh.le]
      change tminus + sblock - W ^ 2 * h < P.time
      have he : 4 * h ≤ W ^ 2 * h :=
        mul_le_mul_of_nonneg_right (by nlinarith only [hW]) hh.le
      linarith only [hs, he, hh]
    · change P.time ≤ tminus + sblock
      linarith only [ht]
  · have hqover := qform_overlap hlam hh hs.le ht
      (P.position - x (P.time - tminus)) (P.velocity - v (P.time - tminus))
    have hqhalf : qform lam h (sigma + h)
        (P.position - x (P.time - tminus)) (P.velocity - v (P.time - tminus)) ≤ L ^ 2 / 2 := by
      have he := mul_le_mul_of_nonneg_left hq.le (by norm_num : (0 : ℝ) ≤ 13 / 50)
      nlinarith only [hqover, he, sq_nonneg L]
    have hs' : 0 ≤ P.time - tminus - (sblock - h) := by linarith only [hs, hh]
    have ht' : P.time - tminus - (sblock - h) ≤ h := by linarith only [ht]
    have hq' : qform lam h (P.time - tminus - (sblock - h))
        (P.position - x (P.time - tminus)) (P.velocity - v (P.time - tminus)) ≤ L ^ 2 / 2 := by
      have he : P.time - tminus - (sblock - h) = sigma + h := by
        dsimp only [sigma]
        ring
      rw [he]
      exact hqhalf
    have hlower := gaussianBarrier_terminal_lower hh Lam H L ell tminus (sblock - h)
      hell (Xi_nonneg d (H := H) hlam hLam hh) hbudget x v P hs' ht' hq'
    have hupper := gaussianBarrier_initial_upper hlam hh Lam H L (barrierGamma L * ell)
      tminus sblock hLam hell' hbudget x v P ht
    have heq : barrierGamma L * ell * Real.exp (L ^ 2 / 512) = ell * barrierCb L := by
      unfold barrierGamma
      have hexp : Real.exp (-L ^ 2 / 512) * Real.exp (L ^ 2 / 512) = 1 := by
        rw [← Real.exp_add]
        have he : -L ^ 2 / 512 + L ^ 2 / 512 = 0 := by ring
        rw [he, Real.exp_zero]
      calc
        _ = ell * barrierCb L *
          (Real.exp (-L ^ 2 / 512) * Real.exp (L ^ 2 / 512)) := by ring
        _ = _ := by rw [hexp, mul_one]
    exact (hupper.trans_eq heq).trans hlower

end HypoellipticAleksandrov.KineticAleksandrov.Holder
