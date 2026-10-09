module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.PropagationBlockContainment
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.PropagationBlockPositive
import Mathlib.Tactic

/-! # A positive Gaussian lies strictly inside every source block lateral face -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Set

/-- Positivity puts the Gaussian strictly inside the velocity and position block faces. -/
theorem gaussianBarrier_positive_lateral {d : ℕ} (hd : 1 ≤ d)
    {lam Lam H T0 T1 kx kv h ell : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hH : 0 ≤ H) (hT0 : 0 < T0) (hT1 : T0 ≤ T1) (hh : 0 < h)
    (hhstar : h ≤ stepSize d lam Lam H T0 T1 kx kv) (hell : 0 ≤ ell)
    (tminus sblock : ℝ) {x v : ℝ → PDE.Vec d} (hv : Continuous v)
    (hkin : ∀ t, HasDerivAt x (v t) t)
    (hLip : ∀ s t, PDE.vecEuclideanNorm (v s - v t) ≤ H * |s - t|)
    (P : KineticPoint d)
    (hP : P ∈ closure (backwardCylinder
      ⟨tminus + sblock + h, x (sblock + h), v (sblock + h)⟩
      (barrierW d lam Lam H T1 * Real.sqrt h)))
    (hpos : 0 < gaussianBarrier lam Lam H h (barrierL d lam Lam H T1)
      ell tminus sblock x v P) :
    P.velocity ∈ PDE.euclideanBall (v (sblock + h))
        (barrierW d lam Lam H T1 * Real.sqrt h) ∧
      relativePosition ⟨tminus + sblock + h, x (sblock + h), v (sblock + h)⟩ P ∈
        PDE.euclideanBall (0 : PDE.Vec d) ((barrierW d lam Lam H T1 * Real.sqrt h) ^ 3) := by
  let L := barrierL d lam Lam H T1
  let W := barrierW d lam Lam H T1
  let C := (3 / 2 : ℝ) * L * Real.sqrt lam
  let b := sblock + h
  let s := P.time - tminus
  let R := W * Real.sqrt h
  let P₀ : KineticPoint d := ⟨tminus + sblock + h, x b, v b⟩
  have hW2 : 2 ≤ W := two_le_barrierW hH
  have hW : 0 < W := by linarith only [hW2]
  have hR : 0 < R := mul_pos hW (Real.sqrt_pos.mpr hh)
  have hbudget := propagation_step_damping hd hlam hLam hH hT0 hT1 hh hhstar
  have ht := (closure_backwardCylinder_bounds P₀ hR hP).2.1
  have hs1 : P.time - tminus - sblock ≤ h := by
    change P.time ≤ tminus + sblock + h at ht
    linarith only [ht]
  obtain ⟨hs0, _⟩ := gaussianBarrier_pos_quadratic hlam hh Lam H L ell tminus sblock
    hLam hell hbudget x v P hpos
  obtain ⟨hy, hV⟩ := gaussianBarrier_positive_set hlam hh Lam H L ell tminus sblock
    hLam hell (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hbudget x v P hs1 hpos
  have hdelta : 0 ≤ b - s ∧ b - s ≤ 2 * h := by
    dsimp only [b, s]
    constructor <;> linarith only [hs0, hs1, hh]
  have hhT1 : h ≤ T1 := by
    have he := (propagation_step_time hH hh hhstar).2
    linarith only [he, hT1, hh]
  have hhalf : h ≤ Real.sqrt T1 * Real.sqrt h := by
    have he := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hhT1) (Real.sqrt_nonneg h)
    nlinarith only [he, Real.sq_sqrt hh.le]
  have hthree : h ^ 2 ≤ Real.sqrt T1 * h ^ (3 / 2 : ℝ) := by
    have he : h ^ 2 = h ^ (3 / 2 : ℝ) * Real.sqrt h := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hh]
      norm_num
    rw [he]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt hhT1) (Real.rpow_nonneg hh.le _)
  have hpathv := hLip s b
  rw [abs_sub_comm, abs_of_nonneg hdelta.1] at hpathv
  have hveq : P.velocity - v b = (P.velocity - v s) + (v s - v b) := by abel
  have hvbound : PDE.vecEuclideanNorm (P.velocity - v b) ≤
      (C + 2 * H * Real.sqrt T1) * Real.sqrt h := by
    rw [hveq]
    apply (PDE.vecEuclideanNorm_add_le _ _).trans
    calc
      _ ≤ C * Real.sqrt h + H * (b - s) := add_le_add hV hpathv
      _ ≤ C * Real.sqrt h + H * (2 * h) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hdelta.2 hH)
      _ ≤ C * Real.sqrt h + (2 * H) * (Real.sqrt T1 * Real.sqrt h) := by
        have he := mul_le_mul_of_nonneg_left hhalf (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hH)
        nlinarith only [he]
      _ = _ := by ring
  have hrel : relativePosition P₀ P = (P.position - x s) +
      (x s - x b - (s - b) • v b) := by
    ext i
    simp only [relativePosition, P₀, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    dsimp only [b, s]
    ring
  have hrem := skeleton_position_remainder_le hv hkin hLip s b (sub_nonneg.mp hdelta.1)
  have hdeltaSq : (b - s) ^ 2 ≤ (2 * h) ^ 2 :=
    (sq_le_sq₀ hdelta.1 (by positivity)).mpr hdelta.2
  have hxb : PDE.vecEuclideanNorm (relativePosition P₀ P) ≤
      (C + 2 * H * Real.sqrt T1) * h ^ (3 / 2 : ℝ) := by
    rw [hrel]
    apply (PDE.vecEuclideanNorm_add_le _ _).trans
    calc
      _ ≤ C * h ^ (3 / 2 : ℝ) + H * (b - s) ^ 2 / 2 := add_le_add hy hrem
      _ ≤ C * h ^ (3 / 2 : ℝ) + H * (2 * h) ^ 2 / 2 :=
        add_le_add le_rfl (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hdeltaSq hH) (by norm_num))
      _ = C * h ^ (3 / 2 : ℝ) + (2 * H) * h ^ 2 := by ring
      _ ≤ C * h ^ (3 / 2 : ℝ) + (2 * H) * (Real.sqrt T1 * h ^ (3 / 2 : ℝ)) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hthree (by positivity))
      _ = _ := by ring
  have hCW : C + 2 * H * Real.sqrt T1 < W := by dsimp only [C, L, W, barrierW]; linarith
  have hcube : W ≤ W ^ 3 := by
    have hsq : 1 ≤ W ^ 2 := by nlinarith only [hW2]
    nlinarith only [mul_nonneg hW.le (sub_nonneg.mpr hsq)]
  constructor
  · apply (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hR).mpr
    exact hvbound.trans_lt (mul_lt_mul_of_pos_right hCW (Real.sqrt_pos.mpr hh))
  · apply (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (pow_pos hR 3)).mpr
    rw [sub_zero, propagation_block_radius_cube hh.le]
    exact hxb.trans_lt (mul_lt_mul_of_pos_right (hCW.trans_le hcube)
      (Real.rpow_pos_of_pos hh _))

/-- The Gaussian is nonpositive on the entire kinetic boundary of a source block. -/
theorem gaussianBarrier_nonpos_boundary {d : ℕ} (hd : 1 ≤ d)
    {lam Lam H T0 T1 kx kv h ell : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hH : 0 ≤ H) (hT0 : 0 < T0) (hT1 : T0 ≤ T1) (hh : 0 < h)
    (hhstar : h ≤ stepSize d lam Lam H T0 T1 kx kv) (hell : 0 ≤ ell)
    (tminus sblock : ℝ) {x v : ℝ → PDE.Vec d} (hv : Continuous v)
    (hkin : ∀ t, HasDerivAt x (v t) t)
    (hLip : ∀ s t, PDE.vecEuclideanNorm (v s - v t) ≤ H * |s - t|)
    (P : KineticPoint d)
    (hP : P ∈ kineticBoundary
      ⟨tminus + sblock + h, x (sblock + h), v (sblock + h)⟩
      (barrierW d lam Lam H T1 * Real.sqrt h)) :
    gaussianBarrier lam Lam H h (barrierL d lam Lam H T1)
      ell tminus sblock x v P ≤ 0 := by
  by_contra hn
  have hp := lt_of_not_ge hn
  obtain ⟨hc, hb⟩ := mem_kineticBoundary_iff.mp hP
  obtain ⟨hvball, hxball⟩ := gaussianBarrier_positive_lateral hd hlam hLam hH hT0 hT1
    hh hhstar hell tminus sblock hv hkin hLip P hc hp
  rcases hb with ht | hvface | ⟨hxface, _⟩
  · have hbudget := propagation_step_damping hd hlam hLam hH hT0 hT1 hh hhstar
    have hs := (gaussianBarrier_pos_quadratic hlam hh Lam H
      (barrierL d lam Lam H T1) ell tminus sblock hLam hell hbudget x v P hp).1
    have hW := two_le_barrierW (d := d) (lam := lam) (Lam := Lam) (T1 := T1) hH
    rw [propagation_block_radius_sq hh.le] at ht
    change P.time = tminus + sblock + h - barrierW d lam Lam H T1 ^ 2 * h at ht
    have he : 4 * h ≤ barrierW d lam Lam H T1 ^ 2 * h := by
      have hw : 4 ≤ barrierW d lam Lam H T1 ^ 2 := by nlinarith only [hW]
      exact mul_le_mul_of_nonneg_right hw hh.le
    linarith only [ht, hs, he, hh]
  · exact (ne_of_lt hvball) hvface
  · exact (ne_of_lt hxball) hxface

end HypoellipticAleksandrov.KineticAleksandrov.Holder
