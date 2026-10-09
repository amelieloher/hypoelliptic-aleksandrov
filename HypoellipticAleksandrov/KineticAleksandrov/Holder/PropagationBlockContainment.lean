module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.PropagationBlockGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.PropagationBlockTaylor
import Mathlib.Tactic

/-! # Source block cylinders lie in the smooth path corridor with halved radii -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Set

/-- The source block closure lies in the path tube with halved position and velocity radii. -/
theorem propagation_block_containment {d : ℕ} {lam Lam H T0 T1 kx kv h : ℝ}
    (hH : 0 ≤ H) (_hT0 : 0 < T0) (hT1 : T0 ≤ T1) (hkx : 0 < kx) (hkv : 0 < kv)
    (hh : 0 < h) (hhstar : h ≤ stepSize d lam Lam H T0 T1 kx kv)
    (tminus sblock TP : ℝ) (hsblock : 0 ≤ sblock) (hblock : sblock + h ≤ TP)
    {x v : ℝ → PDE.Vec d} (hv : Continuous v) (hkin : ∀ t, HasDerivAt x (v t) t)
    (hLip : ∀ s t, PDE.vecEuclideanNorm (v s - v t) ≤ H * |s - t|) :
    closure (backwardCylinder
      ⟨tminus + sblock + h, x (sblock + h), v (sblock + h)⟩
      (barrierW d lam Lam H T1 * Real.sqrt h)) ⊆
      corridor tminus (-T0) TP (kx / 2) (kv / 2) x v := by
  let W := barrierW d lam Lam H T1
  let b := sblock + h
  let R := W * Real.sqrt h
  let P₀ : KineticPoint d := ⟨tminus + sblock + h, x b, v b⟩
  have hW : 0 < W := lt_of_lt_of_le (by norm_num) (two_le_barrierW hH)
  have hR : 0 < R := mul_pos hW (Real.sqrt_pos.mpr hh)
  have htime := propagation_step_time hH hh hhstar
  have hhT1 : h ≤ T1 := by linarith only [htime.2, hT1, hh]
  have hsqrt := Real.sqrt_le_sqrt hhT1
  have hhalf : h ≤ Real.sqrt T1 * Real.sqrt h := by
    calc
      h = Real.sqrt h * Real.sqrt h := by nlinarith only [Real.sq_sqrt hh.le]
      _ ≤ Real.sqrt T1 * Real.sqrt h :=
        mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg h)
  have hpower : h ^ 2 = h ^ (3 / 2 : ℝ) * Real.sqrt h := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hh]
    norm_num
  have hthree : h ^ 2 ≤ Real.sqrt T1 * h ^ (3 / 2 : ℝ) := by
    rw [hpower]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hsqrt (Real.rpow_nonneg hh.le _)
  intro P hP
  let s := P.time - tminus
  obtain ⟨htlo, htup, hvel, hpos⟩ := closure_backwardCylinder_bounds P₀ hR hP
  have hdelta : 0 ≤ b - s ∧ b - s ≤ W ^ 2 * h := by
    rw [propagation_block_radius_sq hh.le] at htlo
    change tminus + sblock + h - W ^ 2 * h ≤ P.time at htlo
    change P.time ≤ tminus + sblock + h at htup
    dsimp only [b, s]
    constructor <;> linarith only [htlo, htup]
  have hs : s ∈ Icc (-T0) TP := by
    have hb : b ≤ TP := hblock
    have ht : W ^ 2 * h ≤ T0 := htime.1
    constructor <;> dsimp only [b] at * <;> linarith only [hdelta.1, hdelta.2, hb, ht, hsblock, hh]
  have hvelEq : P.velocity - v s = (P.velocity - v b) + (v b - v s) := by abel
  have hvelPath := hLip b s
  rw [abs_of_nonneg hdelta.1] at hvelPath
  have hvelTotal : PDE.vecEuclideanNorm (P.velocity - v s) ≤ R + H * (b - s) := by
    rw [hvelEq]
    exact (PDE.vecEuclideanNorm_add_le _ _).trans (add_le_add hvel hvelPath)
  have hvelTube : PDE.vecEuclideanNorm (P.velocity - v s) ≤
      velocityTubeConstant d lam Lam H T1 * Real.sqrt h := by
    calc
      _ ≤ R + H * (W ^ 2 * h) := hvelTotal.trans
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left hdelta.2 hH))
      _ ≤ R + (H * W ^ 2) * (Real.sqrt T1 * Real.sqrt h) := by
        apply add_le_add le_rfl
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hhalf
          (mul_nonneg hH (sq_nonneg W))
      _ = _ := by dsimp only [R, W, velocityTubeConstant]; ring
  have hrem := skeleton_position_remainder_le hv hkin hLip s b (sub_nonneg.mp hdelta.1)
  have hposEq : P.position - x s = relativePosition P₀ P +
      (-(x s - x b - (s - b) • v b)) := by
    ext i
    simp only [relativePosition, P₀, Pi.sub_apply, Pi.add_apply, Pi.neg_apply,
      Pi.smul_apply, smul_eq_mul]
    dsimp only [s, b]
    ring
  have hposTotal : PDE.vecEuclideanNorm (P.position - x s) ≤ R ^ 3 + H * (b - s) ^ 2 / 2 := by
    rw [hposEq]
    exact (PDE.vecEuclideanNorm_add_le _ _).trans
      (add_le_add hpos (by simpa only [PDE.vecEuclideanNorm_neg] using hrem))
  have hdeltaSq : (b - s) ^ 2 ≤ (W ^ 2 * h) ^ 2 :=
    (sq_le_sq₀ hdelta.1 (mul_nonneg (sq_nonneg W) hh.le)).mpr hdelta.2
  have hposTube : PDE.vecEuclideanNorm (P.position - x s) ≤
      positionTubeConstant d lam Lam H T1 * h ^ (3 / 2 : ℝ) := by
    calc
      _ ≤ R ^ 3 + H * (W ^ 2 * h) ^ 2 / 2 := hposTotal.trans
        (add_le_add le_rfl (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hdeltaSq hH) (by norm_num)))
      _ = W ^ 3 * h ^ (3 / 2 : ℝ) + (H * W ^ 4 / 2) * h ^ 2 := by
        rw [propagation_block_radius_cube hh.le]
        ring
      _ ≤ W ^ 3 * h ^ (3 / 2 : ℝ) +
          (H * W ^ 4 / 2) * (Real.sqrt T1 * h ^ (3 / 2 : ℝ)) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hthree (by positivity))
      _ = _ := by dsimp only [W, positionTubeConstant]; ring
  exact ⟨hs, hposTube.trans (propagation_step_position hH hkx hh hhstar),
    hvelTube.trans (propagation_step_velocity hH hkv hh hhstar)⟩

end HypoellipticAleksandrov.KineticAleksandrov.Holder
