module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.PropagationParametersPositive
import Mathlib.Tactic

/-! # Radius containment and joint source propagation parameter bounds -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

/-- The source velocity step restriction gives the half-radius containment bound. -/
theorem propagation_step_velocity {d : ℕ} {lam Lam H T0 T1 kx kv h : ℝ}
    (hH : 0 ≤ H) (hkv : 0 < kv) (_hh : 0 < h)
    (hhstar : h ≤ stepSize d lam Lam H T0 T1 kx kv) :
    velocityTubeConstant d lam Lam H T1 * Real.sqrt h ≤ kv / 2 := by
  have hc := (tubeConstants_pos (d := d) (lam := lam) (Lam := Lam) (T1 := T1) hH).1
  have hratio : 0 < kv / (2 * velocityTubeConstant d lam Lam H T1) := by positivity
  have hb := Real.sqrt_le_sqrt
    (hhstar.trans (stepSize_le_velocity d lam Lam H T0 T1 kx kv))
  rw [Real.sqrt_sq_eq_abs, abs_of_pos hratio] at hb
  calc
    _ ≤ velocityTubeConstant d lam Lam H T1 *
        (kv / (2 * velocityTubeConstant d lam Lam H T1)) :=
      mul_le_mul_of_nonneg_left hb hc.le
    _ = _ := by field_simp

/-- The source position step restriction gives the half-radius containment bound. -/
theorem propagation_step_position {d : ℕ} {lam Lam H T0 T1 kx kv h : ℝ}
    (hH : 0 ≤ H) (hkx : 0 < kx) (hh : 0 < h)
    (hhstar : h ≤ stepSize d lam Lam H T0 T1 kx kv) :
    positionTubeConstant d lam Lam H T1 * h ^ (3 / 2 : ℝ) ≤ kx / 2 := by
  have hc := (tubeConstants_pos (d := d) (lam := lam) (Lam := Lam) (T1 := T1) hH).2
  have hratio : 0 < kx / (2 * positionTubeConstant d lam Lam H T1) := by positivity
  have hb := Real.rpow_le_rpow hh.le
    (hhstar.trans (stepSize_le_position d lam Lam H T0 T1 kx kv))
    (show (0 : ℝ) ≤ 3 / 2 by norm_num)
  rw [← Real.rpow_mul hratio.le] at hb
  norm_num only [show (2 / 3 : ℝ) * (3 / 2) = 1 by norm_num, Real.rpow_one] at hb
  calc
    _ ≤ positionTubeConstant d lam Lam H T1 *
        (kx / (2 * positionTubeConstant d lam Lam H T1)) :=
      mul_le_mul_of_nonneg_left hb hc.le
    _ = _ := by field_simp

/-- The source jointly fixed parameters satisfy positivity, loss, and damping requirements. -/
theorem propagation_parameters {d : ℕ} (hd : 1 ≤ d) {lam Lam H T0 T1 kx kv : ℝ}
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (hH : 0 < H)
    (hT0 : 0 < T0) (hT1 : T0 ≤ T1) (hkx : 0 < kx) (hkv : 0 < kv) :
    0 < stepSize d lam Lam H T0 T1 kx kv ∧
      0 < barrierCb (barrierL d lam Lam H T1) ∧
      0 < barrierGamma (barrierL d lam Lam H T1) ∧
      barrierGamma (barrierL d lam Lam H T1) < 1 ∧
      ∀ h : ℝ, 0 < h → h ≤ stepSize d lam Lam H T0 T1 kx kv →
        Xi d lam Lam H h * h ≤ (barrierL d lam Lam H T1) ^ 2 / 4 := by
  have hL := barrierL_pos (H := H) hd hlam hLam (hT0.trans_le hT1).le
  obtain ⟨hcb, _⟩ := barrierCb_bounds hL
  obtain ⟨hg0, hg1⟩ := barrierGamma_bounds hL
  exact ⟨stepSize_pos hH.le hT0 hkx hkv, hcb, hg0, hg1,
    fun _ hh hhstar => propagation_step_damping hd hlam hLam hH.le hT0 hT1 hh hhstar⟩

end HypoellipticAleksandrov.KineticAleksandrov.Holder
