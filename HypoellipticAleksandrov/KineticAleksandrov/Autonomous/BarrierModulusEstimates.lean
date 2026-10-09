module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BarrierModulusReference

/-! # The source coordinate modulus, derived from actual C² homogeneity -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BarrierRegularization
open HypoellipticAleksandrov Set MeasureTheory

/-- Recover a point from its positive-radius kinetic normalization. -/
theorem barrier_normalized_point (r : ℝ) (hr : 0 < r) (x v : ℝ) :
    bellmanPlaneDilation r (x / r ^ 3, v / r) = (x, v) := by
  simp only [bellmanPlaneDilation]
  congr 1 <;> field_simp

/-- Rescaling a uniform position increment produces its exact alpha/3 power. -/
theorem barrier_position_increment {alpha : ℝ} {phi : (ℝ × ℝ) → ℝ}
    (h : IsBellmanHomogeneous alpha phi) (D : ℝ)
    (hb : ∀ x y v : ℝ, |y - x| ≤ 1 →
      |bellmanOriginExtension phi (y, v) - bellmanOriginExtension phi (x, v)| ≤ D)
    (x y v : ℝ) :
    |bellmanOriginExtension phi (y, v) - bellmanOriginExtension phi (x, v)| ≤
      D * |y - x| ^ (alpha / 3) := by
  by_cases hxy : y = x
  · subst y
    rw [sub_self, abs_zero]
    exact mul_nonneg (le_trans (abs_nonneg _) (hb x x v (by simp)))
      (Real.rpow_nonneg (abs_nonneg _) _)
  let r := |y - x| ^ (1 / 3 : ℝ)
  have hdiff : 0 < |y - x| := abs_pos.mpr (sub_ne_zero.mpr hxy)
  have hr : 0 < r := Real.rpow_pos_of_pos hdiff _
  have hr3 : r ^ 3 = |y - x| := by
    dsimp only [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hdiff.le]
    norm_num
  have hn : |y / r ^ 3 - x / r ^ 3| ≤ 1 := by
    rw [← sub_div, abs_div, abs_of_pos (pow_pos hr _), hr3, div_self hdiff.ne']
  have hh := hb (x / r ^ 3) (y / r ^ 3) (v / r) hn
  have hx := barrierExtension_scaling h r hr (x / r ^ 3, v / r)
  have hy := barrierExtension_scaling h r hr (y / r ^ 3, v / r)
  rw [barrier_normalized_point r hr] at hx hy
  rw [hy, hx, ← mul_sub, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hr alpha)]
  have hpower : r ^ alpha = |y - x| ^ (alpha / 3) := by
    dsimp only [r]
    rw [← Real.rpow_mul hdiff.le]
    congr 1
    ring
  exact (mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hr.le _)).trans_eq
    (by rw [hpower, mul_comm])

/-- Rescaling a uniform velocity increment produces its exact alpha power. -/
theorem barrier_velocity_increment {alpha : ℝ} {phi : (ℝ × ℝ) → ℝ}
    (h : IsBellmanHomogeneous alpha phi) (D : ℝ)
    (hb : ∀ x y X : ℝ, |y - x| ≤ 1 →
      |bellmanOriginExtension phi (X, y) - bellmanOriginExtension phi (X, x)| ≤ D)
    (x y X : ℝ) :
    |bellmanOriginExtension phi (X, y) - bellmanOriginExtension phi (X, x)| ≤
      D * |y - x| ^ alpha := by
  by_cases hxy : y = x
  · subst y
    rw [sub_self, abs_zero]
    exact mul_nonneg (le_trans (abs_nonneg _) (hb x x X (by simp)))
      (Real.rpow_nonneg (abs_nonneg _) _)
  let r := |y - x|
  have hr : 0 < r := abs_pos.mpr (sub_ne_zero.mpr hxy)
  have hn : |y / r - x / r| ≤ 1 := by
    rw [← sub_div, abs_div, abs_of_pos hr]
    exact le_of_eq (div_self hr.ne')
  have hh := hb (x / r) (y / r) (X / r ^ 3) hn
  have hx := barrierExtension_scaling h r hr (X / r ^ 3, x / r)
  have hy := barrierExtension_scaling h r hr (X / r ^ 3, y / r)
  rw [barrier_normalized_point r hr] at hx hy
  rw [hy, hx, ← mul_sub, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hr alpha)]
  exact (mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hr.le _)).trans_eq (mul_comm _ _)

/-- The actual extended Bellman witness has the source modulus without a new analytic premise. -/
theorem barrier_coordinate_modulus {alpha : ℝ} {phi : (ℝ × ℝ) → ℝ}
    (h : IsBellmanHomogeneous alpha phi) (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ z w : ℝ × ℝ,
      |bellmanOriginExtension phi z - bellmanOriginExtension phi w| ≤
        D * (|z.1 - w.1| ^ (alpha / 3) + |z.2 - w.2| ^ alpha) := by
  obtain ⟨D, hD, hb⟩ := barrier_reference_increments h ha ha1
  refine ⟨D, hD, fun z w => ?_⟩
  have hX := barrier_position_increment h D (fun x y v hh => (hb x y v hh).1)
    w.1 z.1 z.2
  have hv := barrier_velocity_increment h D (fun x y X hh => (hb x y X hh).2)
    w.2 z.2 w.1
  have hh := abs_sub_le (bellmanOriginExtension phi z)
    (bellmanOriginExtension phi (w.1, z.2)) (bellmanOriginExtension phi w)
  exact hh.trans (by simpa only [mul_add] using add_le_add hX hv)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BarrierRegularization
