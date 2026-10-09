module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EntranceSlabIntegrated

/-! # Ellipticity-only constants in the quadratic slab count -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous

/-- The slab constant depends only on the upper ellipticity bound. -/
def entranceSlabConstant (Lam : ℝ) : ℝ := 9 / 5 + 32 * Lam / 5

/-- The source slab constant is strictly positive for positive ellipticity. -/
theorem entranceSlabConstant_pos {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    0 < entranceSlabConstant Lam := by
  have hL := hlam.trans_le hLam
  unfold entranceSlabConstant
  positivity

/-- Dividing the source quadratic inequality gives its radius-normalized slab estimate. -/
theorem entranceSlab_mass_arithmetic {r Lam M p g : ℝ}
    (hr : 0 < r) (hLam : 0 ≤ Lam) (hp : 0 ≤ p) (hg : 0 ≤ g)
    (hM : 5 * r ^ 2 / 16 * M ≤ 9 * r ^ 2 / 16 * p + 2 * Lam * g) :
    M ≤ entranceSlabConstant Lam * (p + r ^ (-2 : ℤ) * g) := by
  have hinv : r ^ (-2 : ℤ) = 1 / r ^ 2 := by
    norm_num only [zpow_neg, zpow_ofNat, one_div]
  rw [hinv]
  have hd : M ≤ (9 * r ^ 2 / 16 * p + 2 * Lam * g) / (5 * r ^ 2 / 16) :=
    (le_div_iff₀ (by positivity : 0 < 5 * r ^ 2 / 16)).mpr
      (by simpa only [mul_comm] using hM)
  have he : (9 * r ^ 2 / 16 * p + 2 * Lam * g) / (5 * r ^ 2 / 16) =
      9 / 5 * p + (32 * Lam / 5) * (1 / r ^ 2 * g) := by
    field_simp
    ring
  rw [he] at hd
  have hC1 : (9 / 5 : ℝ) ≤ entranceSlabConstant Lam := by
    unfold entranceSlabConstant
    exact le_add_of_nonneg_right (by positivity)
  have hC2 : 32 * Lam / 5 ≤ entranceSlabConstant Lam := by
    unfold entranceSlabConstant
    exact le_add_of_nonneg_left (by norm_num)
  exact hd.trans (by
    rw [mul_add]
    exact add_le_add (mul_le_mul_of_nonneg_right hC1 hp)
      (mul_le_mul_of_nonneg_right hC2 (by positivity)))

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
