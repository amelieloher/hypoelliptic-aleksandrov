module

public import HypoellipticAleksandrov.LinearAlgebra.LoewnerEntryBound
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Coercivity of the local value-energy flux

A scalar Young inequality absorbs the coefficient and cutoff error row into half of
the elliptic gradient energy, leaving only a multiple of the squared solution value.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Matrix
open scoped BigOperators MatrixOrder

private theorem error_row_young (lam a b : ℝ) (hlam : 0 < lam) :
    -(lam / 2) * b ^ 2 ≤ a * b + a ^ 2 / (2 * lam) := by
  apply (mul_le_mul_iff_right₀ (show 0 < 2 * lam by positivity)).mp
  have hs := sq_nonneg (lam * b + a)
  field_simp
  nlinarith only [hs]

/-- A bounded error row is absorbed into half of the weighted elliptic energy. -/
theorem local_value_energy_flux_coercivity {d : ℕ}
    (lam ρ q K : ℝ) (hlam : 0 < lam) (hK : 0 ≤ K)
    (A : PDE.Mat d) (G B : PDE.Vec d)
    (hA : lam • (1 : PDE.Mat d) ≤ A) (hB : ∀ j, |B j| ≤ K) :
    (lam / 2) * ρ ^ 2 * (∑ j, G j ^ 2) ≤
      ρ ^ 2 * (∑ i, ∑ j, A i j * G j * G i) +
        q * ρ * (∑ j, B j * G j) + (d : ℝ) * K ^ 2 * q ^ 2 / (2 * lam) := by
  have hquad := mul_le_mul_of_nonneg_left (vecDot_mulVec_lower_of_loewner hA G)
    (sq_nonneg ρ)
  have hprincipal : lam * ρ ^ 2 * (∑ j, G j ^ 2) ≤
      ρ ^ 2 * (∑ i, ∑ j, A i j * G j * G i) := by
    have hl : ρ ^ 2 * (lam * PDE.vecNormSq G) = lam * ρ ^ 2 * (∑ j, G j ^ 2) := by
      unfold PDE.vecNormSq PDE.vecDot
      simp only [← pow_two]
      ring
    have hr : ρ ^ 2 * PDE.vecDot G (A *ᵥ G) =
        ρ ^ 2 * (∑ i, ∑ j, A i j * G j * G i) := by
      simp only [PDE.vecDot, Matrix.mulVec, dotProduct, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hl, hr] at hquad
    exact hquad
  have hentry (j : Fin d) : -(lam / 2) * ρ ^ 2 * G j ^ 2 ≤
      q * ρ * (B j * G j) + K ^ 2 * q ^ 2 / (2 * lam) := by
    have hy := error_row_young lam (q * B j) (ρ * G j) hlam
    have hbsq : B j ^ 2 ≤ K ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hK).2 (hB j)
    have hbq : (q * B j) ^ 2 / (2 * lam) ≤ K ^ 2 * q ^ 2 / (2 * lam) := by
      apply div_le_div_of_nonneg_right ?_ (by positivity)
      calc
        _ = q ^ 2 * B j ^ 2 := mul_pow _ _ _
        _ ≤ q ^ 2 * K ^ 2 := mul_le_mul_of_nonneg_left hbsq (sq_nonneg q)
        _ = _ := mul_comm _ _
    have hy' : -(lam / 2) * ρ ^ 2 * G j ^ 2 ≤
        q * ρ * (B j * G j) + (q * B j) ^ 2 / (2 * lam) := by
      convert hy using 1 <;> ring
    exact hy'.trans (add_le_add le_rfl hbq)
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hentry j)
  have herror : -(lam / 2) * ρ ^ 2 * (∑ j, G j ^ 2) ≤
      q * ρ * (∑ j, B j * G j) + (d : ℝ) * K ^ 2 * q ^ 2 / (2 * lam) := by
    convert hsum using 1 <;>
      simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_div_assoc,
      mul_assoc]
    ring
  linarith only [hprincipal, herror]

/-- Bounds on coefficients and cutoff derivatives bound the complete error row. -/
theorem local_value_energy_error_row_abs_le {d : ℕ}
    (ρ Ma Md Kr : ℝ) (hMa : 0 ≤ Ma)
    (hρ : |ρ| ≤ 1) (A D : PDE.Mat d) (R : PDE.Vec d)
    (hA : ∀ i j, |A i j| ≤ Ma) (hD : ∀ i j, |D i j| ≤ Md)
    (hR : ∀ i, |R i| ≤ Kr) (j : Fin d) :
    |∑ i, (2 * A i j * R i + ρ * D i j)| ≤ (d : ℝ) * (2 * Ma * Kr + Md) := by
  calc
    _ ≤ ∑ i, |2 * A i j * R i + ρ * D i j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, (2 * Ma * Kr + Md) := by
      apply Finset.sum_le_sum
      intro i _
      apply (abs_add_le _ _).trans
      apply add_le_add
      · rw [abs_mul, abs_mul, abs_of_nonneg (show 0 ≤ (2 : ℝ) by norm_num)]
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (hA i j) (by norm_num)) (hR i)
          (abs_nonneg _) (mul_nonneg (by norm_num) hMa)
      · rw [abs_mul]
        calc
          _ ≤ 1 * Md := mul_le_mul hρ (hD i j) (abs_nonneg _) (by norm_num)
          _ = Md := one_mul _
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]

/-- The expanded cutoff flux has its exact principal-plus-error-row decomposition. -/
theorem local_value_energy_flux_eq {d : ℕ} (ρ q : ℝ)
    (A D : PDE.Mat d) (G R : PDE.Vec d) :
    (∑ i, ∑ j, (A i j * G j * (ρ ^ 2 * G i + 2 * ρ * R i * q) +
      D i j * G j * q * ρ ^ 2)) =
      ρ ^ 2 * (∑ i, ∑ j, A i j * G j * G i) +
        q * ρ * (∑ j, (∑ i, (2 * A i j * R i + ρ * D i j)) * G j) := by
  have hrow : (∑ j, (∑ i, (2 * A i j * R i + ρ * D i j)) * G j) =
      ∑ i, ∑ j, (2 * A i j * R i + ρ * D i j) * G j := by
    simp_rw [Finset.sum_mul]
    exact Finset.sum_comm
  rw [hrow]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Coercivity also holds for the fully expanded coefficient and cutoff flux. -/
theorem local_value_energy_expanded_flux_coercivity {d : ℕ}
    (lam ρ q K : ℝ) (hlam : 0 < lam) (hK : 0 ≤ K)
    (A D : PDE.Mat d) (G R : PDE.Vec d)
    (hA : lam • (1 : PDE.Mat d) ≤ A)
    (hB : ∀ j, |∑ i, (2 * A i j * R i + ρ * D i j)| ≤ K) :
    (lam / 2) * ρ ^ 2 * (∑ j, G j ^ 2) ≤
      (∑ i, ∑ j, (A i j * G j * (ρ ^ 2 * G i + 2 * ρ * R i * q) +
        D i j * G j * q * ρ ^ 2)) + (d : ℝ) * K ^ 2 * q ^ 2 / (2 * lam) := by
  rw [local_value_energy_flux_eq]
  exact local_value_energy_flux_coercivity lam ρ q K hlam hK A G
    (fun j => ∑ i, (2 * A i j * R i + ρ * D i j)) hA hB

end HypoellipticAleksandrov.Parabolic.LocalHolder
