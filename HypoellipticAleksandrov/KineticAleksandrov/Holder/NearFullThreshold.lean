module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.NearFull
import Mathlib.Tactic

/-! # Uniform density threshold for the near-full estimate -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Set MeasureTheory

/-- A single density threshold gives the source three-quarter cap lower bound. -/
theorem near_full_threshold (d : ℕ) (hd : 1 ≤ d) (Lam p C_A : ℝ) (hp : 1 ≤ p) :
    ∃ eta : ℝ, 0 < eta ∧ eta < 1 ∧
      ∀ lam : ℝ, 0 < lam → lam ≤ Lam →
      ∀ A : FullKineticCoefficient d, FullElliptic lam Lam A →
      ∀ (P₀ : KineticPoint d) (R ell : ℝ), 0 < R → 0 ≤ ell →
      ∀ O : Set (KineticPoint d), IsOpen O → closure (backwardCylinder P₀ R) ⊆ O →
      ∀ u : KineticPoint d → ℝ, (∀ P ∈ O, 0 ≤ u P) →
        IsAdmissibleSupersolution A O p C_A u →
        (1 - eta) * (volume (backwardCylinder P₀ R)).toReal ≤
          (volume ({P | ell ≤ u P} ∩ backwardCylinder P₀ R)).toReal →
      ∀ P ∈ kineticAffine P₀ R '' cap d, (3 / 4 : ℝ) * ell ≤ u P := by
  obtain ⟨C, hC⟩ := near_full d hd Lam p C_A hp
  let B := max C 0
  let delta := 1 / (4 * (B + 1))
  let eta := min (1 / 2 : ℝ) (delta ^ p)
  have hB : 0 ≤ B := le_max_right _ _
  have hden : 0 < 4 * (B + 1) := by positivity
  have hdelta : 0 < delta := one_div_pos.mpr hden
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have heta : 0 < eta := lt_min (by norm_num) (Real.rpow_pos_of_pos hdelta _)
  have heta1 : eta < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hroot : eta ^ (1 / p) ≤ delta := by
    calc
      _ ≤ (delta ^ p) ^ (1 / p) := Real.rpow_le_rpow heta.le
        (min_le_right _ _) (one_div_nonneg.mpr hp0.le)
      _ = delta := by rw [← Real.rpow_mul hdelta.le]; simp [hp0.ne']
  have hsmall : B * delta ≤ 1 / 4 := by
    change B * (1 / (4 * (B + 1))) ≤ 1 / 4
    rw [mul_one_div, div_le_iff₀ hden]
    linarith only [hB]
  have hCsmall : C * eta ^ (1 / p) ≤ 1 / 4 :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg heta.le _)).trans
      ((mul_le_mul_of_nonneg_left hroot hB).trans hsmall)
  refine ⟨eta, heta, heta1, ?_⟩
  intro lam hlam hLam A hA P₀ R ell hR hell O hO hQO u hu0 hu hdensity P hP
  exact (mul_le_mul_of_nonneg_right (by linarith only [hCsmall]) hell).trans
    (hC lam hlam hLam A hA P₀ R ell eta hR hell heta heta1 O hO hQO u hu0 hu hdensity P hP)

end HypoellipticAleksandrov.KineticAleksandrov.Holder
