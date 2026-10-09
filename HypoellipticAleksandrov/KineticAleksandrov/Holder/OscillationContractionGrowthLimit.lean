module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.Assembly
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.AdmissibilityAffine
import Mathlib.Tactic

/-! # The half-density growth comparison and its positive-domain epsilon limit -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Set MeasureTheory

/-- The growth constants give an upper value improvement from a half-density lower sample. -/
theorem exists_growth_half_upper_bound (d : ℕ) (hd : 1 ≤ d) (lam Lam p C_A : ℝ)
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (hp : 1 ≤ p) :
    ∃ (theta : ℝ) (S : KineticPoint d) (r kappa : ℝ),
      0 < theta ∧ theta < 1 ∧ 0 < r ∧ 0 < kappa ∧ kappa ≤ 1 ∧
      closure (backwardCylinder S r) ⊆
        backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1 ∧
      ∀ A : FullKineticCoefficient d, FullElliptic lam Lam A →
      ∀ O : Set (KineticPoint d), IsOpen O →
      ∀ (P0 : KineticPoint d) (R : ℝ), 0 < R → closure (backwardCylinder P0 R) ⊆ O →
      ∀ u : KineticPoint d → ℝ, IsAdmissibleSupersolution A O p C_A (fun P => -u P) →
      ∀ b h : ℝ, 0 < h → (∀ P ∈ closure (backwardCylinder P0 R), u P ≤ b) →
        (1 / 2 : ℝ) * (volume (kineticAffine P0 R '' backwardCylinder S r)).toReal ≤
          (volume ({P | u P ≤ b - h} ∩
            kineticAffine P0 R '' backwardCylinder S r)).toReal →
        ∀ P ∈ backwardCylinder P0 (theta * R), u P ≤ b - kappa * h := by
  obtain ⟨theta, ht, ht1, S, r, hr, hS, hbeta⟩ :=
    kinetic_growth_lemma_aux d hd lam Lam p C_A hlam hLam hp
  obtain ⟨k, hk, hbound⟩ := hbeta (1 / 2) (by norm_num) (by norm_num)
  refine ⟨theta, S, r, min k 1, ht, ht1, hr, lt_min hk (by norm_num),
    min_le_right _ _, hS, ?_⟩
  intro A hA O hO P0 R hR hQ u hu b h hh hupper hdense P hP
  have hcont : ContinuousOn u O := by
    have heq : (-(fun P => -u P)) = u := by funext P; simp only [Pi.neg_apply, neg_neg]
    rw [← heq]
    exact hu.1.neg
  have hlocal : ∀ epsilon : ℝ, 0 < epsilon → u P ≤ b - min k 1 * h + epsilon := by
    intro epsilon hepsilon
    let U := O ∩ {Z | u Z < b + epsilon}
    have hU : IsOpen U := hcont.isOpen_inter_preimage hO isOpen_Iio
    have hQU : closure (backwardCylinder P0 R) ⊆ U := by
      intro Z hZ
      exact ⟨hQ hZ, (hupper Z hZ).trans_lt (by linarith only [hepsilon])⟩
    let w := fun Z => h⁻¹ * (-u Z) + (b + epsilon) / h
    have hw : IsAdmissibleSupersolution A U p C_A w :=
      (admissible_pos_affine hu h⁻¹ ((b + epsilon) / h) (inv_pos.mpr hh)).mono
        inter_subset_left
    have hn : ∀ Z ∈ U, 0 ≤ w Z := by
      intro Z hZ
      dsimp only [w]
      rw [inv_mul_eq_div, ← add_div]
      have hz : u Z < b + epsilon := hZ.2
      exact div_nonneg (by linarith only [hz]) hh.le
    have hlevels : {Z | u Z ≤ b - h} ∩ kineticAffine P0 R '' backwardCylinder S r ⊆
        {Z | 1 ≤ w Z} ∩ kineticAffine P0 R '' backwardCylinder S r := by
      intro Z hZ
      refine ⟨?_, hZ.2⟩
      change 1 ≤ h⁻¹ * (-u Z) + (b + epsilon) / h
      rw [inv_mul_eq_div, ← add_div]
      apply (le_div_iff₀ hh).mpr
      have hz : u Z ≤ b - h := hZ.1
      linarith only [hz, hepsilon]
    have hfinite : volume (kineticAffine P0 R '' backwardCylinder S r) ≠ ⊤ := by
      have hinside : kineticAffine P0 R '' backwardCylinder S r ⊆ backwardCylinder P0 R := by
        rw [← kineticAffine_image_unitCylinder P0 hR]
        exact image_mono (subset_closure.trans hS)
      exact ne_top_of_le_ne_top (Covering.volume_cylinder_pos_ne_top P0 hR).2
        (measure_mono hinside)
    have hdenw : (1 / 2 : ℝ) *
        (volume (kineticAffine P0 R '' backwardCylinder S r)).toReal ≤
          (volume ({Z | 1 ≤ w Z} ∩ kineticAffine P0 R '' backwardCylinder S r)).toReal :=
      hdense.trans (ENNReal.toReal_mono
        (ne_top_of_le_ne_top hfinite (measure_mono inter_subset_right)) (measure_mono hlevels))
    have hkP := hbound A hA.1 hA.2.1 hA.2.2.1 hA.2.2.2 P0 R hR U hU hQU
      w hn hw hdenw P hP
    have hkP' : min k 1 ≤ w P := (min_le_left _ _).trans hkP
    dsimp only [w] at hkP'
    rw [inv_mul_eq_div, ← add_div, le_div_iff₀ hh] at hkP'
    linarith only [hkP']
  apply le_of_forall_pos_le_add
  exact hlocal

end HypoellipticAleksandrov.KineticAleksandrov.Holder
