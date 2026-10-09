module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.OscillationContractionGrowthLimit
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.OscillationContractionGeometry
import Mathlib.Tactic

/-! # Uniform one-scale oscillation contraction from the internal growth theorem -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Set MeasureTheory

/-- The same source comparison data yield a strict, uniform oscillation contraction. -/
theorem oscillation_contraction (d : ℕ) (hd : 1 ≤ d)
    (lam Lam p C_A : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) (hp : 1 ≤ p) :
    ∃ theta q : ℝ, 0 < theta ∧ theta < 1 ∧ 0 < q ∧ q < 1 ∧
      ∀ A : FullKineticCoefficient d, FullElliptic lam Lam A →
      ∀ O : Set (KineticPoint d), IsOpen O →
      ∀ (P0 : KineticPoint d) (R : ℝ), 0 < R →
        closure (backwardCylinder P0 R) ⊆ O →
      ∀ u : KineticPoint d → ℝ, IsAdmissibleSolution A O p C_A u →
        oscillationOn u (backwardCylinder P0 (theta * R)) ≤
          q * oscillationOn u (backwardCylinder P0 R) := by
  obtain ⟨theta, S, r, kappa, ht, ht1, _hr, hk, hk1, _hS, hupper⟩ :=
    exists_growth_half_upper_bound d hd lam Lam p C_A hlam hLam hp
  refine ⟨theta, 1 - kappa / 2, ht, ht1, by linarith only [hk1],
    by linarith only [hk], ?_⟩
  intro A hA O hO P0 R hR hQ u hu
  let Q := backwardCylinder P0 R
  let Qsmall := backwardCylinder P0 (theta * R)
  let Sigma := kineticAffine P0 R '' backwardCylinder S r
  have hQc : IsCompact (closure Q) := isCompact_closure_backwardCylinder P0 R hR
  have huc : ContinuousOn u (closure Q) := hu.1.1.mono hQ
  have habc : BddAbove (u '' closure Q) := hQc.bddAbove_image huc
  have hbbc : BddBelow (u '' closure Q) := hQc.bddBelow_image huc
  have hab : BddAbove (u '' Q) := habc.mono (image_mono subset_closure)
  have hbb : BddBelow (u '' Q) := hbbc.mono (image_mono subset_closure)
  have hsub : Qsmall ⊆ Q := backwardCylinder_radius_mono P0 (mul_pos ht hR)
    ((mul_le_mul_of_nonneg_right ht1.le hR.le).trans_eq (one_mul R))
  have hne := backwardCylinder_nonempty P0 (mul_pos ht hR)
  have hosc : 0 ≤ oscillationOn u Q := oscillationOn_nonneg
    (backwardCylinder_nonempty P0 hR) hab hbb
  by_cases hz : oscillationOn u Q = 0
  · have hm := oscillationOn_mono hne hsub hab hbb
    change oscillationOn u Qsmall ≤ (1 - kappa / 2) * oscillationOn u Q
    simpa only [hz, mul_zero] using hm
  have hpos : 0 < oscillationOn u Q := lt_of_le_of_ne hosc (Ne.symm hz)
  let M := sSup (u '' Q)
  let m := sInf (u '' Q)
  let half := oscillationOn u Q / 2
  have hhalf : 0 < half := div_pos hpos (by norm_num)
  have hM (P : KineticPoint d) (hP : P ∈ closure Q) : u P ≤ M :=
    closure_values_le_sup huc hab hP
  have hm (P : KineticPoint d) (hP : P ∈ closure Q) : m ≤ u P :=
    inf_le_closure_values huc hbb hP
  have hmid : M - half = m + half := by
    dsimp only [half, oscillationOn, M, m]
    ring
  rcases half_density_alternative u Sigma (M - half) with hlo | hhi
  · have himproved := hupper A hA O hO P0 R hR hQ u hu.2 M half hhalf hM hlo
    have hb := oscillationOn_le hne
      (fun P hP => hm P (subset_closure (hsub hP))) himproved
    apply hb.trans_eq
    dsimp only [half, oscillationOn, M, m]
    ring
  · have hneg : IsAdmissibleSupersolution A O p C_A (fun P => -(-u P)) := by
      simpa only [neg_neg] using hu.1
    have hupperneg (P : KineticPoint d) (hP : P ∈ closure Q) : -u P ≤ -m :=
      neg_le_neg (hm P hP)
    have hlevels : {P | M - half ≤ u P} = {P | -u P ≤ -m - half} := by
      ext P
      simp only [mem_ofPred_eq]
      rw [hmid]
      constructor <;> intro h <;> linarith only [h]
    rw [hlevels] at hhi
    have himproved := hupper A hA O hO P0 R hR hQ (fun P => -u P)
      hneg (-m) half hhalf hupperneg hhi
    have hb := oscillationOn_le (a := m + kappa * half) (b := M) hne
      (fun P hP => by have hh := himproved P hP; linarith only [hh])
      (fun P hP => hM P (subset_closure (hsub hP)))
    apply hb.trans_eq
    dsimp only [half, oscillationOn, M, m]
    ring

end HypoellipticAleksandrov.KineticAleksandrov.Holder
