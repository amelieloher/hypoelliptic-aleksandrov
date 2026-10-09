module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.OscillationContraction
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.OscillationDecayArithmetic
import Mathlib.Tactic

/-! # Power decay of oscillation from the internally proved one-scale contraction -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Set

/-- The source logarithmic exponent yields uniform oscillation decay at every smaller radius. -/
theorem oscillation_decay (d : ℕ) (hd : 1 ≤ d)
    (lam Lam p C_A : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) (hp : 1 ≤ p) :
    ∃ alpha D : ℝ, 0 < alpha ∧ alpha ≤ 1 ∧
      ∀ A : FullKineticCoefficient d, FullElliptic lam Lam A →
      ∀ O : Set (KineticPoint d), IsOpen O →
      ∀ (P0 : KineticPoint d) (R rho : ℝ), 0 < R → 0 < rho → rho ≤ R →
        closure (backwardCylinder P0 R) ⊆ O →
      ∀ u : KineticPoint d → ℝ, IsAdmissibleSolution A O p C_A u →
        oscillationOn u (backwardCylinder P0 rho) ≤
          D * (rho / R) ^ alpha * oscillationOn u (backwardCylinder P0 R) := by
  obtain ⟨theta, q, ht, ht1, hq, hq1, hcontract⟩ :=
    oscillation_contraction d hd lam Lam p C_A hlam hLam hp
  let alpha := min 1 (Real.log (1 / q) / Real.log (1 / theta))
  obtain ⟨ha, ha1, hqa⟩ := source_holder_exponent ht ht1 hq hq1
  refine ⟨alpha, theta ^ (-alpha), ha, ha1, ?_⟩
  intro A hA O hO P0 R rho hR hrho hrhoR hQ u hu
  have hcompact := isCompact_closure_backwardCylinder P0 R hR
  have hcont := hu.1.1.mono hQ
  have hab := (hcompact.bddAbove_image hcont).mono (image_mono subset_closure)
  have hbb := (hcompact.bddBelow_image hcont).mono (image_mono subset_closure)
  have hosc := oscillationOn_nonneg (backwardCylinder_nonempty P0 hR) hab hbb
  have hrad (n : ℕ) : 0 < theta ^ n * R := mul_pos (pow_pos ht n) hR
  have hrads (n : ℕ) : theta ^ n * R ≤ R :=
    (mul_le_mul_of_nonneg_right (pow_le_one₀ ht.le ht1.le) hR.le).trans_eq (one_mul R)
  have hsub (n : ℕ) := backwardCylinder_radius_mono P0 (hrad n) (hrads n)
  have hiter (n : ℕ) : oscillationOn u (backwardCylinder P0 (theta ^ n * R)) ≤
      q ^ n * oscillationOn u (backwardCylinder P0 R) := by
    induction n with
    | zero => simp only [pow_zero, one_mul, le_refl]
    | succ n ih =>
      have hc := hcontract A hA O hO P0 (theta ^ n * R) (hrad n)
        ((closure_mono (hsub n)).trans hQ) u hu
      have he : theta * (theta ^ n * R) = theta ^ (n + 1) * R := by rw [pow_succ]; ring
      rw [he] at hc
      have hb := hc.trans (mul_le_mul_of_nonneg_left ih hq.le)
      exact hb.trans_eq (by rw [pow_succ]; ring)
  have hx : 0 < rho / R := div_pos hrho hR
  have hx1 : rho / R ≤ 1 := (div_le_one hR).mpr hrhoR
  obtain ⟨n, hnlo, hnhi⟩ := exists_nat_pow_near_of_lt_one hx hx1 ht ht1
  have hsmall : rho ≤ theta ^ n * R := (div_le_iff₀ hR).mp hnhi
  have hm := oscillationOn_mono (backwardCylinder_nonempty P0 hrho)
    (backwardCylinder_radius_mono P0 hrho hsmall)
    (hab.mono (image_mono (hsub n))) (hbb.mono (image_mono (hsub n)))
  have hpower := contraction_power_le_scale_power ht hq.le ha hqa n hnlo
  exact (hm.trans (hiter n)).trans (mul_le_mul_of_nonneg_right hpower hosc)

end HypoellipticAleksandrov.KineticAleksandrov.Holder
