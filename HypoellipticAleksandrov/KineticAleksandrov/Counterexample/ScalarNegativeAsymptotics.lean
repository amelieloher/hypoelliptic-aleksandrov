module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarAsymptotics
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarGammaRatios
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.MAsymptotics
import Mathlib.Tactic

/-!
# The negative scalar tail

Conditional consumption of the complete planned negative-ray M expansion theorem.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open Filter Asymptotics

/-- The first truncation of the literal M expansion is its leading power. -/
theorem mExpansion_one (a b X : ℝ) : Kummer.mExpansion a b 1 X =
    Real.Gamma b / Real.Gamma (b - a) * Real.rpow X (-a) := by
  simp only [Kummer.mExpansion, Finset.sum_range_one, Kummer.poch_zero,
    Nat.factorial_zero, Nat.cast_one, pow_zero, div_one, mul_one]

/-- The leading powers of the two M terms have the source joint coefficient. -/
theorem scalar_negative_leading (gamma : ScalarGamma) (Lam s : ℝ)
    (hLam : 0 < Lam) (hs : 0 < s) :
    gammaA gamma.1 * Kummer.mExpansion (-gamma.1) (2 / 3) 1 (s ^ 3 / 9) -
      gammaB gamma.1 * s / Real.rpow (9 * Lam) (1 / 3) *
        Kummer.mExpansion (1 / 3 - gamma.1) (4 / 3) 1 (s ^ 3 / 9) =
    Real.rpow 9 (-gamma.1) *
      (Pgamma gamma.1 - Qgamma gamma.1 * Real.rpow Lam (-(1 / 3))) *
        Real.rpow s (3 * gamma.1) := by
  rw [mExpansion_one, mExpansion_one]
  rw [show (2 / 3 : ℝ) - -gamma.1 = 2 / 3 + gamma.1 by ring,
    show (4 / 3 : ℝ) - (1 / 3 - gamma.1) = 1 + gamma.1 by ring,
    neg_neg, show -(1 / 3 - gamma.1) = gamma.1 - 1 / 3 by ring,
    scalar_tail_power s 9 gamma.1 hs (by norm_num),
    scalar_tail_power s 9 (gamma.1 - 1 / 3) hs (by norm_num)]
  simp only [Real.rpow_eq_pow]
  have hpow : (9 : ℝ) ^ (-(gamma.1 - 1 / 3)) =
      9 ^ (1 / 3 : ℝ) * 9 ^ (-gamma.1) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 9)]
    congr 1
    ring
  have hsprod : s * s ^ (3 * (gamma.1 - 1 / 3)) = s ^ (3 * gamma.1) := by
    rw [mul_comm s, ← Real.rpow_add_one hs.ne']
    congr 1
    ring
  have hroot : (9 * Lam) ^ (1 / 3 : ℝ) = 9 ^ (1 / 3 : ℝ) * Lam ^ (1 / 3 : ℝ) :=
    Real.mul_rpow (by norm_num) hLam.le
  have ha := gammaA_leading_ratio gamma
  have hb := gammaB_leading_ratio gamma
  rw [hpow, hroot, Real.rpow_neg hLam.le]
  have h9 : (9 : ℝ) ^ (1 / 3 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
  have hL : Lam ^ (1 / 3 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hLam _).ne'
  have he : gammaA gamma.1 *
      (Real.Gamma (2 / 3) / Real.Gamma (2 / 3 + gamma.1)) = Pgamma gamma.1 := by
    simpa only [mul_div_assoc] using ha
  have he' : gammaB gamma.1 *
      (Real.Gamma (4 / 3) / Real.Gamma (1 + gamma.1)) = Qgamma gamma.1 := by
    simpa only [mul_div_assoc] using hb
  calc
    _ = (gammaA gamma.1 * (Real.Gamma (2 / 3) / Real.Gamma (2 / 3 + gamma.1))) *
          9 ^ (-gamma.1) * s ^ (3 * gamma.1) -
        (gammaB gamma.1 * (Real.Gamma (4 / 3) / Real.Gamma (1 + gamma.1))) *
          9 ^ (-gamma.1) / Lam ^ (1 / 3 : ℝ) *
            (s * s ^ (3 * (gamma.1 - 1 / 3))) := by field_simp
    _ = _ := by rw [he, he', hsprod]; ring

section MExpansion

variable (hm : ∀ (a : ℝ) (b : Kummer.Pos), -1 < a → a < b.1 → ∀ N : ℕ,
  IsBigO atTop (fun X => Kummer.M a b (-X) - Kummer.mExpansion a b.1 N X)
    (fun X => Real.rpow X (-a - (N : ℝ))))

include hm

/-- The two rescaled M remainders have exactly the scalar negative-tail orders. -/
theorem scalar_M_remainders_of_M_expansion (gamma : ScalarGamma) :
    IsBigO atTop
      (fun s => Kummer.M (-gamma.1) Kummer.b23 (-(s ^ 3 / 9)) -
        Kummer.mExpansion (-gamma.1) (2 / 3) 1 (s ^ 3 / 9))
      (fun s => Real.rpow s (3 * gamma.1 - 3)) ∧
    IsBigO atTop
      (fun s => s * (Kummer.M (1 / 3 - gamma.1) Kummer.b43 (-(s ^ 3 / 9)) -
        Kummer.mExpansion (1 / 3 - gamma.1) (4 / 3) 1 (s ^ 3 / 9)))
      (fun s => Real.rpow s (3 * gamma.1 - 3)) := by
  have ha1 : -1 < -gamma.1 := by linarith only [gamma.2.2]
  have hb1 : -gamma.1 < Kummer.b23.1 := by
    dsimp only [Kummer.b23]
    linarith only [gamma.2.1]
  have ha2 : -1 < 1 / 3 - gamma.1 := by linarith only [gamma.2.2]
  have hb2 : 1 / 3 - gamma.1 < Kummer.b43.1 := by
    dsimp only [Kummer.b43]
    linarith only [gamma.2.1]
  have hm1 := hm (-gamma.1) Kummer.b23 ha1 hb1 1
  have hm2 := hm (1 / 3 - gamma.1) Kummer.b43 ha2 hb2 1
  simp only [neg_neg, Nat.cast_one, Kummer.b23] at hm1
  simp only [Nat.cast_one, Kummer.b43] at hm2
  rw [show -(1 / 3 - gamma.1) - 1 = gamma.1 - 4 / 3 by ring] at hm2
  have h1 := isBigO_comp_scalar_tail _ (gamma.1 - 1) 9 (by norm_num) hm1
  have h2 := isBigO_comp_scalar_tail _ (gamma.1 - 4 / 3) 9 (by norm_num) hm2
  have hi : IsBigO atTop (fun s : ℝ => s) (fun s => Real.rpow s 1) := by
    simpa only [Real.rpow_eq_pow, Real.rpow_one] using (isBigO_refl (fun s : ℝ => s) atTop)
  have hprod := hi.mul h2
  have he : (fun s : ℝ => Real.rpow s 1 * Real.rpow s (3 * (gamma.1 - 4 / 3)))
      =ᶠ[atTop] fun s => Real.rpow s (3 * gamma.1 - 3) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_add hs]
    congr 1
    ring
  constructor
  · convert h1 using 1
    congr 1
    funext s
    congr 1
    ring
  · exact hprod.congr' (EventuallyEq.refl _ _) he

/-- The full negative-ray remainder has the exact source coefficient and order. -/
theorem Fminus_negative_ray_asymptotic_of_M_expansion (gamma : ScalarGamma) (Lam : ℝ)
    (hLam : 0 < Lam) :
    IsBigO atTop
      (fun s => Fminus gamma Lam (-s) - Real.rpow 9 (-gamma.1) *
        (Pgamma gamma.1 - Qgamma gamma.1 * Real.rpow Lam (-(1 / 3))) *
          Real.rpow s (3 * gamma.1))
      (fun s => Real.rpow s (3 * gamma.1 - 3)) := by
  obtain ⟨h1, h2⟩ := scalar_M_remainders_of_M_expansion hm gamma
  have h := (h1.const_mul_left (gammaA gamma.1)).sub
    (h2.const_mul_left (gammaB gamma.1 / Real.rpow (9 * Lam) (1 / 3)))
  apply h.congr' _ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  rw [← scalar_negative_leading gamma Lam s hLam hs]
  unfold Fminus
  rw [show (-s) ^ 3 / 9 = -(s ^ 3 / 9) by ring]
  ring

/-- The same estimate on the original negative scalar variable. -/
theorem Fminus_asymptotic_of_M_expansion (gamma : ScalarGamma) (Lam : ℝ)
    (hLam : 0 < Lam) :
    IsBigO atBot
      (fun s => Fminus gamma Lam s - Real.rpow 9 (-gamma.1) *
        (Pgamma gamma.1 - Qgamma gamma.1 * Real.rpow Lam (-(1 / 3))) *
          Real.rpow |s| (3 * gamma.1))
      (fun s => Real.rpow |s| (3 * gamma.1 - 3)) := by
  have h := (Fminus_negative_ray_asymptotic_of_M_expansion hm gamma Lam hLam).comp_tendsto
    tendsto_neg_atBot_atTop
  apply h.congr' _ _
  · filter_upwards [eventually_lt_atBot (0 : ℝ)] with s hs
    simp only [Function.comp_def, neg_neg, abs_of_neg hs]
  · filter_upwards [eventually_lt_atBot (0 : ℝ)] with s hs
    simp only [Function.comp_def, abs_of_neg hs]

end MExpansion

/-- The negative scalar tail uses the now proved Kummer M expansion without extra premises. -/
theorem Fminus_asymptotic (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam) :
    IsBigO atBot
      (fun s => Fminus gamma Lam s - Real.rpow 9 (-gamma.1) *
        (Pgamma gamma.1 - Qgamma gamma.1 * Real.rpow Lam (-(1 / 3))) *
          Real.rpow |s| (3 * gamma.1))
      (fun s => Real.rpow |s| (3 * gamma.1 - 3)) :=
  Fminus_asymptotic_of_M_expansion Kummer.M_negative_expansion gamma Lam hLam

/-- Matching selects exactly the positive piece's leading coefficient. -/
theorem scalar_matching_trace_coefficient (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam)
    (hmatch : Pgamma gamma.1 - Qgamma gamma.1 * Real.rpow Lam (-(1 / 3)) =
      Real.rpow Lam (-gamma.1)) :
    Real.rpow 9 (-gamma.1) *
      (Pgamma gamma.1 - Qgamma gamma.1 * Real.rpow Lam (-(1 / 3))) =
        Real.rpow (9 * Lam) (-gamma.1) := by
  rw [hmatch]
  simp only [Real.rpow_eq_pow]
  exact (Real.mul_rpow (by norm_num) hLam.le).symm

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
