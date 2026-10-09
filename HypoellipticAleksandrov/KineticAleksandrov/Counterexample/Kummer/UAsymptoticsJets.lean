module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.UAsymptoticsDerivatives
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.MAsymptotics
import Mathlib.Tactic

/-!
# First two derivative remainders for the transformed U solution

Product differentiation is applied to the actual integral remainder. Each term is
estimated by the independently proved shifted-integral expansions.
-/

@[expose] public noncomputable section

open Set Filter Asymptotics
open scoped Topology

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

/-- Multiplication by a real power adds its exponent to an existing remainder bound. -/
theorem rpow_mul_isBigO (f : ℝ → ℝ) (p r : ℝ)
    (h : IsBigO atTop f (fun z => z ^ r)) :
    IsBigO atTop (fun z => z ^ p * f z) (fun z => z ^ (p + r)) := by
  have hh := (isBigO_refl (fun z : ℝ => z ^ p) atTop).mul h
  apply hh.congr' EventuallyEq.rfl _
  filter_upwards [Ioi_mem_atTop (0 : ℝ)] with z hz
  exact (Real.rpow_add hz p r).symm

/-- A version with an explicitly identified sum of exponents. -/
theorem rpow_mul_isBigO_of_add_eq (f : ℝ → ℝ) (p r e : ℝ)
    (h : IsBigO atTop f (fun z => z ^ r)) (he : p + r = e) :
    IsBigO atTop (fun z => z ^ p * f z) (fun z => Real.rpow z e) := by
  simp only [Real.rpow_eq_pow, ← he]
  exact rpow_mul_isBigO f p r h

/-- The transformed remainder is a power times the positive integral remainder. -/
theorem UNr_remainder_eq_power (a : NegThird) (N : ℕ) (z : ℝ) (hz : 0 < z) :
    UNr a z - uExpansion a.1 (2 / 3) N z =
      z ^ (1 / 3 : ℝ) *
        (UIr ⟨a.1 + 1 / 3, by linarith only [a.2.1]⟩ (4 / 3) z -
          uExpansion (a.1 + 1 / 3) (4 / 3) N z) := by
  rw [mul_sub, uExpansion_transform a N z hz]
  rfl

/-- The first derivative remainder has one additional inverse power. -/
theorem UNr_expansion_deriv (a : NegThird) (N : ℕ) :
    IsBigO atTop (deriv (fun z => UNr a z - uExpansion a.1 (2 / 3) N z))
      (fun z => Real.rpow z (-a.1 - (N : ℝ) - 1)) := by
  let c : Pos := ⟨a.1 + 1 / 3, by linarith only [a.2.1]⟩
  let f : ℝ → ℝ := fun z => UIr c (4 / 3) z - uExpansion c.1 (4 / 3) N z
  have h0 : IsBigO atTop f (fun z => z ^ (-c.1 - (N : ℝ))) := by
    simpa only [Real.rpow_eq_pow] using UIr_expansion c (4 / 3) N
  have h1 : IsBigO atTop (deriv f) (fun z => z ^ (-c.1 - (N : ℝ) - 1)) := by
    simpa only [Real.rpow_eq_pow] using UIr_expansion_deriv c (4 / 3) N
  have ha := (rpow_mul_isBigO f (1 / 3 - 1) (-c.1 - (N : ℝ)) h0).const_mul_left (1 / 3 : ℝ)
  have hb := rpow_mul_isBigO (deriv f) (1 / 3) (-c.1 - (N : ℝ) - 1) h1
  have ha' : IsBigO atTop (fun z => (1 / 3 : ℝ) * (z ^ (1 / 3 - 1 : ℝ) * f z))
      (fun z => Real.rpow z (-a.1 - (N : ℝ) - 1)) := by
    apply ha.congr' EventuallyEq.rfl _
    filter_upwards with z
    rw [Real.rpow_eq_pow]
    congr 1
    dsimp only [c]
    ring
  have hb' : IsBigO atTop (fun z => z ^ (1 / 3 : ℝ) * deriv f z)
      (fun z => Real.rpow z (-a.1 - (N : ℝ) - 1)) := by
    apply hb.congr' EventuallyEq.rfl _
    filter_upwards with z
    rw [Real.rpow_eq_pow]
    congr 1
    dsimp only [c]
    ring
  apply (ha'.add hb').congr' _ EventuallyEq.rfl
  filter_upwards [Ioi_mem_atTop (0 : ℝ)] with z hz
  have heq : (fun w => UNr a w - uExpansion a.1 (2 / 3) N w) =ᶠ[𝓝 z]
      fun w => w ^ (1 / 3 : ℝ) * f w := by
    filter_upwards [Ioi_mem_nhds hz] with w hw
    exact UNr_remainder_eq_power a N w hw
  have hf := (hasDerivAt_UIr_remainder c (4 / 3) N z hz).differentiableAt.hasDerivAt
  have hd := ((hasDerivAt_power_mul f (1 / 3) z hz hf).congr_of_eventuallyEq heq).deriv
  exact (by convert hd.symm using 1; ring)

/-- The second derivative remainder has two additional inverse powers. -/
theorem UNr_expansion_deriv2 (a : NegThird) (N : ℕ) :
    IsBigO atTop (deriv (deriv (fun z => UNr a z - uExpansion a.1 (2 / 3) N z)))
      (fun z => Real.rpow z (-a.1 - (N : ℝ) - 2)) := by
  let c : Pos := ⟨a.1 + 1 / 3, by linarith only [a.2.1]⟩
  let f : ℝ → ℝ := fun z => UIr c (4 / 3) z - uExpansion c.1 (4 / 3) N z
  have h0 : IsBigO atTop f (fun z => z ^ (-c.1 - (N : ℝ))) := by
    simpa only [Real.rpow_eq_pow] using UIr_expansion c (4 / 3) N
  have h1 : IsBigO atTop (deriv f) (fun z => z ^ (-c.1 - (N : ℝ) - 1)) := by
    simpa only [Real.rpow_eq_pow] using UIr_expansion_deriv c (4 / 3) N
  have h2 : IsBigO atTop (deriv (deriv f)) (fun z => z ^ (-c.1 - (N : ℝ) - 2)) := by
    simpa only [Real.rpow_eq_pow] using UIr_expansion_deriv2 c (4 / 3) N
  have ha := (rpow_mul_isBigO_of_add_eq f (1 / 3 - 2) (-c.1 - (N : ℝ))
    (-a.1 - (N : ℝ) - 2) h0 (by dsimp only [c]; ring)).const_mul_left
      ((1 / 3 : ℝ) * (1 / 3 - 1))
  have hb := (rpow_mul_isBigO_of_add_eq (deriv f) (1 / 3 - 1) (-c.1 - (N : ℝ) - 1)
    (-a.1 - (N : ℝ) - 2) h1 (by dsimp only [c]; ring)).const_mul_left (2 * (1 / 3 : ℝ))
  have hc := rpow_mul_isBigO_of_add_eq (deriv (deriv f)) (1 / 3) (-c.1 - (N : ℝ) - 2)
    (-a.1 - (N : ℝ) - 2) h2 (by dsimp only [c]; ring)
  apply ((ha.add hb).add hc).congr' _ EventuallyEq.rfl
  filter_upwards [Ioi_mem_atTop (0 : ℝ)] with z hz
  have heq : (fun w => UNr a w - uExpansion a.1 (2 / 3) N w) =ᶠ[𝓝 z]
      fun w => w ^ (1 / 3 : ℝ) * f w := by
    filter_upwards [Ioi_mem_nhds hz] with w hw
    exact UNr_remainder_eq_power a N w hw
  have hf : ∀ w ∈ Ioi (0 : ℝ), HasDerivAt f (deriv f w) w := by
    intro w hw
    exact (hasDerivAt_UIr_remainder c (4 / 3) N w hw).differentiableAt.hasDerivAt
  have hf' := (hasDerivAt_deriv_UIr_remainder c (4 / 3) N z hz).differentiableAt.hasDerivAt
  have hd := deriv_deriv_power_mul f (1 / 3) z hz hf hf'
  have hder := heq.deriv.deriv_eq
  rw [hd] at hder
  exact (by convert hder.symm using 1; ring)

/-- The first two derivative remainders, including the undifferentiated order. -/
theorem UNr_expansion_jet (a : NegThird) (N j : ℕ) (hj : j ≤ 2) :
    IsBigO atTop (jet j (fun z => UNr a z - uExpansion a.1 (2 / 3) N z))
      (fun z => Real.rpow z (-a.1 - (N : ℝ) - (j : ℝ))) := by
  have hjcases : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hjcases with rfl | rfl | rfl
  · simpa only [jet, Function.iterate_zero_apply, Nat.cast_zero, sub_zero] using UNr_expansion a N
  · simpa only [jet, Function.iterate_one, Nat.cast_one] using UNr_expansion_deriv a N
  · simpa only [jet, Function.iterate_succ_apply, Function.iterate_zero_apply,
      Nat.cast_ofNat] using UNr_expansion_deriv2 a N

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
