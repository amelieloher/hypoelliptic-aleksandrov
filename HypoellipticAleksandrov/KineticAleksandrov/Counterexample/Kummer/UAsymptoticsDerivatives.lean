module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.UAsymptotics
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.BasisM
import Mathlib.Tactic

/-!
# Exact derivatives of the finite expansion and its remainder

The derivative remainder is a shifted integral remainder. This proves derivative
estimates from convergent integrals rather than differentiating a Landau estimate.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

/-- The finite U expansion as a sum of real powers on the positive axis. -/
theorem uExpansion_eq_sum_rpow (a b : ℝ) (N : ℕ) (z : ℝ) (hz : 0 < z) :
    uExpansion a b N z = ∑ n ∈ Finset.range N,
      ((-1 : ℝ) ^ n * poch a n * poch (a - b + 1) n / (n.factorial : ℝ)) *
        z ^ (-a - (n : ℝ)) := by
  simp only [uExpansion, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  have heq : z ^ (-a) * z⁻¹ ^ n = z ^ (-a - (n : ℝ)) := by
    rw [sub_eq_add_neg, Real.rpow_add hz]
    simp only [Real.rpow_neg_eq_inv_rpow, Real.rpow_natCast]
  calc
    _ = ((-1 : ℝ) ^ n * poch a n * poch (a - b + 1) n / (n.factorial : ℝ)) *
        (z ^ (-a) * z⁻¹ ^ n) := by ring
    _ = _ := by rw [heq]

/-- Parameter recurrence for the derivative of a finite U expansion. -/
theorem hasDerivAt_uExpansion (a b : ℝ) (N : ℕ) (z : ℝ) (hz : 0 < z) :
    HasDerivAt (uExpansion a b N) (-a * uExpansion (a + 1) (b + 1) N z) z := by
  let k : ℕ → ℝ := fun n =>
    (-1 : ℝ) ^ n * poch a n * poch (a - b + 1) n / (n.factorial : ℝ)
  have hd : HasDerivAt (fun w => ∑ n ∈ Finset.range N, k n * w ^ (-a - (n : ℝ)))
      (∑ n ∈ Finset.range N, k n * ((-a - (n : ℝ)) *
        z ^ (-a - (n : ℝ) - 1))) z := by
    apply HasDerivAt.fun_sum
    intro n _
    exact (Real.hasDerivAt_rpow_const (Or.inl hz.ne')).const_mul (k n)
  have heq : uExpansion a b N =ᶠ[𝓝 z]
      fun w => ∑ n ∈ Finset.range N, k n * w ^ (-a - (n : ℝ)) := by
    filter_upwards [Ioi_mem_nhds hz] with w hw
    exact uExpansion_eq_sum_rpow a b N w hw
  have hv : -a * uExpansion (a + 1) (b + 1) N z =
      ∑ n ∈ Finset.range N, k n * ((-a - (n : ℝ)) * z ^ (-a - (n : ℝ) - 1)) := by
    rw [uExpansion_eq_sum_rpow (a + 1) (b + 1) N z hz, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    have hp : a * poch (a + 1) n = poch a n * (a + n) := by
      rw [← poch_succ_left, poch_succ]
    rw [show a + 1 - (b + 1) + 1 = a - b + 1 by ring,
      show -(a + 1) - (n : ℝ) = -a - (n : ℝ) - 1 by ring]
    dsimp only [k]
    calc
      _ = -((-1 : ℝ) ^ n * (a * poch (a + 1) n) *
          poch (a - b + 1) n / (n.factorial : ℝ)) * z ^ (-a - (n : ℝ) - 1) := by ring
      _ = _ := by rw [hp]; ring
  rw [hv]
  exact hd.congr_of_eventuallyEq heq

/-- Shape shift of the normalized integral derivative. -/
theorem hasDerivAt_UIr_shift (a : Pos) (b z : ℝ) (hz : 0 < z) :
    HasDerivAt (UIr a b)
      (-a.1 * UIr ⟨a.1 + 1, add_pos a.2 zero_lt_one⟩ (b + 1) z) z := by
  have heq : -a.1 * UIr ⟨a.1 + 1, add_pos a.2 zero_lt_one⟩ (b + 1) z =
      -(Real.Gamma a.1)⁻¹ * laplaceIntegral (a.1 + 1) (b + 1) z := by
    change -a.1 * ((Real.Gamma (a.1 + 1))⁻¹ * laplaceIntegral (a.1 + 1) (b + 1) z) = _
    rw [Real.Gamma_add_one a.2.ne']
    field_simp [a.2.ne', (Real.Gamma_pos_of_pos a.2).ne']
  rw [heq]
  exact hasDerivAt_UIr a b z hz

/-- The derivative remainder is exactly a simultaneous parameter shift. -/
theorem hasDerivAt_UIr_remainder (a : Pos) (b : ℝ) (N : ℕ) (z : ℝ) (hz : 0 < z) :
    HasDerivAt (fun w => UIr a b w - uExpansion a.1 b N w)
      (-a.1 * (UIr ⟨a.1 + 1, add_pos a.2 zero_lt_one⟩ (b + 1) z -
        uExpansion (a.1 + 1) (b + 1) N z)) z := by
  have h := (hasDerivAt_UIr_shift a b z hz).sub (hasDerivAt_uExpansion a.1 b N z hz)
  convert h using 1
  ring

/-- First derivative expansion of the integral, proved from shifted remainders. -/
theorem UIr_expansion_deriv (a : Pos) (b : ℝ) (N : ℕ) :
    Asymptotics.IsBigO atTop
      (deriv (fun z => UIr a b z - uExpansion a.1 b N z))
      (fun z => Real.rpow z (-a.1 - (N : ℝ) - 1)) := by
  let c : Pos := ⟨a.1 + 1, add_pos a.2 zero_lt_one⟩
  have h := (UIr_expansion c (b + 1) N).const_mul_left (-a.1)
  apply h.congr' _ _
  · filter_upwards [Ioi_mem_atTop (0 : ℝ)] with z hz
    exact (hasDerivAt_UIr_remainder a b N z hz).deriv.symm
  · filter_upwards with z
    congr 1
    dsimp only [c]
    ring

/-- The second remainder derivative is another exact integral shift. -/
theorem hasDerivAt_deriv_UIr_remainder (a : Pos) (b : ℝ) (N : ℕ) (z : ℝ) (hz : 0 < z) :
    HasDerivAt (deriv (fun w => UIr a b w - uExpansion a.1 b N w))
      (a.1 * (a.1 + 1) *
        (UIr ⟨a.1 + 1 + 1, add_pos (add_pos a.2 zero_lt_one) zero_lt_one⟩ (b + 1 + 1) z -
          uExpansion (a.1 + 1 + 1) (b + 1 + 1) N z)) z := by
  let c : Pos := ⟨a.1 + 1, add_pos a.2 zero_lt_one⟩
  have hd := (hasDerivAt_UIr_remainder c (b + 1) N z hz).const_mul (-a.1)
  have heq : deriv (fun w => UIr a b w - uExpansion a.1 b N w) =ᶠ[𝓝 z]
      fun w => -a.1 * (UIr c (b + 1) w - uExpansion c.1 (b + 1) N w) := by
    filter_upwards [Ioi_mem_nhds hz] with w hw
    exact (hasDerivAt_UIr_remainder a b N w hw).deriv
  have h := hd.congr_of_eventuallyEq heq
  convert h using 1
  dsimp only [c]
  ring

/-- Second derivative expansion of the integral, using two proved shifts. -/
theorem UIr_expansion_deriv2 (a : Pos) (b : ℝ) (N : ℕ) :
    Asymptotics.IsBigO atTop
      (deriv (deriv (fun z => UIr a b z - uExpansion a.1 b N z)))
      (fun z => Real.rpow z (-a.1 - (N : ℝ) - 2)) := by
  let d : Pos := ⟨a.1 + 1 + 1, add_pos (add_pos a.2 zero_lt_one) zero_lt_one⟩
  have h := (UIr_expansion d (b + 1 + 1) N).const_mul_left (a.1 * (a.1 + 1))
  apply h.congr' _ _
  · filter_upwards [Ioi_mem_atTop (0 : ℝ)] with z hz
    exact (hasDerivAt_deriv_UIr_remainder a b N z hz).deriv.symm
  · filter_upwards with z
    congr 1
    dsimp only [d]
    ring

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
