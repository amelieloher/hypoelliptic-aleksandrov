module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularEquationIntegrals
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularEquationRadial
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Tactic

/-! # The radial coefficients in the actual homogeneous product representation -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- Dividing a radial test by s^n reduces the literal radial exponent by n. -/
theorem bellmanRadialWeight_integral_div (β : ℝ) (ψ : ℝ → ℝ) (n : ℕ) :
    (∫ s, ψ s.val / s.val ^ n ∂bellmanRadialWeight β) =
      ∫ s in Ioi (0 : ℝ), s ^ ((3 - β) - n) * ψ s := by
  rw [bellmanRadialWeight_integral β (fun s : ℝ => ψ s / s ^ n)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s hs
  change s ^ (3 - β) * (ψ s / s ^ n) = s ^ ((3 - β) - n) * ψ s
  rw [Real.rpow_sub hs (3 - β) (n : ℝ), Real.rpow_natCast]
  ring

/-- A positive-position supported integrand has the same positive and full real integral. -/
theorem bellman_positiveIntegral_eq_full {ψ : ℝ → ℝ}
    (hs : Function.support ψ ⊆ Ioi (0 : ℝ)) :
    (∫ s in Ioi (0 : ℝ), ψ s) = ∫ s, ψ s := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro s hn
  by_contra h
  exact hn (hs h)

/-- The two radial factors satisfy the exact relation required by the angular equation. -/
theorem bellmanRadialWeight_deriv_relation (β a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hs : tsupport ζ ⊆ Ioo a b) :
    (∫ s, deriv ζ s.val / s.val ∂bellmanRadialWeight β) =
      (β - 2) * (∫ s, ζ s.val / s.val ^ 2 ∂bellmanRadialWeight β) := by
  have hd : tsupport (deriv ζ) ⊆ Ioo a b := tsupport_deriv_subset.trans hs
  have hs1 : Function.support (fun s : ℝ => s ^ (2 - β) * deriv ζ s) ⊆ Ioc a b := by
    intro s h
    have hz : deriv ζ s ≠ 0 := (mul_ne_zero_iff.mp h).2
    exact ⟨(hd (subset_tsupport _ hz)).1, (hd (subset_tsupport _ hz)).2.le⟩
  have hs2 : Function.support (fun s : ℝ => s ^ (1 - β) * ζ s) ⊆ Ioc a b := by
    intro s h
    have hz : ζ s ≠ 0 := (mul_ne_zero_iff.mp h).2
    exact ⟨(hs (subset_tsupport _ hz)).1, (hs (subset_tsupport _ hz)).2.le⟩
  have hp1 : Function.support (fun s : ℝ => s ^ (2 - β) * deriv ζ s) ⊆ Ioi 0 :=
    fun s h => ha.trans (hs1 h).1
  have hp2 : Function.support (fun s : ℝ => s ^ (1 - β) * ζ s) ⊆ Ioi 0 :=
    fun s h => ha.trans (hs2 h).1
  have h1 := bellmanRadialWeight_integral_div β (deriv ζ) 1
  simp only [pow_one, Nat.cast_one] at h1
  rw [h1, bellmanRadialWeight_integral_div β ζ 2]
  norm_num only [Nat.cast_ofNat]
  have he1 : (3 - β) - 1 = 2 - β := by ring
  have he2 : (3 - β) - 2 = 1 - β := by ring
  rw [he1, he2, bellman_positiveIntegral_eq_full hp1,
    bellman_positiveIntegral_eq_full hp2,
    ← intervalIntegral.integral_eq_integral_of_support_subset hs1,
    ← intervalIntegral.integral_eq_integral_of_support_subset hs2]
  have hza : ζ a = 0 := image_eq_zero_of_notMem_tsupport
    (fun h => (lt_irrefl a) (hs h).1)
  have hzb : ζ b = 0 := image_eq_zero_of_notMem_tsupport
    (fun h => (lt_irrefl b) (hs h).2)
  exact bellmanAngularRadial_integrationByParts β a b ha hab ζ hζ hza hzb

end HypoellipticAleksandrov.KineticAleksandrov
