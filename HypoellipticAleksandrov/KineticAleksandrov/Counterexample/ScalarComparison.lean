module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarContinuity
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarPositive
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2SpectralCompact
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ShellGeometry
import Mathlib.Tactic

/-!
# Scalar kinetic gauge comparison

Continuity and strict positivity on the compact unit gauge shell give the two-sided bound.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open Set

/-- The actual reflected source profile is comparable with the literal native kinetic gauge. -/
theorem scalarProfile_comparison (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam)
    (hmatch : Pgamma gamma.1 - Qgamma gamma.1 * Real.rpow Lam (-(1 / 3)) =
      Real.rpow Lam (-gamma.1)) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ q : XV 1,
      c * Real.rpow (rho q) (3 * gamma.1) ≤ scalarProfile gamma Lam q ∧
      scalarProfile gamma Lam q ≤ C * Real.rpow (rho q) (3 * gamma.1) := by
  let K : Set (XV 1) := {q | rho q = 1}
  have hK : IsCompact K := (isCompact_rho_sublevel 1 1).of_isClosed_subset
    (isClosed_eq (continuous_rho 1) continuous_const) (fun _ h => le_of_eq h)
  have hKnz : ∀ q ∈ K, q ≠ 0 := by
    intro q hq hz
    have hh : rho q = 1 := hq
    simp only [hz, rho_zero] at hh
    norm_num at hh
  obtain ⟨c, C, hc, hcC, hbound⟩ := exists_positive_bounds_on_compact K hK
    (scalarProfile gamma Lam) (scalarProfile_continuous gamma Lam hLam hmatch).continuousOn
    (fun q hq => scalarProfile_pos gamma Lam hLam hmatch q (hKnz q hq))
  refine ⟨c, C, hc, hcC, ?_⟩
  intro q
  by_cases hq : q = 0
  · subst q
    simp only [rho_zero, scalarProfile_zero, Real.rpow_eq_pow,
      Real.zero_rpow (mul_pos (by norm_num : (0 : ℝ) < 3) gamma.2.1).ne',
      mul_zero, le_refl, and_self]
  · have hr : 0 < rho q := (rho_nonneg q).lt_of_ne' ((rho_eq_zero_iff q).not.mpr hq)
    let p := dilate (rho q)⁻¹ q
    have hp : p ∈ K := by
      change rho (dilate (rho q)⁻¹ q) = 1
      rw [rho_dilate _ (inv_pos.mpr hr), inv_mul_cancel₀ hr.ne']
    have hpH := scalarProfile_homogeneous gamma Lam (rho q)⁻¹ (inv_pos.mpr hr) q
    have hpR : Real.rpow (rho q) (3 * gamma.1) *
        Real.rpow (rho q)⁻¹ (3 * gamma.1) = 1 := by
      simp only [Real.rpow_eq_pow]
      rw [Real.inv_rpow hr.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos hr _).ne']
    have hH : scalarProfile gamma Lam q =
        Real.rpow (rho q) (3 * gamma.1) * scalarProfile gamma Lam p := by
      dsimp only [p]
      rw [hpH, ← mul_assoc, hpR, one_mul]
    obtain ⟨hlo, hhi⟩ := hbound p hp
    rw [hH]
    have hnonneg := (Real.rpow_pos_of_pos hr (3 * gamma.1)).le
    constructor
    · simpa only [mul_comm, Real.rpow_eq_pow] using mul_le_mul_of_nonneg_left hlo hnonneg
    · simpa only [mul_comm, Real.rpow_eq_pow] using mul_le_mul_of_nonneg_left hhi hnonneg

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
