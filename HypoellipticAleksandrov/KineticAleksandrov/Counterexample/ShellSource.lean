module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningSource
import Mathlib.Tactic.Linarith

/-! # Uniform stationary source amplitude on the shrinking shell -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open MeasureTheory Set
open scoped MatrixOrder

/-- The upper profile comparison traps the shell away from the origin at scale r. -/
theorem velocity_gradient_on_shell {d : ℕ} (H : XV d → ℝ) (gv : XV d → PDE.Vec d)
    (alpha C : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1) (hC : 0 < C)
    (hzero : H 0 = 0)
    (hcomp : ∀ q, H q ≤ C * Real.rpow (rho q) alpha)
    (hgrad : ∀ q : XV d, q ≠ 0 →
      PDE.vecEuclideanNorm (gv q) ≤ C * Real.rpow (rho q) (alpha - 1)) :
    ∃ K : ℝ, 0 < K ∧ ∀ r : ℝ, 0 < r → ∀ q ∈ profileShell H alpha r,
      PDE.vecEuclideanNorm (gv q) ≤ K * Real.rpow r (alpha - 1) := by
  let B : ℝ := Real.rpow C alpha⁻¹
  have hB : 0 < B := Real.rpow_pos_of_pos hC _
  have hBa : B ^ alpha = C := Real.rpow_inv_rpow hC.le ha.ne'
  let K : ℝ := C / B ^ (alpha - 1)
  have hK : 0 < K := div_pos hC (Real.rpow_pos_of_pos hB _)
  refine ⟨K, hK, ?_⟩
  intro r hr q hq
  have hlo := hq.1
  have hn : q ≠ 0 := by
    intro he
    rw [he, hzero] at hlo
    exact (not_le_of_gt (Real.rpow_pos_of_pos hr alpha)) hlo
  have hb : r ≤ B * rho q := by
    apply (Real.rpow_le_rpow_iff hr.le (mul_nonneg hB.le (rho_nonneg q)) ha).mp
    rw [Real.mul_rpow hB.le (rho_nonneg q), hBa]
    exact hlo.trans (hcomp q)
  have hlower : r / B ≤ rho q := (div_le_iff₀ hB).2 (by simpa only [mul_comm] using hb)
  have hnegative : alpha - 1 ≤ 0 := sub_nonpos.mpr ha1.le
  have hp := Real.rpow_le_rpow_of_nonpos (div_pos hr hB) hlower hnegative
  have ht := (hgrad q hn).trans (mul_le_mul_of_nonneg_left hp hC.le)
  simp only [Real.rpow_eq_pow] at ht ⊢
  rw [Real.div_rpow hr.le hB.le] at ht
  simpa only [K, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using ht

/-- The exact powers in the source amplitude combine to alpha minus two. -/
theorem source_rpow_identity (alpha r : ℝ) (hr : 0 < r) :
    Real.rpow r (-alpha) * (Real.rpow r (alpha - 1)) ^ (2 : ℕ) =
      Real.rpow r (alpha - 2) := by
  simp only [Real.rpow_eq_pow]
  rw [← Real.rpow_mul_natCast hr.le, ← Real.rpow_add hr]
  congr 1
  ring

/-- Ellipticity, the cutoff, and the velocity estimate give the source's uniform amplitude. -/
theorem shell_source_bound {d : ℕ} (A : XV d → PDE.Mat d) (H : XV d → ℝ)
    (gv : XV d → PDE.Vec d) (alpha lam Lam C : ℝ)
    (ha : 0 < alpha) (ha1 : alpha < 1) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hA : ∀ q, lam • (1 : PDE.Mat d) ≤ A q ∧ A q ≤ Lam • (1 : PDE.Mat d))
    (hC : 0 < C) (hzero : H 0 = 0)
    (hcomp : ∀ q, H q ≤ C * Real.rpow (rho q) alpha)
    (hgrad : ∀ q : XV d, q ≠ 0 →
      PDE.vecEuclideanNorm (gv q) ≤ C * Real.rpow (rho q) (alpha - 1)) :
    ∃ K : ℝ, 0 < K ∧ ∀ r : ℝ, 0 < r → ∀ q,
      0 ≤ flatSourceWithJet A H gv alpha r q ∧
      flatSourceWithJet A H gv alpha r q ≤ K * Real.rpow r (alpha - 2) := by
  obtain ⟨G, hG, hgradShell⟩ := velocity_gradient_on_shell H gv alpha C ha ha1 hC
    hzero hcomp hgrad
  obtain ⟨D, hD, hsecond⟩ := flatteningPsi_deriv2_bound
  have hLam : 0 < Lam := hlam.trans_le hlamLam
  refine ⟨D * Lam * G ^ 2, by positivity, ?_⟩
  intro r hr q
  by_cases hq : q ∈ profileShell H alpha r
  · have hquad0 := quadratic_nonneg_of_loewner lam hlam.le (A q) (hA q).1 (gv q)
    have hquad1 := quadratic_upper_of_loewner Lam (A q) (hA q).2 (gv q)
    have hnorm := hgradShell r hr q hq
    have hnormSq : PDE.vecNormSq (gv q) ≤ (G * Real.rpow r (alpha - 1)) ^ 2 := by
      rw [← PDE.vecEuclideanNorm_sq]
      exact pow_le_pow_left₀ (PDE.vecEuclideanNorm_nonneg _) hnorm _
    have hsecond0 := flatteningPsi_deriv2_nonneg (H q / Real.rpow r alpha)
    have hsecond1 := hsecond (H q / Real.rpow r alpha)
    unfold flatSourceWithJet
    constructor
    · exact mul_nonneg (mul_nonneg (Real.rpow_pos_of_pos hr _).le hsecond0) hquad0
    · calc
        _ ≤ Real.rpow r (-alpha) * D * (Lam * (G * Real.rpow r (alpha - 1)) ^ 2) :=
          mul_le_mul
            (mul_le_mul_of_nonneg_left hsecond1 (Real.rpow_pos_of_pos hr _).le)
            (hquad1.trans (mul_le_mul_of_nonneg_left hnormSq hLam.le))
            hquad0 (mul_nonneg (Real.rpow_pos_of_pos hr _).le hD.le)
        _ = D * Lam * G ^ 2 *
            (Real.rpow r (-alpha) * (Real.rpow r (alpha - 1)) ^ 2) := by ring
        _ = _ := by rw [source_rpow_identity alpha r hr]
  · rw [flatSourceWithJet_eq_zero_off_shell A H gv alpha r hr q hq]
    exact ⟨le_rfl, mul_nonneg
      (mul_nonneg (mul_nonneg hD.le hLam.le) (sq_nonneg G))
      (Real.rpow_pos_of_pos hr _).le⟩

/-- The literal selected source is nonnegative, shell-supported, and uniformly bounded. -/
theorem shell_source_bound_of_profile {d : ℕ} {alpha : ℝ}
    (ha : 0 < alpha) (ha1 : alpha < 1) (h : CounterProfileStatement d alpha) :
    ∃ K : ℝ, 0 < K ∧ ∀ r : ℝ, 0 < r → ∀ᵐ q ∂volume,
      0 ≤ flatSource (profileMatrix h) (profileFunction h) flatteningPsi alpha r q ∧
      flatSource (profileMatrix h) (profileFunction h) flatteningPsi alpha r q ≤
        K * Real.rpow r (alpha - 2) ∧
      (q ∉ profileShell (profileFunction h) alpha r →
        flatSource (profileMatrix h) (profileFunction h) flatteningPsi alpha r q = 0) := by
  obtain ⟨hlam, hlamLam, hc, hC, hAm, hA, hH, hzero, hhom, hcomp,
    _, hgv, _, _, _, hgrad, _⟩ := selectedProfile_spec h
  obtain ⟨K, hK, hb⟩ := shell_source_bound (profileMatrix h) (profileFunction h)
    (profileVelocityJet h) alpha (profileLowerEllipticity h) (profileUpperEllipticity h)
    (profileUpperComparison h) ha ha1 hlam hlamLam hA hC hzero
    (fun q => (hcomp q).2) hgrad
  refine ⟨K, hK, ?_⟩
  intro r hr
  filter_upwards [flatSource_ae_eq_jet_of_profile h r] with q hq
  rw [hq]
  exact ⟨(hb r hr q).1, (hb r hr q).2,
    fun hn => flatSourceWithJet_eq_zero_off_shell _ _ _ alpha r hr q hn⟩

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
