module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ExtensionGeometry

/-! # The initial zero region of the literal cutoff -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/-- Nonpositive times give zero wherever the barrier velocity radius is respected. -/
theorem timeCutoffProfile_eq_zero_of_nonpos_time {d : ℕ} (H : XV d → ℝ)
    (alpha r mu R : ℝ) (hr : 0 < r) (hmu : 0 < mu) (hR : 0 < R)
    (P : KineticPoint d) (ht : P.time ≤ 0) (hv : PDE.vecNormSq P.velocity < R ^ 2) :
    timeCutoffProfile H alpha r mu R P = 0 := by
  have hs : 0 < R ^ 2 := sq_pos_of_pos hR
  have hb : 1 < 2 - PDE.vecNormSq P.velocity / R ^ 2 := by
    have he := (div_lt_one hs).mpr hv
    linarith
  have hexp : 1 ≤ Real.exp (-mu * P.time) :=
    Real.one_le_exp_iff.mpr (mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hmu.le) ht)
  have hbar : 1 ≤ barrier mu R P := by
    unfold barrier
    exact hexp.trans (le_mul_of_one_le_right (Real.exp_pos _).le hb.le)
  unfold timeCutoffProfile
  apply timeCutoffTheta_eq_zero
  exact sub_nonpos.mpr ((flatProfile_le_one H alpha r hr _).trans hbar)

/-- On the profile domain the negative-time splice equals the raw cutoff at every time. -/
theorem zeroExtendedProfile_eq_raw_on_profile {d : ℕ} (H : XV d → ℝ)
    (alpha r mu R : ℝ) (hr : 0 < r) (hmu : 0 < mu) (hR : 0 < R)
    (hvel : ∀ q, H q ≤ 1 → PDE.vecNormSq q.2 < R ^ 2)
    (P : KineticPoint d) (hq : H (P.position, P.velocity) < 1) :
    zeroExtendedProfile H alpha r mu R P = timeCutoffProfile H alpha r mu R P := by
  by_cases ht : 0 < P.time
  · simp only [zeroExtendedProfile, ht, hq, and_self, ite_true]
  · rw [zeroExtendedProfile_eq_zero_of_time H alpha r mu R P (not_lt.mp ht)]
    exact (timeCutoffProfile_eq_zero_of_nonpos_time H alpha r mu R hr hmu hR P
      (not_lt.mp ht) (hvel _ hq.le)).symm

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
