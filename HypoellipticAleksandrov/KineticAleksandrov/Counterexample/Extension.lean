module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.TimeCutoff
import Mathlib.Tactic.Linarith

/-!
# Zero extension and the fixed spatial collar

The collar threshold is independent of the flattening scale. Derivative gluing is a
separate step from these pointwise identities.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open Set

/-- Extension by zero outside the positive-time profile domain. -/
def zeroExtendedProfile {d : ℕ} (H : XV d → ℝ) (alpha r mu R : ℝ)
    (P : KineticPoint d) : ℝ :=
  if 0 < P.time ∧ H (P.position, P.velocity) < 1 then
    timeCutoffProfile H alpha r mu R P else 0

/-- The extension is globally nonnegative. -/
theorem zeroExtendedProfile_nonneg {d : ℕ} (H : XV d → ℝ) (alpha r mu R : ℝ)
    (P : KineticPoint d) : 0 ≤ zeroExtendedProfile H alpha r mu R P := by
  unfold zeroExtendedProfile
  split
  · exact timeCutoffProfile_nonneg H alpha r mu R P
  · exact le_refl 0

/-- The extension vanishes at every nonpositive time. -/
theorem zeroExtendedProfile_eq_zero_of_time {d : ℕ} (H : XV d → ℝ)
    (alpha r mu R : ℝ) (P : KineticPoint d) (ht : P.time ≤ 0) :
    zeroExtendedProfile H alpha r mu R P = 0 := by
  simp only [zeroExtendedProfile, not_lt.mpr ht, false_and, ite_false]

/-- The extension vanishes everywhere outside the profile domain. -/
theorem zeroExtendedProfile_eq_zero_of_profile {d : ℕ} (H : XV d → ℝ)
    (alpha r mu R : ℝ) (P : KineticPoint d) (hH : 1 ≤ H (P.position, P.velocity)) :
    zeroExtendedProfile H alpha r mu R P = 0 := by
  simp only [zeroExtendedProfile, not_lt.mpr hH, and_false, ite_false]

/-- The flattened profile never exceeds one, independently of the profile value. -/
theorem flatProfile_le_one {d : ℕ} (H : XV d → ℝ) (alpha r : ℝ) (hr : 0 < r)
    (q : XV d) : flatProfile H flatteningPsi flatteningOffset alpha r q ≤ 1 := by
  have hpow := (Real.rpow_pos_of_pos hr alpha).le
  have hc : 0 ≤ flatteningOffset := (by linarith [flatteningOffset_bounds.1])
  have h1 := mul_nonneg hc hpow
  have h2 := mul_nonneg hpow (flatteningPsi_nonneg (H q / Real.rpow r alpha))
  unfold flatProfile
  simp only [Real.rpow_eq_pow] at *
  linarith

/-- The positive barrier creates the source's fixed spatial zero collar. -/
theorem zero_extension_collar {d : ℕ} (H : XV d → ℝ) (alpha r mu R : ℝ)
    (hr : 0 < r) (hmu : 0 < mu) (hR : 0 < R)
    (hscale : 2 * Real.rpow r alpha ≤ 7 / 8) (P : KineticPoint d)
    (ht : P.time ∈ Icc 0 (barrierTime mu))
    (hv : PDE.vecNormSq P.velocity < R ^ 2)
    (hH : 7 / 8 ≤ H (P.position, P.velocity)) :
    zeroExtendedProfile H alpha r mu R P = 0 := by
  have hb := (barrier_endpoint_bounds mu R hmu hR P.position P.velocity hv).2.2
    P.time ht
  have hf := flatProfile_eq_one_sub H alpha r hr (P.position, P.velocity)
    (hscale.trans hH)
  unfold zeroExtendedProfile
  split
  · unfold timeCutoffProfile
    rw [hf]
    apply timeCutoffTheta_eq_zero
    linarith
  · rfl

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
