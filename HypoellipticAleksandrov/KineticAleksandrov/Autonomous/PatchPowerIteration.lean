module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PatchPowerDoubling
import Mathlib.Tactic

/-! # Finite doubling iteration for a positive return patch -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Parabolic Set

/-- The radius after `n` doublings. -/
def returnExpandedRadius (ell : ℝ) (n : ℕ) : ℝ := (2 : ℝ) ^ n * ell

/-- The transported centre after `n` doublings, with the geometric time sum evaluated. -/
def returnExpandedCenter (z : Point) (ell : ℝ) (n : ℕ) : Point :=
  let dt := (8 / 3 : ℝ) * ((returnExpandedRadius ell n) ^ 2 - ell ^ 2)
  ⟨z.time + dt, z.position + dt • z.velocity, z.velocity⟩

/-- Radius doubling is multiplication by two. -/
theorem returnExpandedRadius_succ (ell : ℝ) (n : ℕ) :
    returnExpandedRadius ell (n + 1) = 2 * returnExpandedRadius ell n := by
  simp only [returnExpandedRadius, pow_succ]
  ring

/-- The explicit geometric sum agrees with the one-step transported centre. -/
theorem returnExpandedCenter_succ (z : Point) (ell : ℝ) (n : ℕ) :
    returnExpandedCenter z ell (n + 1) =
      returnDoubleCenter (returnExpandedCenter z ell n) (returnExpandedRadius ell n) := by
  rw [returnExpandedCenter, returnExpandedRadius_succ]
  ext i <;> simp only [returnExpandedCenter, returnDoubleCenter,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;> ring

/-- The expanded radius never decreases. -/
theorem returnExpandedRadius_mono {ell : ℝ} (hell : 0 ≤ ell) {m n : ℕ} (hmn : m ≤ n) :
    returnExpandedRadius ell m ≤ returnExpandedRadius ell n := by
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hmn) hell

/-- All intermediate centres stay later than the initial centre. -/
theorem returnExpandedCenter_time_ge (z : Point) {ell : ℝ} (hell : 0 ≤ ell) (n : ℕ) :
    z.time ≤ (returnExpandedCenter z ell n).time := by
  have h := returnExpandedRadius_mono hell (Nat.zero_le n)
  rw [show returnExpandedRadius ell 0 = ell by simp [returnExpandedRadius]] at h
  have hsq := pow_le_pow_left₀ hell h 2
  dsimp only [returnExpandedCenter]
  linarith

/-- The same coefficient-independent loss can be iterated as long as the radius stays small. -/
theorem return_patch_doublings (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hp6 : SmoothAutonomousP6Statement lam Lam) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ (A : SmoothAutonomous lam Lam) (u : Point → ℝ),
      IsNonnegativeHomogeneousSolution A u → ∀ (z : Point) (ell k : ℝ) (N : ℕ),
      0 < ell → 1 / 2 ≤ z.time → returnExpandedRadius ell N ≤ 1 / 64 → 0 ≤ k →
      (∀ p ∈ backwardCylinder z ell, k ≤ u p) →
      ∀ p ∈ backwardCylinder (returnExpandedCenter z ell N) (returnExpandedRadius ell N),
        c ^ N * k ≤ u p := by
  obtain ⟨c, hc, hc1, hd⟩ := return_patch_double lam Lam hlam hLam hp6
  refine ⟨c, hc, hc1, ?_⟩
  intro A u hu z ell k N hell hzt hrad hk hpatch
  have hrpos (n : ℕ) : 0 < returnExpandedRadius ell n := by
    dsimp only [returnExpandedRadius]
    positivity
  have hi : ∀ n, n ≤ N →
      ∀ p ∈ backwardCylinder (returnExpandedCenter z ell n) (returnExpandedRadius ell n),
        c ^ n * k ≤ u p := by
    intro n
    induction n with
    | zero =>
      intro _ p hp
      simpa only [returnExpandedCenter, returnExpandedRadius, pow_zero, one_mul,
        sub_self, mul_zero, add_zero, zero_smul] using hpatch p (by simpa only
          [returnExpandedCenter, returnExpandedRadius, pow_zero, one_mul, sub_self,
            mul_zero, add_zero, zero_smul] using hp)
    | succ n ih =>
      intro hn p hp
      have hnN : n ≤ N := by omega
      have hsmall : returnExpandedRadius ell n ≤ 1 / 64 :=
        (returnExpandedRadius_mono hell.le hnN).trans hrad
      have ht := returnExpandedCenter_time_ge z hell.le n
      have htime : 12 * (returnExpandedRadius ell n) ^ 2 <
          (returnExpandedCenter z ell n).time := by
        have hnn := (hrpos n).le
        nlinarith
      rw [returnExpandedCenter_succ, returnExpandedRadius_succ] at hp
      have h := hd A u hu (returnExpandedCenter z ell n) (returnExpandedRadius ell n)
        (c ^ n * k) (hrpos n) htime (mul_nonneg (pow_nonneg hc.le n) hk)
        (ih hnN) p hp
      simpa only [pow_succ', mul_assoc] using h
  exact hi N le_rfl

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
