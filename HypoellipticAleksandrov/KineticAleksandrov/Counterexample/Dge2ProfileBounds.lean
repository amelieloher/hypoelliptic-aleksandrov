module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2ProfileConstruction
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2SpectralCompact
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ShellGeometry

/-! # Compact gauge-shell comparison for the actual homogeneous profile -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/-- The unit kinetic gauge shell is compact in native coordinates. -/
theorem isCompact_unitGaugeShell (d : ℕ) : IsCompact {q : XV d | rho q = 1} :=
  (isCompact_rho_sublevel d 1).of_isClosed_subset
    (isClosed_eq (continuous_rho d) continuous_const) (fun _ h => le_of_eq h)

/-- Positive-degree homogeneity transports shell bounds to every nonzero kinetic point. -/
theorem homogeneous_profile_comparison {d : ℕ} (alpha : ℝ) (ha : 0 < alpha)
    (H : XV d → ℝ) (hzero : H 0 = 0)
    (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ))
    (hpos : ∀ q, q ≠ 0 → 0 < H q)
    (hhom : ∀ r : ℝ, 0 < r → ∀ q, H (dilate r q) = Real.rpow r alpha * H q) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ q,
      c * Real.rpow (rho q) alpha ≤ H q ∧ H q ≤ C * Real.rpow (rho q) alpha := by
  let K : Set (XV d) := {q | rho q = 1}
  have hKnz : ∀ q ∈ K, q ≠ 0 := by
    intro q hq hzeroq
    have hh : rho q = 1 := hq
    simp [hzeroq] at hh
  have hcont : ContinuousOn H K := hsmooth.continuousOn.mono (fun q hq => hKnz q hq)
  obtain ⟨c, C, hc, hcC, hbound⟩ := exists_positive_bounds_on_compact K
    (isCompact_unitGaugeShell d) H hcont (fun q hq => hpos q (hKnz q hq))
  refine ⟨c, C, hc, hcC, ?_⟩
  intro q
  by_cases hq : q = 0
  · subst q
    simp only [rho_zero, hzero, Real.rpow_eq_pow, Real.zero_rpow ha.ne', mul_zero, le_refl,
      and_self]
  · have hr : 0 < rho q := (rho_nonneg q).lt_of_ne' ((rho_eq_zero_iff q).not.mpr hq)
    let p := dilate (rho q)⁻¹ q
    have hp : p ∈ K := by
      change rho (dilate (rho q)⁻¹ q) = 1
      rw [rho_dilate _ (inv_pos.mpr hr), inv_mul_cancel₀ hr.ne']
    have hpH := hhom (rho q)⁻¹ (inv_pos.mpr hr) q
    have hpR : Real.rpow (rho q) alpha * Real.rpow (rho q)⁻¹ alpha = 1 := by
      simp only [Real.rpow_eq_pow]
      rw [Real.inv_rpow hr.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos hr alpha).ne']
    have hH : H q = Real.rpow (rho q) alpha * H p := by
      dsimp [p]
      rw [hpH]
      simp only [Real.rpow_eq_pow] at hpR ⊢
      rw [← mul_assoc, hpR, one_mul]
    obtain ⟨hlo, hhi⟩ := hbound p hp
    rw [hH]
    have hnonneg := (Real.rpow_pos_of_pos hr alpha).le
    constructor
    · simpa only [mul_comm, Real.rpow_eq_pow] using mul_le_mul_of_nonneg_left hlo hnonneg
    · simpa only [mul_comm, Real.rpow_eq_pow] using mul_le_mul_of_nonneg_left hhi hnonneg

/-- The actual profile is quantitatively comparable with the source kinetic gauge power. -/
theorem geometricProfile_comparison {d : ℕ} (alpha C₀ sigma R : ℝ) (ha : 0 < alpha)
    (hC₀ : 0 ≤ C₀) (hsigma : 0 < sigma) (hR : 0 < R) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ q : XV d,
      c * Real.rpow (rho q) alpha ≤ geometricProfile alpha C₀ sigma R q ∧
      geometricProfile alpha C₀ sigma R q ≤ C * Real.rpow (rho q) alpha := by
  apply homogeneous_profile_comparison alpha ha (geometricProfile alpha C₀ sigma R)
    (geometricProfile_zero d alpha C₀ sigma R ha)
    (geometricProfile_smooth_off_origin alpha C₀ sigma R hsigma hR)
    (geometricProfile_pos alpha C₀ sigma R hC₀ hsigma hR)
  exact fun r hr q => geometricProfile_homogeneous alpha C₀ sigma R r hr q

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
