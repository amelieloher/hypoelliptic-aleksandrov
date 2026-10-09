module

public import PDEFoundation.Sobolev.Cutoff.Profile
public import Mathlib.Analysis.Calculus.Deriv.Support

/-!
# Original-time smooth plateau cutoffs

This module constructs a smooth real-valued cutoff that equals one on a
prescribed closed time interval and has topological support strictly inside a
larger open time interval. It also supplies a nonnegative global bound for the
ordinary derivative.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Function Set

private def timePlateauLeftMidpoint (s₀ t₁ : ℝ) : ℝ :=
  (s₀ + t₁) / 2

private def timePlateauRightMidpoint (t₂ s₁ : ℝ) : ℝ :=
  (t₂ + s₁) / 2

private def timePlateauLeft (s₀ t₁ : ℝ) : ℝ → ℝ :=
  fun t => PDE.smoothTransitionProfile
    ((t - timePlateauLeftMidpoint s₀ t₁) /
      (t₁ - timePlateauLeftMidpoint s₀ t₁))

private def timePlateauRight (t₂ s₁ : ℝ) : ℝ → ℝ :=
  fun t => PDE.smoothTransitionProfile
    ((timePlateauRightMidpoint t₂ s₁ - t) /
      (timePlateauRightMidpoint t₂ s₁ - t₂))

private def timePlateau (s₀ t₁ t₂ s₁ : ℝ) : ℝ → ℝ :=
  fun t => timePlateauLeft s₀ t₁ t * timePlateauRight t₂ s₁ t

private theorem timePlateauLeft_contDiff (s₀ t₁ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (timePlateauLeft s₀ t₁) := by
  unfold timePlateauLeft
  exact PDE.smoothTransitionProfile.smooth.comp
    ((contDiff_id.sub contDiff_const).div_const _)

private theorem timePlateauRight_contDiff (t₂ s₁ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (timePlateauRight t₂ s₁) := by
  unfold timePlateauRight
  exact PDE.smoothTransitionProfile.smooth.comp
    ((contDiff_const.sub contDiff_id).div_const _)

private theorem timePlateau_contDiff (s₀ t₁ t₂ s₁ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (timePlateau s₀ t₁ t₂ s₁) := by
  unfold timePlateau
  exact (timePlateauLeft_contDiff s₀ t₁).mul
    (timePlateauRight_contDiff t₂ s₁)

private theorem timePlateau_nonneg (s₀ t₁ t₂ s₁ t : ℝ) :
    0 ≤ timePlateau s₀ t₁ t₂ s₁ t := by
  unfold timePlateau timePlateauLeft timePlateauRight
  exact mul_nonneg (PDE.smoothTransitionProfile.nonneg _)
    (PDE.smoothTransitionProfile.nonneg _)

private theorem timePlateau_le_one (s₀ t₁ t₂ s₁ t : ℝ) :
    timePlateau s₀ t₁ t₂ s₁ t ≤ 1 := by
  unfold timePlateau timePlateauLeft timePlateauRight
  exact mul_le_one₀ (PDE.smoothTransitionProfile.le_one _)
    (PDE.smoothTransitionProfile.nonneg _)
    (PDE.smoothTransitionProfile.le_one _)

private theorem timePlateauLeft_eq_one
    {s₀ t₁ t : ℝ} (hs₀t₁ : s₀ < t₁) (ht₁ : t₁ ≤ t) :
    timePlateauLeft s₀ t₁ t = 1 := by
  apply PDE.smoothTransitionProfile.one_of_one_le
  unfold timePlateauLeftMidpoint
  have hden : 0 < t₁ - (s₀ + t₁) / 2 := by
    linarith
  rw [le_div_iff₀ hden]
  linarith

private theorem timePlateauRight_eq_one
    {t₂ s₁ t : ℝ} (ht₂s₁ : t₂ < s₁) (htt₂ : t ≤ t₂) :
    timePlateauRight t₂ s₁ t = 1 := by
  apply PDE.smoothTransitionProfile.one_of_one_le
  unfold timePlateauRightMidpoint
  have hden : 0 < (t₂ + s₁) / 2 - t₂ := by
    linarith
  rw [le_div_iff₀ hden]
  linarith

private theorem timePlateau_eq_one_on
    {s₀ t₁ t₂ s₁ t : ℝ} (hs₀t₁ : s₀ < t₁)
    (ht₁t₂ : t₁ ≤ t₂) (ht₂s₁ : t₂ < s₁) (ht : t ∈ Icc t₁ t₂) :
    timePlateau s₀ t₁ t₂ s₁ t = 1 := by
  have hvalue : timePlateau s₀ t₁ t₂ s₁ t = 1 := by
    simp only [timePlateau, timePlateauLeft_eq_one hs₀t₁ ht.1,
      timePlateauRight_eq_one ht₂s₁ ht.2, one_mul]
  exact (show t₁ ≤ t₂ ∧ timePlateau s₀ t₁ t₂ s₁ t = 1 from ⟨ht₁t₂, hvalue⟩).2

private theorem timePlateauLeft_eq_zero_of_lt_midpoint
    {s₀ t₁ t : ℝ} (hs₀t₁ : s₀ < t₁)
    (ht : t < timePlateauLeftMidpoint s₀ t₁) :
    timePlateauLeft s₀ t₁ t = 0 := by
  apply PDE.smoothTransitionProfile.zero_of_nonpos
  unfold timePlateauLeftMidpoint
  unfold timePlateauLeftMidpoint at ht
  apply le_of_lt
  apply div_neg_of_neg_of_pos <;> linarith

private theorem timePlateauRight_eq_zero_of_midpoint_lt
    {t₂ s₁ t : ℝ} (ht₂s₁ : t₂ < s₁)
    (ht : timePlateauRightMidpoint t₂ s₁ < t) :
    timePlateauRight t₂ s₁ t = 0 := by
  apply PDE.smoothTransitionProfile.zero_of_nonpos
  unfold timePlateauRightMidpoint
  unfold timePlateauRightMidpoint at ht
  apply le_of_lt
  apply div_neg_of_neg_of_pos <;> linarith

private theorem timePlateau_support_subset
    {s₀ t₁ t₂ s₁ : ℝ} (hs₀t₁ : s₀ < t₁) (ht₂s₁ : t₂ < s₁) :
    support (timePlateau s₀ t₁ t₂ s₁) ⊆
      Icc (timePlateauLeftMidpoint s₀ t₁) (timePlateauRightMidpoint t₂ s₁) := by
  intro t hsupport
  change timePlateau s₀ t₁ t₂ s₁ t ≠ 0 at hsupport
  constructor
  · by_contra hnot
    have hlt : t < timePlateauLeftMidpoint s₀ t₁ := lt_of_not_ge hnot
    have hzero := timePlateauLeft_eq_zero_of_lt_midpoint hs₀t₁ hlt
    exact hsupport (by simp only [timePlateau, hzero, zero_mul])
  · by_contra hnot
    have hlt : timePlateauRightMidpoint t₂ s₁ < t := lt_of_not_ge hnot
    have hzero := timePlateauRight_eq_zero_of_midpoint_lt ht₂s₁ hlt
    exact hsupport (by simp only [timePlateau, hzero, mul_zero])

private theorem timePlateau_tsupport_subset
    {s₀ t₁ t₂ s₁ : ℝ} (hs₀t₁ : s₀ < t₁) (ht₂s₁ : t₂ < s₁) :
    tsupport (timePlateau s₀ t₁ t₂ s₁) ⊆
      Icc (timePlateauLeftMidpoint s₀ t₁) (timePlateauRightMidpoint t₂ s₁) := by
  rw [tsupport]
  exact closure_minimal (timePlateau_support_subset hs₀t₁ ht₂s₁) isClosed_Icc

private theorem timePlateau_hasCompactSupport
    {s₀ t₁ t₂ s₁ : ℝ} (hs₀t₁ : s₀ < t₁) (ht₂s₁ : t₂ < s₁) :
    HasCompactSupport (timePlateau s₀ t₁ t₂ s₁) := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  exact timePlateau_support_subset hs₀t₁ ht₂s₁

private theorem timePlateau_tsupport_subset_outer
    {s₀ t₁ t₂ s₁ : ℝ} (hs₀t₁ : s₀ < t₁) (ht₂s₁ : t₂ < s₁) :
    tsupport (timePlateau s₀ t₁ t₂ s₁) ⊆ Ioo s₀ s₁ := by
  refine (timePlateau_tsupport_subset hs₀t₁ ht₂s₁).trans ?_
  intro t ht
  constructor
  · have hmid : s₀ < timePlateauLeftMidpoint s₀ t₁ := by
      unfold timePlateauLeftMidpoint
      linarith
    exact hmid.trans_le ht.1
  · have hmid : timePlateauRightMidpoint t₂ s₁ < s₁ := by
      unfold timePlateauRightMidpoint
      linarith
    exact lt_of_le_of_lt ht.2 hmid

/-- A smooth original-time cutoff with a closed plateau, strictly interior
topological support, and a nonnegative global derivative bound. -/
theorem exists_smooth_timePlateau_with_deriv_bound
    (s₀ t₁ t₂ s₁ : ℝ)
    (hs₀t₁ : s₀ < t₁) (ht₁t₂ : t₁ ≤ t₂) (ht₂s₁ : t₂ < s₁) :
    ∃ (ζ : ℝ → ℝ) (Kζ : ℝ),
      ContDiff ℝ (⊤ : ℕ∞) ζ ∧
      HasCompactSupport ζ ∧
      0 ≤ Kζ ∧
      (∀ t, 0 ≤ ζ t) ∧
      (∀ t, ζ t ≤ 1) ∧
      (∀ t ∈ Set.Icc t₁ t₂, ζ t = 1) ∧
      tsupport ζ ⊆ Set.Ioo s₀ s₁ ∧
      ∀ t, |_root_.deriv ζ t| ≤ Kζ := by
  let ζ := timePlateau s₀ t₁ t₂ s₁
  have hζsmooth : ContDiff ℝ (⊤ : ℕ∞) ζ := timePlateau_contDiff s₀ t₁ t₂ s₁
  have hζcompact : HasCompactSupport ζ := timePlateau_hasCompactSupport hs₀t₁ ht₂s₁
  have hderivSmooth : ContDiff ℝ (⊤ : ℕ∞) (_root_.deriv ζ) :=
    (contDiff_infty_iff_deriv.mp hζsmooth).2
  have hderivCompact : HasCompactSupport (_root_.deriv ζ) := hζcompact.deriv
  obtain ⟨C, hC⟩ := hderivSmooth.continuous.bounded_above_of_compact_support hderivCompact
  refine ⟨ζ, max C 0, hζsmooth, hζcompact, le_max_right C 0, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    exact timePlateau_nonneg s₀ t₁ t₂ s₁ t
  · intro t
    exact timePlateau_le_one s₀ t₁ t₂ s₁ t
  · intro t ht
    exact timePlateau_eq_one_on hs₀t₁ ht₁t₂ ht₂s₁ ht
  · exact timePlateau_tsupport_subset_outer hs₀t₁ ht₂s₁
  · intro t
    simpa only [Real.norm_eq_abs] using! (hC t).trans (le_max_left C 0)

end HypoellipticAleksandrov.Parabolic
