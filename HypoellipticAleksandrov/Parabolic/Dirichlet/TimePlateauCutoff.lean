module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeTests
public import PDEFoundation.Sobolev.Cutoff.Profile

/-!
# Reverse-time scalar plateau cutoffs

This module constructs a smooth reverse-time scalar test that is one on a
closed inner interval and has topological support strictly inside a prescribed
outer interval.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open Function Set

private def timePlateauEll (a b : ℝ) : ℝ :=
  (a + b) / 2

private def timePlateauR (c d : ℝ) : ℝ :=
  (c + d) / 2

private def timePlateauLeft (a b : ℝ) : ℝ → ℝ :=
  fun tau => PDE.smoothTransitionProfile
    ((tau - timePlateauEll a b) / (b - timePlateauEll a b))

private def timePlateauRight (c d : ℝ) : ℝ → ℝ :=
  fun tau => PDE.smoothTransitionProfile
    ((timePlateauR c d - tau) / (timePlateauR c d - c))

private def timePlateau (a b c d : ℝ) : ℝ → ℝ :=
  fun tau => timePlateauLeft a b tau * timePlateauRight c d tau

private theorem timePlateauLeft_contDiff (a b : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (timePlateauLeft a b) := by
  unfold timePlateauLeft
  exact PDE.smoothTransitionProfile.smooth.comp
    ((contDiff_id.sub contDiff_const).div_const _)

private theorem timePlateauRight_contDiff (c d : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (timePlateauRight c d) := by
  unfold timePlateauRight
  exact PDE.smoothTransitionProfile.smooth.comp
    ((contDiff_const.sub contDiff_id).div_const _)

private theorem timePlateau_contDiff (a b c d : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (timePlateau a b c d) := by
  unfold timePlateau
  exact
    (timePlateauLeft_contDiff a b).mul (timePlateauRight_contDiff c d)

private theorem timePlateau_nonneg (a b c d tau : ℝ) :
    0 ≤ timePlateau a b c d tau := by
  unfold timePlateau timePlateauLeft timePlateauRight
  exact mul_nonneg (PDE.smoothTransitionProfile.nonneg _)
    (PDE.smoothTransitionProfile.nonneg _)

private theorem timePlateau_le_one (a b c d tau : ℝ) :
    timePlateau a b c d tau ≤ 1 := by
  unfold timePlateau timePlateauLeft timePlateauRight
  exact mul_le_one₀ (PDE.smoothTransitionProfile.le_one _)
    (PDE.smoothTransitionProfile.nonneg _)
    (PDE.smoothTransitionProfile.le_one _)

private theorem timePlateauLeft_eq_one
    {a b tau : ℝ} (hab : a < b) (hbt : b ≤ tau) :
    timePlateauLeft a b tau = 1 := by
  apply PDE.smoothTransitionProfile.one_of_one_le
  unfold timePlateauEll
  have hden : 0 < b - (a + b) / 2 := by
    linarith
  rw [le_div_iff₀ hden]
  linarith

private theorem timePlateauRight_eq_one
    {c d tau : ℝ} (hcd : c < d) (htc : tau ≤ c) :
    timePlateauRight c d tau = 1 := by
  apply PDE.smoothTransitionProfile.one_of_one_le
  unfold timePlateauR
  have hden : 0 < (c + d) / 2 - c := by
    linarith
  rw [le_div_iff₀ hden]
  linarith

private theorem timePlateau_eq_one_on
    {a b c d tau : ℝ} (hab : a < b) (hbc : b ≤ c) (hcd : c < d)
    (htau : tau ∈ Icc b c) :
    timePlateau a b c d tau = 1 := by
  have hvalue : timePlateau a b c d tau = 1 := by
    simp only [timePlateau, timePlateauLeft_eq_one hab htau.1,
      timePlateauRight_eq_one hcd htau.2, one_mul]
  exact (show b ≤ c ∧ timePlateau a b c d tau = 1 from ⟨hbc, hvalue⟩).2

private theorem timePlateauLeft_eq_zero_of_lt_ell
    {a b tau : ℝ} (hab : a < b) (htau : tau < timePlateauEll a b) :
    timePlateauLeft a b tau = 0 := by
  apply PDE.smoothTransitionProfile.zero_of_nonpos
  unfold timePlateauEll
  unfold timePlateauEll at htau
  apply le_of_lt
  apply div_neg_of_neg_of_pos <;> linarith

private theorem timePlateauRight_eq_zero_of_r_lt
    {c d tau : ℝ} (hcd : c < d) (htau : timePlateauR c d < tau) :
    timePlateauRight c d tau = 0 := by
  apply PDE.smoothTransitionProfile.zero_of_nonpos
  unfold timePlateauR
  unfold timePlateauR at htau
  apply le_of_lt
  apply div_neg_of_neg_of_pos <;> linarith

private theorem timePlateau_support_subset
    {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    support (timePlateau a b c d) ⊆
      Icc (timePlateauEll a b) (timePlateauR c d) := by
  intro tau hsupport
  change timePlateau a b c d tau ≠ 0 at hsupport
  constructor
  · by_contra hnot
    have hlt : tau < timePlateauEll a b := lt_of_not_ge hnot
    have hzero := timePlateauLeft_eq_zero_of_lt_ell hab hlt
    exact hsupport (by simp only [timePlateau, hzero, zero_mul])
  · by_contra hnot
    have hlt : timePlateauR c d < tau := lt_of_not_ge hnot
    have hzero := timePlateauRight_eq_zero_of_r_lt hcd hlt
    exact hsupport (by simp only [timePlateau, hzero, mul_zero])

private theorem timePlateau_tsupport_subset
    {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    tsupport (timePlateau a b c d) ⊆
      Icc (timePlateauEll a b) (timePlateauR c d) := by
  rw [tsupport]
  exact closure_minimal (timePlateau_support_subset hab hcd) isClosed_Icc

private theorem timePlateau_hasCompactSupport
    {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    HasCompactSupport (timePlateau a b c d) := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  exact timePlateau_support_subset hab hcd

private theorem timePlateau_Icc_subset_outer
    {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    Icc (timePlateauEll a b) (timePlateauR c d) ⊆ Ioo a d := by
  intro tau htau
  constructor
  · have hell : a < timePlateauEll a b := by
      unfold timePlateauEll
      linarith
    exact hell.trans_le htau.1
  · have hr : timePlateauR c d < d := by
      unfold timePlateauR
      linarith
    exact lt_of_le_of_lt htau.2 hr

private theorem timePlateau_outer_subset_reverseTime
    {T a d : ℝ} (ha0 : 0 ≤ a) (hdT : d ≤ T) :
    Ioo a d ⊆ reverseTimeOpenInterval T := by
  intro tau htau
  change tau ∈ Ioo 0 T
  exact ⟨lt_of_le_of_lt ha0 htau.1, lt_of_lt_of_le htau.2 hdT⟩

/-- A smooth reverse-time test with values in `[0, 1]`, a closed inner
plateau, and topological support strictly inside the prescribed outer interval. -/
theorem exists_reverseTimeScalarTest_plateau
    (T a b c d : ℝ)
    (ha0 : 0 ≤ a) (hab : a < b) (hbc : b ≤ c)
    (hcd : c < d) (hdT : d ≤ T) :
    ∃ eta : ReverseTimeScalarTest T,
      (∀ tau : ℝ, 0 ≤ eta tau) ∧
      (∀ tau : ℝ, eta tau ≤ 1) ∧
      (∀ tau ∈ Set.Icc b c, eta tau = 1) ∧
      tsupport (eta : ℝ → ℝ) ⊆ Set.Ioo a d := by
  let eta : ReverseTimeScalarTest T :=
    { toFun := timePlateau a b c d
      contDiff' := timePlateau_contDiff a b c d
      hasCompactSupport' := timePlateau_hasCompactSupport hab hcd
      tsupport_subset' := (timePlateau_tsupport_subset hab hcd).trans
        ((timePlateau_Icc_subset_outer hab hcd).trans
          (timePlateau_outer_subset_reverseTime ha0 hdT)) }
  refine ⟨eta, ?_, ?_, ?_, ?_⟩
  · intro tau
    change 0 ≤ timePlateau a b c d tau
    exact timePlateau_nonneg a b c d tau
  · intro tau
    change timePlateau a b c d tau ≤ 1
    exact timePlateau_le_one a b c d tau
  · intro tau htau
    change timePlateau a b c d tau = 1
    exact timePlateau_eq_one_on hab hbc hcd htau
  · change tsupport (timePlateau a b c d) ⊆ Ioo a d
    exact (timePlateau_tsupport_subset hab hcd).trans
      (timePlateau_Icc_subset_outer hab hcd)

end HypoellipticAleksandrov.Parabolic.Dirichlet
