module

public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# The time mollifier of the smoothed equation

The smoothed Green measure: a standard mollifier `η_δ` on `ℝ` supported in `(-δ, δ)`.  The predicate
`IsMollifier δ η` records smoothness, nonnegativity, the support condition and unit mass; the
consequences used below (integrability, bounds of `η` and `η'`) are derived from it.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

open MeasureTheory

/-- `η` is a standard mollifier on `ℝ` supported in `(-δ, δ)`. -/
structure IsMollifier (δ : ℝ) (η : ℝ → ℝ) : Prop where
  /-- Smoothness. -/
  contDiff : ContDiff ℝ (⊤ : ℕ∞) η
  /-- Nonnegativity. -/
  nonneg : ∀ t, 0 ≤ η t
  /-- Vanishing outside `(-δ, δ)`. -/
  support : ∀ t, δ ≤ |t| → η t = 0
  /-- Unit mass. -/
  integral_eq_one : ∫ t, η t = 1

namespace IsMollifier

variable {δ : ℝ} {η : ℝ → ℝ}

theorem hasCompactSupport (hη : IsMollifier δ η) : HasCompactSupport η := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -δ) (b := δ)) ?_
  intro t ht
  by_contra hnot
  have h1 : δ ≤ |t| := by
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hnot
    rcases hnot with h | h
    · exact (by linarith : δ ≤ -t).trans (neg_le_abs t)
    · exact (by linarith : δ ≤ t).trans (le_abs_self t)
  exact ht (hη.support t h1)

theorem continuous (hη : IsMollifier δ η) : Continuous η := hη.contDiff.continuous

theorem integrable (hη : IsMollifier δ η) : Integrable η := by
  exact hη.continuous.integrable_of_hasCompactSupport hη.hasCompactSupport

/-- `η` is bounded. -/
theorem exists_bound (hη : IsMollifier δ η) : ∃ C : ℝ, ∀ t, |η t| ≤ C := by
  obtain ⟨C, hC⟩ := hη.continuous.bounded_above_of_compact_support hη.hasCompactSupport
  exact ⟨C, fun t => by simpa [Real.norm_eq_abs] using hC t⟩

theorem contDiff_deriv (hη : IsMollifier δ η) : ContDiff ℝ (⊤ : ℕ∞) (deriv η) :=
  (contDiff_infty_iff_deriv.1 hη.contDiff).2

theorem hasCompactSupport_deriv (hη : IsMollifier δ η) : HasCompactSupport (deriv η) :=
  HasCompactSupport.deriv hη.hasCompactSupport

/-- `η'` is bounded. -/
theorem exists_bound_deriv (hη : IsMollifier δ η) : ∃ C : ℝ, ∀ t, |deriv η t| ≤ C := by
  obtain ⟨C, hC⟩ := hη.contDiff_deriv.continuous.bounded_above_of_compact_support
    hη.hasCompactSupport_deriv
  exact ⟨C, fun t => by simpa [Real.norm_eq_abs] using hC t⟩

theorem hasDerivAt (hη : IsMollifier δ η) (t : ℝ) : HasDerivAt η (deriv η t) t :=
  ((hη.contDiff.differentiable (by simp)) t).hasDerivAt

end IsMollifier

/-- Standard mollifiers exist for every `δ > 0`. -/
theorem exists_isMollifier {δ : ℝ} (hδ : 0 < δ) : ∃ η : ℝ → ℝ, IsMollifier δ η := by
  let f : ContDiffBump (0 : ℝ) := ⟨δ / 2, δ, by linarith, by linarith⟩
  refine ⟨f.normed volume, ⟨f.contDiff_normed, f.nonneg_normed, fun t ht => ?_,
    f.integral_normed⟩⟩
  by_contra hne
  have : t ∈ Function.support (f.normed volume) := hne
  rw [f.support_normed_eq] at this
  simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at this
  exact absurd ht (not_le.2 this)

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
