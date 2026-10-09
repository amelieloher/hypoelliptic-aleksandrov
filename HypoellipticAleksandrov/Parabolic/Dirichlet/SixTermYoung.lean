module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# A six-term scalar Young estimate

This elementary real-algebra leaf is independent of the PDE application.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

private theorem young_eps
    (ε B g n : ℝ) (hε : 0 < ε) :
    B * g * n ≤ ε * g ^ 2 + (B ^ 2 / (4 * ε)) * n ^ 2 := by
  have hsq : 0 ≤ (2 * ε * g - B * n) ^ 2 := sq_nonneg _
  field_simp
  nlinarith

private theorem abs_six_terms_le (s a b c e f : ℝ) :
    |(-s) - a - b - c + e + f| ≤ |s| + |a| + |b| + |c| + |e| + |f| := by
  calc
    |(-s) - a - b - c + e + f| ≤ |(-s) - a - b - c + e| + |f| :=
      abs_add_le _ _
    _ ≤ (|(-s) - a - b - c| + |e|) + |f| := by
      gcongr
      exact abs_add_le _ _
    _ ≤ ((|(-s) - a - b| + |c|) + |e|) + |f| := by
      gcongr
      exact abs_sub _ _
    _ ≤ (((|(-s) - a| + |b|) + |c|) + |e|) + |f| := by
      gcongr
      exact abs_sub _ _
    _ ≤ ((((|-s| + |a|) + |b|) + |c|) + |e|) + |f| := by
      gcongr
      exact abs_sub _ _
    _ = |s| + |a| + |b| + |c| + |e| + |f| := by rw [abs_neg]

/-- A scalar six-term estimate with the two mixed terms absorbed by Young's
inequality. -/
theorem abs_six_terms_le_young
    (s a b c e f S A B g n ε : ℝ)
    (hs : |s| ≤ S + n ^ 2)
    (ha : |a| ≤ A * n ^ 2 + B * g * n)
    (hb : |b| ≤ A * n ^ 2 + B * g * n)
    (hc : |c| ≤ A * n ^ 2)
    (he : |e| ≤ A * n ^ 2)
    (hf : |f| ≤ A * n ^ 2)
    (hS : 0 ≤ S) (hA : 0 ≤ A)
    (hε : 0 < ε) :
    |(-s) - a - b - c + e + f| ≤
      ε * g ^ 2 + (1 + S + 5 * A + (2 * B) ^ 2 / (4 * ε)) * (1 + n ^ 2) := by
  have hy := young_eps ε (2 * B) g n hε
  have hQ : 0 ≤ (2 * B) ^ 2 / (4 * ε) := by positivity
  have hCoeff : 0 ≤ 1 + S + 5 * A + (2 * B) ^ 2 / (4 * ε) := by positivity
  calc
    _ ≤ |s| + |a| + |b| + |c| + |e| + |f| := abs_six_terms_le s a b c e f
    _ ≤ ε * g ^ 2 + (1 + S + 5 * A + (2 * B) ^ 2 / (4 * ε)) * (1 + n ^ 2) := by
      nlinarith [mul_nonneg hCoeff (sq_nonneg n)]

end HypoellipticAleksandrov.Parabolic.Dirichlet
