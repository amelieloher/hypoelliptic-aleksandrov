module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Elementary real inequalities for the `W^{2,1}` membership of `r^q` and `r^q |β|²`

Pointwise bounds of the first and second coordinate derivatives of `u^s` and `u^s J²` by the
integrands of the integrability list of the smoothing estimates, stated for real numbers
standing for `u`, the partials of `u` and `J`, and the integrands.
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

theorem abs_mul_le_of_sq_le {a b GS : ℝ} (ha : a ^ 2 ≤ GS) (hb : b ^ 2 ≤ GS) :
    |a| * |b| ≤ GS := by
  nlinarith [sq_abs a, sq_abs b, sq_nonneg (|a| - |b|), abs_nonneg a, abs_nonneg b]

theorem two_mul_abs_mul_le {a b GS FS : ℝ} (ha : a ^ 2 ≤ GS) (hb : b ^ 2 ≤ FS) :
    2 * (|a| * |b|) ≤ GS + FS := by
  nlinarith [sq_abs a, sq_abs b, sq_nonneg (|a| - |b|), abs_nonneg a, abs_nonneg b]

/-- Second derivative of `u^s`, with `P2 = u^{s-2}`, `P1 = u^{s-1}`. -/
theorem second_bound_rpow {P1 P2 a a' a'' s GS HS : ℝ} (hP1 : 0 ≤ P1) (hP2 : 0 ≤ P2)
    (ha : a ^ 2 ≤ GS) (ha' : a' ^ 2 ≤ GS) (ha'' : |a''| ≤ HS) :
    |s * (s - 1) * P2 * a' * a + s * P1 * a''| ≤
      |s * (s - 1)| * (P2 * GS) + |s| * (P1 * HS) := by
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · have : |s * (s - 1) * P2 * a' * a| = |s * (s - 1)| * P2 * (|a'| * |a|) := by
      simp only [abs_mul, abs_of_nonneg hP2]; ring
    rw [this]
    have h2 := abs_mul_le_of_sq_le ha' ha
    calc |s * (s - 1)| * P2 * (|a'| * |a|) ≤ |s * (s - 1)| * P2 * GS := by gcongr
      _ = _ := by ring
  · have : |s * P1 * a''| = |s| * P1 * |a''| := by
      simp only [abs_mul, abs_of_nonneg hP1]
    rw [this]
    calc |s| * P1 * |a''| ≤ |s| * P1 * HS := by gcongr
      _ = _ := by ring

/-- First and zeroth derivative bounds for `u^s J²`. -/
theorem first_bound_G {Q Q1 U a J b s Lam HA HB : ℝ} (hU : 0 < U) (hQ1 : 0 ≤ Q1) (hQ : 0 ≤ Q)
    (hQU : Q = U * Q1) (hJ : |J| ≤ Lam * U) (hLam : 0 ≤ Lam) (ha : |a| ≤ HA) (hb : |b| ≤ HB) :
    |s * Q1 * a * J ^ 2 + Q * (2 * J * b)| ≤
      |s| * Lam ^ 2 * (Q * U * HA) + 2 * Lam * (Q * U * HB) := by
  have hJ2 : J ^ 2 ≤ (Lam * U) ^ 2 := by
    rw [← sq_abs J]; exact pow_le_pow_left₀ (abs_nonneg _) hJ 2
  have hHA : 0 ≤ HA := (abs_nonneg _).trans ha
  have hHB : 0 ≤ HB := (abs_nonneg _).trans hb
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · have : |s * Q1 * a * J ^ 2| = |s| * Q1 * |a| * J ^ 2 := by
      simp only [abs_mul, abs_of_nonneg hQ1, abs_pow, sq_abs]
    rw [this]
    calc |s| * Q1 * |a| * J ^ 2 ≤ |s| * Q1 * HA * (Lam * U) ^ 2 := by gcongr
      _ = |s| * Lam ^ 2 * (Q * U * HA) := by rw [hQU]; try ring
  · have : |Q * (2 * J * b)| = Q * (2 * |J| * |b|) := by
      simp only [abs_mul, abs_of_nonneg hQ, abs_two]; try ring
    rw [this]
    calc Q * (2 * |J| * |b|) ≤ Q * (2 * (Lam * U) * HB) := by gcongr
      _ = 2 * Lam * (Q * U * HB) := by ring

/-- Second derivative bound for `u^s J²`; `Q = u^s`, `Q1 = u^{s-1}`, `Q2 = u^{s-2}`. -/
theorem second_bound_G {Q Q1 Q2 U a a' a'' J b b' b'' s Lam GS FG HS HG : ℝ} (hU : 0 < U)
    (hQ2 : 0 ≤ Q2) (hQ1' : Q1 = U * Q2) (hQ : Q = U * Q1) (hJ : |J| ≤ Lam * U)
    (hLam : 0 ≤ Lam) (ha : a ^ 2 ≤ GS) (ha' : a' ^ 2 ≤ GS) (hb : b ^ 2 ≤ FG) (hb' : b' ^ 2 ≤ FG)
    (ha'' : |a''| ≤ HS) (hb'' : |b''| ≤ HG) :
    |s * (s - 1) * Q2 * a' * a * J ^ 2 + s * Q1 * a'' * J ^ 2 + s * Q1 * a * (2 * J * b') +
        s * Q1 * a' * (2 * J * b) + Q * (2 * b' * b + 2 * J * b'')| ≤
      (|s * (s - 1)| * Lam ^ 2 + 2 * |s| * Lam) * (Q * GS) + |s| * Lam ^ 2 * (Q * U * HS) +
      (2 * |s| * Lam + 2) * (Q * FG) + 2 * Lam * (Q * U * HG) := by
  have hQ1 : 0 ≤ Q1 := by rw [hQ1']; positivity
  have hQn : 0 ≤ Q := by rw [hQ]; positivity
  have hQQ : Q = U ^ 2 * Q2 := by rw [hQ, hQ1']; ring
  have hQ1U : Q1 * U = Q := by rw [hQ]; ring
  have hJ2 : J ^ 2 ≤ (Lam * U) ^ 2 := by
    rw [← sq_abs J]; exact pow_le_pow_left₀ (abs_nonneg _) hJ 2
  have hGS : 0 ≤ GS := (sq_nonneg a).trans ha
  have hFG : 0 ≤ FG := (sq_nonneg b).trans hb
  have hHS : 0 ≤ HS := (abs_nonneg _).trans ha''
  have hHG : 0 ≤ HG := (abs_nonneg _).trans hb''
  set X := |s * (s - 1)| with hX
  -- the six terms
  have t1 : |s * (s - 1) * Q2 * a' * a * J ^ 2| ≤ X * Lam ^ 2 * (Q * GS) := by
    have e : |s * (s - 1) * Q2 * a' * a * J ^ 2| = X * Q2 * (|a'| * |a|) * J ^ 2 := by
      simp only [hX, abs_mul, abs_of_nonneg hQ2, abs_pow, sq_abs]; ring
    rw [e]
    have h2 := abs_mul_le_of_sq_le ha' ha
    calc X * Q2 * (|a'| * |a|) * J ^ 2 ≤ X * Q2 * GS * (Lam * U) ^ 2 := by gcongr
      _ = X * Lam ^ 2 * (Q * GS) := by rw [hQQ]; ring
  have t2 : |s * Q1 * a'' * J ^ 2| ≤ |s| * Lam ^ 2 * (Q * U * HS) := by
    have e : |s * Q1 * a'' * J ^ 2| = |s| * Q1 * |a''| * J ^ 2 := by
      simp only [abs_mul, abs_of_nonneg hQ1, abs_pow, sq_abs]
    rw [e]
    calc |s| * Q1 * |a''| * J ^ 2 ≤ |s| * Q1 * HS * (Lam * U) ^ 2 := by gcongr
      _ = |s| * Lam ^ 2 * (Q * U * HS) := by rw [hQ]; try ring
  have t34 : ∀ {x y GX FY : ℝ}, x ^ 2 ≤ GX → y ^ 2 ≤ FY →
      |s * Q1 * x * (2 * J * y)| ≤ |s| * Lam * (Q * (GX + FY)) := by
    intro x y GX FY hx hy
    have e : |s * Q1 * x * (2 * J * y)| = |s| * Q1 * |J| * (2 * (|x| * |y|)) := by
      simp only [abs_mul, abs_of_nonneg hQ1, abs_two]; ring
    rw [e]
    have h2 := two_mul_abs_mul_le hx hy
    calc |s| * Q1 * |J| * (2 * (|x| * |y|)) ≤ |s| * Q1 * (Lam * U) * (GX + FY) := by gcongr
      _ = |s| * Lam * (Q * (GX + FY)) := by rw [← hQ1U]; ring
  have t3 := t34 ha hb'
  have t4 := t34 ha' hb
  have t5 : |Q * (2 * b' * b)| ≤ 2 * (Q * FG) := by
    have e : |Q * (2 * b' * b)| = Q * (2 * (|b'| * |b|)) := by
      simp only [abs_mul, abs_of_nonneg hQn, abs_two]; ring
    rw [e]
    have h2 := abs_mul_le_of_sq_le hb' hb
    calc Q * (2 * (|b'| * |b|)) ≤ Q * (2 * FG) := by gcongr
      _ = _ := by ring
  have t6 : |Q * (2 * J * b'')| ≤ 2 * Lam * (Q * U * HG) := by
    have e : |Q * (2 * J * b'')| = Q * (2 * |J| * |b''|) := by
      simp only [abs_mul, abs_of_nonneg hQn, abs_two]; try ring
    rw [e]
    calc Q * (2 * |J| * |b''|) ≤ Q * (2 * (Lam * U) * HG) := by gcongr
      _ = _ := by ring
  have hsplit : s * (s - 1) * Q2 * a' * a * J ^ 2 + s * Q1 * a'' * J ^ 2 +
      s * Q1 * a * (2 * J * b') + s * Q1 * a' * (2 * J * b) + Q * (2 * b' * b + 2 * J * b'') =
      s * (s - 1) * Q2 * a' * a * J ^ 2 + s * Q1 * a'' * J ^ 2 +
      s * Q1 * a * (2 * J * b') + s * Q1 * a' * (2 * J * b) + Q * (2 * b' * b) +
      Q * (2 * J * b'') := by ring
  have h6 : ∀ A B C D E G : ℝ,
      |A + B + C + D + E + G| ≤ |A| + |B| + |C| + |D| + |E| + |G| := by
    intro A B C D E G
    have := abs_add_le (A + B + C + D + E) G
    have := abs_add_le (A + B + C + D) E
    have := abs_add_le (A + B + C) D
    have := abs_add_le (A + B) C
    have := abs_add_le A B
    linarith
  rw [hsplit]
  refine (h6 _ _ _ _ _ _).trans ?_
  nlinarith [t1, t2, t3, t4, t5, t6]

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
