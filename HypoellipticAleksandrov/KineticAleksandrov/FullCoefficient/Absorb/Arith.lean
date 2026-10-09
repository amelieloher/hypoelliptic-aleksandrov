module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The exponent range `q ≤ q_*`

Arithmetic used by the absorption estimate: for
`1 < q ≤ q_* = 1 + 3λ²/(128 d² Λ²)` one has `q ≤ 4/3`, `2d(q-1) < 1` and
`16 d² q (q-1) Λ²/λ² ≤ 1/2`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

theorem qstar_facts {d : ℕ} {lam Lam q : ℝ} (hd : 1 ≤ d) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hq : 1 < q) (hqΛ : q ≤ 1 + 3 * lam ^ 2 / (128 * (d : ℝ) ^ 2 * Lam ^ 2)) :
    q ≤ 4 / 3 ∧ 2 * d * (q - 1) < 1 ∧
      16 * d * q * (q - 1) / lam ^ 2 * (d * Lam ^ 2) ≤ 1 / 2 := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hLam0 : 0 < Lam := hlam.trans_le hLam
  set x : ℝ := 3 * lam ^ 2 / (128 * (d : ℝ) ^ 2 * Lam ^ 2) with hx
  have hx0 : 0 < x := by positivity
  have hq1x : q - 1 ≤ x := by linarith
  have hratio : lam ^ 2 / Lam ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith
  have hxle : x ≤ 3 / 128 := by
    have : x = 3 / 128 * (lam ^ 2 / Lam ^ 2) / (d : ℝ) ^ 2 := by rw [hx]; field_simp
    rw [this]
    have h2 : (1 : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
    calc 3 / 128 * (lam ^ 2 / Lam ^ 2) / (d : ℝ) ^ 2 ≤ 3 / 128 * 1 / 1 := by
          gcongr
      _ = 3 / 128 := by norm_num
  have hq43 : q ≤ 4 / 3 := by linarith
  refine ⟨hq43, ?_, ?_⟩
  · have : 2 * (d : ℝ) * (q - 1) ≤ 2 * d * x := by gcongr
    have h3 : 2 * (d : ℝ) * x = 6 / 128 * (lam ^ 2 / Lam ^ 2) / d := by rw [hx]; field_simp; ring
    have h4 : 6 / 128 * (lam ^ 2 / Lam ^ 2) / (d : ℝ) ≤ 6 / 128 := by
      calc 6 / 128 * (lam ^ 2 / Lam ^ 2) / (d : ℝ) ≤ 6 / 128 * 1 / 1 := by gcongr
        _ = 6 / 128 := by norm_num
    linarith
  · have e : 16 * (d : ℝ) * q * (q - 1) / lam ^ 2 * (d * Lam ^ 2) =
        (16 * (d : ℝ) ^ 2 * Lam ^ 2 / lam ^ 2) * (q * (q - 1)) := by ring
    rw [e]
    have hqq : q * (q - 1) ≤ 4 / 3 * x :=
      mul_le_mul hq43 hq1x (by linarith) (by norm_num)
    calc (16 * (d : ℝ) ^ 2 * Lam ^ 2 / lam ^ 2) * (q * (q - 1))
        ≤ (16 * (d : ℝ) ^ 2 * Lam ^ 2 / lam ^ 2) * (4 / 3 * x) :=
          mul_le_mul_of_nonneg_left hqq (by positivity)
      _ = 1 / 2 := by rw [hx]; field_simp; norm_num

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
