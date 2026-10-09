module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarConstants
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.Integral
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.MEquation
import Mathlib.Tactic

/-!
# Literal scalar pieces

The exponent is restricted to the source interval by typing data. In particular the
positive piece uses the convergent transformed U integral, never a negative-shape integral.
The second M term retains the signed real variable `s`.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/-- The source scalar exponent interval. -/
abbrev ScalarGamma := {gamma : ℝ // 0 < gamma ∧ gamma < 1 / 3}

/-- The negative Kummer parameter belonging to a source scalar exponent. -/
def ScalarGamma.negative (gamma : ScalarGamma) : Kummer.NegThird :=
  ⟨-gamma.1, by constructor <;> linarith only [gamma.2.1, gamma.2.2]⟩

/-- The positive-s source piece; only its values at positive `s` are consumed. -/
def Fplus (gamma : ScalarGamma) (Lam s : ℝ) : ℝ :=
  Kummer.UNr gamma.negative (s ^ 3 / (9 * Lam))

/-- The negative-s source piece with its signed linear prefactor. -/
def Fminus (gamma : ScalarGamma) (Lam s : ℝ) : ℝ :=
  gammaA gamma.1 * Kummer.M (-gamma.1) Kummer.b23 (s ^ 3 / 9) +
    gammaB gamma.1 * s / Real.rpow (9 * Lam) (1 / 3) *
      Kummer.M (1 / 3 - gamma.1) Kummer.b43 (s ^ 3 / 9)

/-- The piecewise source profile, with the connection value specified at zero. -/
def F (gamma : ScalarGamma) (Lam s : ℝ) : ℝ :=
  if 0 < s then Fplus gamma Lam s
  else if s < 0 then Fminus gamma Lam s else gammaA gamma.1

/-- The value at the joining point is the literal connection constant. -/
@[simp] theorem F_zero (gamma : ScalarGamma) (Lam : ℝ) :
    F gamma Lam 0 = gammaA gamma.1 := by
  simp only [F, lt_self_iff_false, ↓reduceIte]

/-- The entire negative piece already has the correct value at zero. -/
@[simp] theorem Fminus_zero (gamma : ScalarGamma) (Lam : ℝ) :
    Fminus gamma Lam 0 = gammaA gamma.1 := by
  simp only [Fminus, zero_pow (by decide : 3 ≠ 0), zero_div, Kummer.M_zero,
    mul_one, mul_zero, add_zero]

/-- The positive piece is strictly positive on its consumed half-line. -/
theorem Fplus_pos (gamma : ScalarGamma) (Lam s : ℝ) (hLam : 0 < Lam) (hs : 0 < s) :
    0 < Fplus gamma Lam s :=
  Kummer.UNr_pos gamma.negative _ (div_pos (pow_pos hs 3) (mul_pos (by norm_num) hLam))

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
