module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.IntegralEquation
import Mathlib.Tactic

/-!
# The power transformation of Kummer's equation

The calculus transformation is proved for actual twice differentiable functions, then
applied to the positive integral. No singular initial-value uniqueness is used.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

/-- First derivative of a power times a differentiable function. -/
theorem hasDerivAt_power_mul (f : ℝ → ℝ) (p z : ℝ) (hz : 0 < z)
    (hf : HasDerivAt f (deriv f z) z) :
    HasDerivAt (fun w => w ^ p * f w)
      (p * z ^ (p - 1) * f z + z ^ p * deriv f z) z :=
  (Real.hasDerivAt_rpow_const (Or.inl hz.ne')).mul hf

/-- Exact second derivative of a power product on the positive half-line. -/
theorem deriv_deriv_power_mul (f : ℝ → ℝ) (p z : ℝ) (hz : 0 < z)
    (hf : ∀ w ∈ Ioi (0 : ℝ), HasDerivAt f (deriv f w) w)
    (hf' : HasDerivAt (deriv f) (deriv (deriv f) z) z) :
    deriv (deriv (fun w => w ^ p * f w)) z =
      p * (p - 1) * z ^ (p - 2) * f z +
        2 * p * z ^ (p - 1) * deriv f z + z ^ p * deriv (deriv f) z := by
  have h1 := ((Real.hasDerivAt_rpow_const (p := p - 1) (Or.inl hz.ne')).const_mul p).mul
    (hf z hz)
  have h2 := (Real.hasDerivAt_rpow_const (p := p) (Or.inl hz.ne')).mul hf'
  have heq : deriv (fun w => w ^ p * f w) =ᶠ[𝓝 z]
      fun w => p * w ^ (p - 1) * f w + w ^ p * deriv f w := by
    filter_upwards [Ioi_mem_nhds hz] with w hw
    exact (hasDerivAt_power_mul f p w hw (hf w hw)).deriv
  have h := ((h1.add h2).congr_of_eventuallyEq heq).deriv
  rw [show p - 1 - 1 = p - 2 by ring] at h
  exact h.trans (by ring)

/-- Power transformation of Kummer's equation on the nonsingular domain. -/
theorem power_mul_kummer_ode (f : ℝ → ℝ) (c p z : ℝ) (hz : 0 < z)
    (hf : ∀ w ∈ Ioi (0 : ℝ), HasDerivAt f (deriv f w) w)
    (hf' : HasDerivAt (deriv f) (deriv (deriv f) z) z)
    (hode : z * deriv (deriv f) z + (p + 1 - z) * deriv f z - c * f z = 0) :
    z * deriv (deriv (fun w => w ^ p * f w)) z +
      (1 - p - z) * deriv (fun w => w ^ p * f w) z -
      (c - p) * (z ^ p * f z) = 0 := by
  rw [deriv_deriv_power_mul f p z hz hf hf',
    (hasDerivAt_power_mul f p z hz (hf z hz)).deriv]
  have h1 : z ^ (p - 1) = z ^ (p - 2) * z := by
    rw [← Real.rpow_add_one hz.ne']
    congr 1
    ring
  have h2 : z ^ p = z ^ (p - 2) * z * z := by
    rw [← h1, ← Real.rpow_add_one hz.ne']
    congr 1
    ring
  rw [h1, h2]
  linear_combination z ^ (p - 2) * z * z * hode

/-- The transformed negative-shape integral solves the required Kummer equation. -/
theorem UNr_ode (a : NegThird) (z : ℝ) (hz : 0 < z) :
    z * deriv (deriv (UNr a)) z + (2 / 3 - z) * deriv (UNr a) z - a.1 * UNr a z = 0 := by
  let c : Pos := ⟨a.1 + 1 / 3, by linarith only [a.2.1]⟩
  have hs := contDiffOn_UIr c (4 / 3)
  have hf : ∀ w ∈ Ioi (0 : ℝ), HasDerivAt (UIr c (4 / 3))
      (deriv (UIr c (4 / 3)) w) w := by
    intro w hw
    exact (hasDerivAt_UIr c (4 / 3) w hw).differentiableAt.hasDerivAt
  have hf' := (hs.deriv_of_isOpen isOpen_Ioi (by norm_num : (1 : ℕ∞ω) + 1 ≤ ∞))
    |>.differentiableOn (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have hd := (hf' z hz).differentiableAt (isOpen_Ioi.mem_nhds hz)
  have ho := UIr_ode c (4 / 3) z hz
  have h := power_mul_kummer_ode (UIr c (4 / 3)) c.1 (1 / 3) z hz hf hd.hasDerivAt
    (by convert ho using 1; norm_num)
  rw [show c.1 - 1 / 3 = a.1 by dsimp only [c]; ring,
    show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num] at h
  change z * deriv (deriv (fun w => w ^ (1 / 3 : ℝ) * UIr c (4 / 3) w)) z +
    (2 / 3 - z) * deriv (fun w => w ^ (1 / 3 : ℝ) * UIr c (4 / 3) w) z -
    a.1 * (z ^ (1 / 3 : ℝ) * UIr c (4 / 3) z) = 0
  exact h

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
