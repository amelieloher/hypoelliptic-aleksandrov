module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Calculus
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# The auxiliary Gaussian flow: definitions

definition the Gaussian flow. The kernel `Φ_h` is the centred Gaussian
density on phase space `y = (v, z)` with covariance `Σ_h`; it is a product of the two-dimensional
densities `φ_h(z_i, v_i)`. For `λ, h > 0` the pair density is rewritten in the form
`κ * exp (-(a u² + b u w + c w²))` with explicit coefficients, which is the form used throughout.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open Real

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ}

/-- The two-dimensional Gaussian `φ_h(u, w)` of the Gaussian flow; `u` is the position component and
`w`
the velocity component, `D_h = 5 λ² h⁴ / 12`. -/
def flowPairDensity (lam h u w : ℝ) : ℝ :=
  1 / (2 * π * √(5 * lam ^ 2 * h ^ 4 / 12)) *
    exp (-(lam * h * u ^ 2 + lam * h ^ 2 * u * w + 2 * lam * h ^ 3 / 3 * w ^ 2) /
      (2 * (5 * lam ^ 2 * h ^ 4 / 12)))

/-- The kernel `Φ_h` of the Gaussian flow at `y = (v, z)`: the product of the pair densities
`φ_h(z_i, v_i)`. -/
def flowKernel (lam h : ℝ) (y : EvolutionAmbientState d) : ℝ :=
  ∏ i, flowPairDensity lam h (y.2 i) (y.1 i)

/-- The constant `c_{d,λ} = (2π)^{-d} (12/5)^{d/2} λ^{-d}` with `sup Φ_h = c_{d,λ} h^{-2d}`. -/
def flowSupConstant (d : ℕ) (lam : ℝ) : ℝ :=
  (2 * π) ^ (-(d : ℝ)) * (12 / 5 : ℝ) ^ ((d : ℝ) / 2) * lam ^ (-(d : ℝ))

/-- Normalising constant of the pair density: `√(12/5) / (2 π λ h²)`. -/
def flowConst (lam h : ℝ) : ℝ := √(12 / 5) / (2 * π * lam * h ^ 2)

/-- Coefficient of `u²` in the exponent of the pair density: `6 / (5 λ h³)`. -/
def flowA (lam h : ℝ) : ℝ := 6 / (5 * lam * h ^ 3)

/-- Coefficient of `u w` in the exponent of the pair density: `6 / (5 λ h²)`. -/
def flowB (lam h : ℝ) : ℝ := 6 / (5 * lam * h ^ 2)

/-- Coefficient of `w²` in the exponent of the pair density: `4 / (5 λ h)`. -/
def flowC (lam h : ℝ) : ℝ := 4 / (5 * lam * h)

/-- The pair density in normal form. -/
theorem flowPairDensity_eq {lam h : ℝ} (hl : 0 < lam) (hh : 0 < h) (u w : ℝ) :
    flowPairDensity lam h u w = flowConst lam h *
      exp (-(flowA lam h * u ^ 2 + flowB lam h * u * w + flowC lam h * w ^ 2)) := by
  unfold flowPairDensity flowConst flowA flowB flowC
  have hs : 0 < √(12 / 5 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hD : √(5 * lam ^ 2 * h ^ 4 / 12) = lam * h ^ 2 / √(12 / 5) := by
    have h1 : (5 * lam ^ 2 * h ^ 4 / 12 : ℝ) = (lam * h ^ 2) ^ 2 * ((12 / 5 : ℝ))⁻¹ := by
      field_simp
    rw [h1, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity), Real.sqrt_inv]
    field_simp
  rw [hD]
  congr 1
  · field_simp
  · congr 1
    field_simp
    ring

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
