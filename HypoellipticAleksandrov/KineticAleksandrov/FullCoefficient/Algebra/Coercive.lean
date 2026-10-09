module

public import PDEFoundation.Ambient.EuclideanNorm
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Coercivity of the flow form

The coercivity estimate. For `h, lam > 0`, the quadratic form
`Mform` of the covariance operator `M^h` controls `(lam/4) |ξ_v|²`, and the form `Gform` of the
diffusion matrix controls `(1/4) Mform + (lam/4) |ξ_v|²`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open Matrix
open scoped MatrixOrder

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ}

/-- The quadratic form `|ξ|²_{M^h} = (lam/2)(2h²|ξ_z|² - 2h ξ_z·ξ_v + |ξ_v|²)`. -/
def Mform (lam h : ℝ) (ξz ξv : PDE.Vec d) : ℝ :=
  lam / 2 * (2 * h ^ 2 * PDE.vecDot ξz ξz - 2 * h * PDE.vecDot ξz ξv + PDE.vecDot ξv ξv)

/-- The quadratic form `ξ·Gξ = (lam h²/2)|ξ_z|² - lam h ξ_z·ξ_v + ξ_v·β ξ_v`. -/
def Gform (lam h : ℝ) (β : PDE.Mat d) (ξz ξv : PDE.Vec d) : ℝ :=
  lam * h ^ 2 / 2 * PDE.vecDot ξz ξz - lam * h * PDE.vecDot ξz ξv
    + PDE.vecDot ξv (β *ᵥ ξv)

/-- Coordinate expansion of a quadratic expression in two vectors. -/
theorem sum_quad (a b c : ℝ) (x y : PDE.Vec d) :
    ∑ i, (a * (x i * x i) + b * (x i * y i) + c * (y i * y i))
      = a * PDE.vecDot x x + b * PDE.vecDot x y + c * PDE.vecDot y y := by
  simp only [PDE.vecDot, Finset.mul_sum, Finset.sum_add_distrib]

/-- The termwise bound `(lam/4)|ξ_v|² ≤ Mform`, coordinate-wise square form. -/
theorem Mform_sub_eq_sum (lam h : ℝ) (ξz ξv : PDE.Vec d) :
    Mform lam h ξz ξv - lam / 4 * PDE.vecDot ξv ξv
      = lam * ∑ i, (h * ξz i - ξv i / 2) ^ 2 := by
  have : ∑ i, (h * ξz i - ξv i / 2) ^ 2
      = ∑ i, (h ^ 2 * (ξz i * ξz i) + (-h) * (ξz i * ξv i) + (1 / 4) * (ξv i * ξv i)) :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [this, sum_quad]
  unfold Mform
  ring

/-- Coercivity of `M^h`. -/
theorem Mform_ge {lam h : ℝ} (hlam : 0 < lam) (ξz ξv : PDE.Vec d) :
    lam / 4 * PDE.vecDot ξv ξv ≤ Mform lam h ξz ξv := by
  have := Mform_sub_eq_sum lam h ξz ξv
  have h0 : 0 ≤ lam * ∑ i, (h * ξz i - ξv i / 2) ^ 2 :=
    mul_nonneg hlam.le (Finset.sum_nonneg fun i _ => sq_nonneg _)
  linarith

/-- Coercivity of `G`. -/
theorem Gform_ge {lam h : ℝ} (hlam : 0 < lam) {β : PDE.Mat d}
    (hβ : lam • (1 : PDE.Mat d) ≤ β) (ξz ξv : PDE.Vec d) :
    1 / 4 * Mform lam h ξz ξv + lam / 4 * PDE.vecDot ξv ξv ≤ Gform lam h β ξz ξv := by
  have hpsd : (β - lam • (1 : PDE.Mat d)).PosSemidef := Matrix.le_iff.mp hβ
  have hq := hpsd.dotProduct_mulVec_nonneg ξv
  have hq' : lam * PDE.vecDot ξv ξv ≤ PDE.vecDot ξv (β *ᵥ ξv) := by
    simp only [star_trivial, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub,
      dotProduct_smul, smul_eq_mul] at hq
    simpa [PDE.vecDot, dotProduct] using hq
  have hs : 0 ≤ lam / 8 * ∑ i, (2 * (h * ξz i - 3 / 2 * ξv i) ^ 2 + ξv i ^ 2 / 2) := by
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => by positivity)
  have hexp : lam / 8 * ∑ i, (2 * (h * ξz i - 3 / 2 * ξv i) ^ 2 + ξv i ^ 2 / 2)
      = lam * h ^ 2 / 4 * PDE.vecDot ξz ξz - 3 * lam * h / 4 * PDE.vecDot ξz ξv
        + 5 * lam / 8 * PDE.vecDot ξv ξv := by
    have : ∑ i, (2 * (h * ξz i - 3 / 2 * ξv i) ^ 2 + ξv i ^ 2 / 2)
        = ∑ i, (2 * h ^ 2 * (ξz i * ξz i) + (-6 * h) * (ξz i * ξv i)
            + 5 * (ξv i * ξv i)) :=
      Finset.sum_congr rfl fun i _ => by ring
    rw [this, sum_quad]
    ring
  unfold Mform Gform
  nlinarith [hs, hexp, hq']

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
