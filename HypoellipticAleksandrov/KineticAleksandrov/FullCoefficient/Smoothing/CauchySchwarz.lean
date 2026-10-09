module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Algebra.QuadraticDiscriminant

/-!
# A weighted Cauchy--Schwarz inequality for integrals

`(∫ u)² ≤ (∫ u² / p) (∫ p)` for a positive weight `p`. This is the Cauchy--Schwarz step in the
Fisher-type bounds of the smoothing estimates.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

theorem sq_integral_le_mul {α : Type*} [MeasurableSpace α] {μ : Measure α} {u p : α → ℝ}
    (hp : ∀ a, 0 < p a) (hpi : Integrable p μ) (hu : Integrable u μ)
    (hq : Integrable (fun a => u a ^ 2 / p a) μ) :
    (∫ a, u a ∂μ) ^ 2 ≤ (∫ a, u a ^ 2 / p a ∂μ) * ∫ a, p a ∂μ := by
  have key : ∀ t : ℝ, 0 ≤ (∫ a, p a ∂μ) * (t * t) + (-2 * ∫ a, u a ∂μ) * t +
      ∫ a, u a ^ 2 / p a ∂μ := by
    intro t
    have hpt : ∀ a, 0 ≤ u a ^ 2 / p a - 2 * t * u a + t ^ 2 * p a := fun a => by
      have hpa := hp a
      have : u a ^ 2 / p a - 2 * t * u a + t ^ 2 * p a = (u a - t * p a) ^ 2 / p a := by
        field_simp
        ring
      rw [this]
      positivity
    have h0 : 0 ≤ ∫ a, (u a ^ 2 / p a - 2 * t * u a + t ^ 2 * p a) ∂μ :=
      integral_nonneg hpt
    have hint : ∫ a, (u a ^ 2 / p a - 2 * t * u a + t ^ 2 * p a) ∂μ =
        (∫ a, u a ^ 2 / p a ∂μ) - 2 * t * (∫ a, u a ∂μ) + t ^ 2 * ∫ a, p a ∂μ := by
      have h1 : Integrable (fun a => u a ^ 2 / p a - 2 * t * u a) μ :=
        hq.sub (hu.const_mul (2 * t))
      rw [integral_add h1 (hpi.const_mul (t ^ 2)), integral_sub hq (hu.const_mul (2 * t)),
        integral_const_mul, integral_const_mul]
    rw [hint] at h0
    nlinarith [h0]
  have := discrim_le_zero key
  rw [discrim] at this
  nlinarith [this]

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
