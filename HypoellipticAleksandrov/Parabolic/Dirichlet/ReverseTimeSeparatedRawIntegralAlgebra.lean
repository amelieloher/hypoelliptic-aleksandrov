module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSeparatedRawIntegrability

/-!
# Fixed-time algebra for reverse-time separated raw terms

The public theorem in this module has the following boundary: given integrability of each
fixed-time raw family and explicit expansions of the mass, spatial form, and negative source
scalars, it rewrites the spatial integral of the literal raw slice as
`M * eta.deriv τ - A * eta τ + S * eta τ`.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Matrix.Norms.Elementwise MatrixOrder

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

private theorem integral_double_sum
    {d : ℕ} {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (p : Fin d → Fin d → X → ℝ)
    (hp : ∀ i j : Fin d, Integrable (p i j) μ) :
    (∫ x, ∑ i : Fin d, ∑ j : Fin d, p i j x ∂μ) =
      ∑ i : Fin d, ∑ j : Fin d, ∫ x, p i j x ∂μ := by
  have hpi (i : Fin d) : Integrable (fun x => ∑ j : Fin d, p i j x) μ :=
    integrable_finset_sum Finset.univ fun j _ => hp i j
  rw [integral_finset_sum Finset.univ (fun i _ => hpi i)]
  simp_rw [integral_finset_sum Finset.univ (fun j _ => hp _ j)]

private theorem integral_single_sum
    {d : ℕ} {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (q : Fin d → X → ℝ) (hq : ∀ j : Fin d, Integrable (q j) μ) :
    (∫ x, ∑ j : Fin d, q j x ∂μ) = ∑ j : Fin d, ∫ x, q j x ∂μ := by
  exact integral_finset_sum Finset.univ fun j _ => hq j

/-- Fixed-time integration of the literal reverse-time raw slice agrees with the three
expanded residual scalars. -/
theorem reverseTime_raw_slice_integral_eq_residual
    {d : ℕ} {Ω : Set (PDE.Vec d)} {T : ℝ}
    (r₁ τ : ℝ)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c F : ℝ → PDE.Vec d → ℝ)
    (U : TimeVelocity d → ℝ) (G : Fin d → TimeVelocity d → ℝ)
    (eta : ReverseTimeScalarTest T) (psi : PDE.WeakTestFunction Ω)
    (M A S : ℝ)
    (hmass : Integrable (fun y => U (τ, y) * eta.deriv τ * psi y)
      (PDE.volumeOn Ω))
    (hprincipal : ∀ i j : Fin d, Integrable (fun y =>
      reverseTimeCoefficient r₁ a τ y i j * G j (τ, y) *
        psi.partialDeriv i y * eta τ) (PDE.volumeOn Ω))
    (hdrift : ∀ j : Fin d, Integrable (fun y =>
      reverseTimeDivergenceDrift r₁ a b τ y j * G j (τ, y) *
        psi y * eta τ) (PDE.volumeOn Ω))
    (hscalar : Integrable (fun y =>
      reverseTimeScalarCoefficient r₁ c τ y * U (τ, y) *
        psi y * eta τ) (PDE.volumeOn Ω))
    (hsource : Integrable (fun y =>
      reverseTimeScalarCoefficient r₁ F τ y * psi y * eta τ)
      (PDE.volumeOn Ω))
    (hmassExpand : M = ∫ y, U (τ, y) * psi y ∂PDE.volumeOn Ω)
    (hformExpand : A =
      (∑ i : Fin d, ∑ j : Fin d,
        ∫ y, reverseTimeCoefficient r₁ a τ y i j * G j (τ, y) *
          psi.partialDeriv i y ∂PDE.volumeOn Ω) +
      (∑ j : Fin d, ∫ y,
        reverseTimeDivergenceDrift r₁ a b τ y j * G j (τ, y) * psi y
          ∂PDE.volumeOn Ω) -
      ∫ y, reverseTimeScalarCoefficient r₁ c τ y * U (τ, y) * psi y
        ∂PDE.volumeOn Ω)
    (hsourceExpand : S =
      -(∫ y, reverseTimeScalarCoefficient r₁ F τ y * psi y
        ∂PDE.volumeOn Ω)) :
    (∫ y,
      U (τ, y) * eta.deriv τ * psi y -
        (∑ i : Fin d, ∑ j : Fin d,
          reverseTimeCoefficient r₁ a τ y i j * G j (τ, y) *
            psi.partialDeriv i y) * eta τ -
        (∑ j : Fin d,
          reverseTimeDivergenceDrift r₁ a b τ y j * G j (τ, y) * psi y) * eta τ +
        reverseTimeScalarCoefficient r₁ c τ y * U (τ, y) * psi y * eta τ -
        reverseTimeScalarCoefficient r₁ F τ y * psi y * eta τ
      ∂PDE.volumeOn Ω) =
      M * eta.deriv τ - A * eta τ + S * eta τ := by
  let p : Fin d → Fin d → PDE.Vec d → ℝ := fun i j y =>
    reverseTimeCoefficient r₁ a τ y i j * G j (τ, y) *
      psi.partialDeriv i y * eta τ
  let q : Fin d → PDE.Vec d → ℝ := fun j y =>
    reverseTimeDivergenceDrift r₁ a b τ y j * G j (τ, y) * psi y * eta τ
  have hpSum : Integrable (fun y => ∑ i : Fin d, ∑ j : Fin d, p i j y)
      (PDE.volumeOn Ω) :=
    integrable_finset_sum Finset.univ fun i _ =>
      integrable_finset_sum Finset.univ fun j _ => hprincipal i j
  have hqSum : Integrable (fun y => ∑ j : Fin d, q j y) (PDE.volumeOn Ω) :=
    integrable_finset_sum Finset.univ fun j _ => hdrift j
  have hraw : Integrable (fun y =>
      U (τ, y) * eta.deriv τ * psi y -
        (∑ i : Fin d, ∑ j : Fin d, p i j y) -
        (∑ j : Fin d, q j y) +
        reverseTimeScalarCoefficient r₁ c τ y * U (τ, y) * psi y * eta τ -
        reverseTimeScalarCoefficient r₁ F τ y * psi y * eta τ)
      (PDE.volumeOn Ω) :=
    (((hmass.sub hpSum).sub hqSum).add hscalar).sub hsource
  simp_rw [Finset.sum_mul]
  change (∫ y, ((((fun y => U (τ, y) * eta.deriv τ * psi y) -
      (fun y => ∑ i : Fin d, ∑ j : Fin d, p i j y)) -
      (fun y => ∑ j : Fin d, q j y)) +
      (fun y => reverseTimeScalarCoefficient r₁ c τ y * U (τ, y) * psi y * eta τ)) y -
      reverseTimeScalarCoefficient r₁ F τ y * psi y * eta τ
      ∂PDE.volumeOn Ω) = _
  rw [integral_sub (((hmass.sub hpSum).sub hqSum).add hscalar) hsource]
  change ((∫ y, ((((fun y => U (τ, y) * eta.deriv τ * psi y) -
      (fun y => ∑ i : Fin d, ∑ j : Fin d, p i j y)) -
      (fun y => ∑ j : Fin d, q j y)) y +
      reverseTimeScalarCoefficient r₁ c τ y * U (τ, y) * psi y * eta τ)
      ∂PDE.volumeOn Ω) - _) = _
  rw [integral_add ((hmass.sub hpSum).sub hqSum) hscalar]
  change ((((∫ y, (((fun y => U (τ, y) * eta.deriv τ * psi y) -
      (fun y => ∑ i : Fin d, ∑ j : Fin d, p i j y)) y -
      ∑ j : Fin d, q j y) ∂PDE.volumeOn Ω) + _) - _)) = _
  rw [integral_sub (hmass.sub hpSum) hqSum]
  change (((((∫ y, U (τ, y) * eta.deriv τ * psi y -
      ∑ i : Fin d, ∑ j : Fin d, p i j y ∂PDE.volumeOn Ω) - _) + _) - _)) = _
  rw [integral_sub hmass hpSum,
    integral_double_sum (PDE.volumeOn Ω) p (by
      intro i j
      simpa only [p] using hprincipal i j),
    integral_single_sum (PDE.volumeOn Ω) q (by
      intro j
      simpa only [q] using hdrift j)]
  have hmassPull :
      (∫ y, U (τ, y) * eta.deriv τ * psi y ∂PDE.volumeOn Ω) =
        (∫ y, U (τ, y) * psi y ∂PDE.volumeOn Ω) * eta.deriv τ := by
    calc
      _ = ∫ y, (U (τ, y) * psi y) * eta.deriv τ ∂PDE.volumeOn Ω := by
        apply integral_congr_ae
        filter_upwards [] with y
        ring
      _ = _ := integral_mul_const _ _
  have hprincipalPull (i j : Fin d) :
      (∫ y, p i j y ∂PDE.volumeOn Ω) =
        (∫ y, reverseTimeCoefficient r₁ a τ y i j * G j (τ, y) *
          psi.partialDeriv i y ∂PDE.volumeOn Ω) * eta τ := by
    dsimp only [p]
    exact integral_mul_const _ _
  have hdriftPull (j : Fin d) :
      (∫ y, q j y ∂PDE.volumeOn Ω) =
        (∫ y, reverseTimeDivergenceDrift r₁ a b τ y j * G j (τ, y) * psi y
          ∂PDE.volumeOn Ω) * eta τ := by
    dsimp only [q]
    exact integral_mul_const _ _
  have hscalarPull :
      (∫ y, reverseTimeScalarCoefficient r₁ c τ y * U (τ, y) * psi y * eta τ
        ∂PDE.volumeOn Ω) =
      (∫ y, reverseTimeScalarCoefficient r₁ c τ y * U (τ, y) * psi y
        ∂PDE.volumeOn Ω) * eta τ :=
    integral_mul_const _ _
  have hsourcePull :
      (∫ y, reverseTimeScalarCoefficient r₁ F τ y * psi y * eta τ
        ∂PDE.volumeOn Ω) =
      (∫ y, reverseTimeScalarCoefficient r₁ F τ y * psi y
        ∂PDE.volumeOn Ω) * eta τ :=
    integral_mul_const _ _
  rw [hmassPull, hscalarPull, hsourcePull]
  simp_rw [hprincipalPull, hdriftPull]
  simp_rw [← Finset.sum_mul]
  rw [← hmassExpand, hformExpand, hsourceExpand]
  ring

end HypoellipticAleksandrov.Parabolic.Dirichlet
