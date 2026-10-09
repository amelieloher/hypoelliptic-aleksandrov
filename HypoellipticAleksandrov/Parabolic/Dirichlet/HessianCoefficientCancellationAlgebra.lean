module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Algebra for Hessian coefficient cancellation

This module isolates the finite-sum integral algebra used to cancel divergence-form coefficient
derivatives against weak Hessian identities.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- Finite-sum algebra turning a divergence-form raw identity and its weighted
weak integration-by-parts identities into the corresponding Hessian identity. -/
theorem integral_mass_eq_neg_integral_hessian_add_drift_add_scalar_sub_source
    {X : Type*} [MeasurableSpace X] {d : ℕ} (mu : Measure X)
    (mass scalar source : X → ℝ)
    (grouped hessian : Fin d → Fin d → X → ℝ)
    (drift : Fin d → X → ℝ)
    (hmass : Integrable mass mu)
    (hgrouped : ∀ i j : Fin d, Integrable (grouped i j) mu)
    (hhessian : ∀ i j : Fin d, Integrable (hessian i j) mu)
    (hdrift : ∀ j : Fin d, Integrable (drift j) mu)
    (hscalar : Integrable scalar mu)
    (hsource : Integrable source mu)
    (hraw : (∫ x,
      mass x -
        (∑ i : Fin d, ∑ j : Fin d, grouped i j x) +
        (∑ j : Fin d, drift j x) +
        scalar x - source x ∂mu) = 0)
    (hweak : ∀ i j : Fin d,
      (∫ x, grouped i j x ∂mu) =
        -(∫ x, hessian i j x ∂mu)) :
    (∫ x, mass x ∂mu) =
      -(∫ x,
        (∑ i : Fin d, ∑ j : Fin d, hessian i j x) +
        (∑ j : Fin d, drift j x) + scalar x - source x ∂mu) := by
  have hgroupedSum : Integrable
      (fun x => ∑ i : Fin d, ∑ j : Fin d, grouped i j x) mu :=
    integrable_finset_sum Finset.univ fun i _ =>
      integrable_finset_sum Finset.univ fun j _ => hgrouped i j
  have hhessianSum : Integrable
      (fun x => ∑ i : Fin d, ∑ j : Fin d, hessian i j x) mu :=
    integrable_finset_sum Finset.univ fun i _ =>
      integrable_finset_sum Finset.univ fun j _ => hhessian i j
  have hdriftSum : Integrable (fun x => ∑ j : Fin d, drift j x) mu :=
    integrable_finset_sum Finset.univ fun j _ => hdrift j
  have hgroupedIntegral :
      (∫ x, ∑ i : Fin d, ∑ j : Fin d, grouped i j x ∂mu) =
        ∑ i : Fin d, ∑ j : Fin d, ∫ x, grouped i j x ∂mu := by
    rw [integral_finset_sum Finset.univ (fun i _ =>
      integrable_finset_sum Finset.univ fun j _ => hgrouped i j)]
    simp_rw [integral_finset_sum Finset.univ (fun j _ => hgrouped _ j)]
  have hdriftIntegral :
      (∫ x, ∑ j : Fin d, drift j x ∂mu) =
        ∑ j : Fin d, ∫ x, drift j x ∂mu :=
    integral_finset_sum Finset.univ fun j _ => hdrift j
  have hraw' :
      (∫ x, mass x ∂mu) -
        (∑ i : Fin d, ∑ j : Fin d, ∫ x, grouped i j x ∂mu) +
        (∑ j : Fin d, ∫ x, drift j x ∂mu) +
        (∫ x, scalar x ∂mu) - (∫ x, source x ∂mu) = 0 := by
    have e₁ : (∫ x, mass x - (∑ i : Fin d, ∑ j : Fin d, grouped i j x) ∂mu) =
        (∫ x, mass x ∂mu) - ∫ x, ∑ i : Fin d, ∑ j : Fin d, grouped i j x ∂mu :=
      integral_sub hmass hgroupedSum
    have e₂ : (∫ x, mass x - (∑ i : Fin d, ∑ j : Fin d, grouped i j x) +
        (∑ j : Fin d, drift j x) ∂mu) =
        ((∫ x, mass x ∂mu) - ∫ x, ∑ i : Fin d, ∑ j : Fin d, grouped i j x ∂mu) +
          ∫ x, ∑ j : Fin d, drift j x ∂mu := by
      calc
        _ = (∫ x, mass x - (∑ i : Fin d, ∑ j : Fin d, grouped i j x) ∂mu) +
            ∫ x, ∑ j : Fin d, drift j x ∂mu := by
          simpa only [Pi.sub_apply, Pi.add_apply] using
            integral_add (hmass.sub hgroupedSum) hdriftSum
        _ = _ := by rw [e₁]
    have e₃ : (∫ x, mass x - (∑ i : Fin d, ∑ j : Fin d, grouped i j x) +
        (∑ j : Fin d, drift j x) + scalar x ∂mu) =
        (((∫ x, mass x ∂mu) - ∫ x, ∑ i : Fin d, ∑ j : Fin d, grouped i j x ∂mu) +
          ∫ x, ∑ j : Fin d, drift j x ∂mu) + ∫ x, scalar x ∂mu := by
      calc
        _ = (∫ x, mass x - (∑ i : Fin d, ∑ j : Fin d, grouped i j x) +
            (∑ j : Fin d, drift j x) ∂mu) + ∫ x, scalar x ∂mu := by
          simpa only [Pi.sub_apply, Pi.add_apply] using
            integral_add ((hmass.sub hgroupedSum).add hdriftSum) hscalar
        _ = _ := by rw [e₂]
    have e₄ : (∫ x, mass x - (∑ i : Fin d, ∑ j : Fin d, grouped i j x) +
        (∑ j : Fin d, drift j x) + scalar x - source x ∂mu) =
        ((((∫ x, mass x ∂mu) - ∫ x, ∑ i : Fin d, ∑ j : Fin d, grouped i j x ∂mu) +
          ∫ x, ∑ j : Fin d, drift j x ∂mu) + ∫ x, scalar x ∂mu) -
          ∫ x, source x ∂mu := by
      calc
        _ = (∫ x, mass x - (∑ i : Fin d, ∑ j : Fin d, grouped i j x) +
            (∑ j : Fin d, drift j x) + scalar x ∂mu) - ∫ x, source x ∂mu := by
          simpa only [Pi.sub_apply, Pi.add_apply] using
            integral_sub (((hmass.sub hgroupedSum).add hdriftSum).add hscalar) hsource
        _ = _ := by rw [e₃]
    rw [← hgroupedIntegral, ← hdriftIntegral, ← e₄]
    exact hraw
  have hweakSum :
      (∑ i : Fin d, ∑ j : Fin d, ∫ x, grouped i j x ∂mu) =
        -(∑ i : Fin d, ∑ j : Fin d, ∫ x, hessian i j x ∂mu) := by
    simp_rw [hweak]
    simp only [Finset.sum_neg_distrib]
  have hhessianIntegral :
      (∫ x, ∑ i : Fin d, ∑ j : Fin d, hessian i j x ∂mu) =
        ∑ i : Fin d, ∑ j : Fin d, ∫ x, hessian i j x ∂mu := by
    rw [integral_finset_sum Finset.univ (fun i _ =>
      integrable_finset_sum Finset.univ fun j _ => hhessian i j)]
    simp_rw [integral_finset_sum Finset.univ (fun j _ => hhessian _ j)]
  have hright :
      (∫ x, (∑ i : Fin d, ∑ j : Fin d, hessian i j x) +
          (∑ j : Fin d, drift j x) + scalar x - source x ∂mu) =
        ((∑ i : Fin d, ∑ j : Fin d, ∫ x, hessian i j x ∂mu) +
          (∑ j : Fin d, ∫ x, drift j x ∂mu) + ∫ x, scalar x ∂mu) -
          ∫ x, source x ∂mu := by
    calc
      _ = (∫ x, (∑ i : Fin d, ∑ j : Fin d, hessian i j x) +
          (∑ j : Fin d, drift j x) + scalar x ∂mu) - ∫ x, source x ∂mu := by
        simpa only [Pi.sub_apply, Pi.add_apply] using
          integral_sub ((hhessianSum.add hdriftSum).add hscalar) hsource
      _ = (((∫ x, ∑ i : Fin d, ∑ j : Fin d, hessian i j x ∂mu) +
          ∫ x, ∑ j : Fin d, drift j x ∂mu) + ∫ x, scalar x ∂mu) -
          ∫ x, source x ∂mu := by
        rw [show (∫ x, (∑ i : Fin d, ∑ j : Fin d, hessian i j x) +
            (∑ j : Fin d, drift j x) + scalar x ∂mu) =
            (∫ x, (∑ i : Fin d, ∑ j : Fin d, hessian i j x) +
              (∑ j : Fin d, drift j x) ∂mu) + ∫ x, scalar x ∂mu from by
              simpa only [Pi.add_apply] using integral_add (hhessianSum.add hdriftSum) hscalar]
        rw [show (∫ x, (∑ i : Fin d, ∑ j : Fin d, hessian i j x) +
            (∑ j : Fin d, drift j x) ∂mu) =
            (∫ x, ∑ i : Fin d, ∑ j : Fin d, hessian i j x ∂mu) +
              ∫ x, ∑ j : Fin d, drift j x ∂mu from by
                simpa only [Pi.add_apply] using integral_add hhessianSum hdriftSum]
      _ = _ := by rw [hhessianIntegral, hdriftIntegral]
  rw [hright]
  rw [hweakSum] at hraw'
  linarith

end HypoellipticAleksandrov.Parabolic.Dirichlet
