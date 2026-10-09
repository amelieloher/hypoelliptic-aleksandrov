module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Energy.ByParts
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Energy.Triple
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Energy.SlicePointwise

/-!
# The energy inequality on a slice

The energy inequality: for a non-zero slice `τ`, multiply the smoothed
equation by `q ρ^{q-1} ζ` and integrate over `ℝ^{2d}`. The time term stays as the integral
`∫ ζ q ρ^{q-1} ∂_τ ρ`; the transport term vanishes; the diffusion terms are integrated by parts.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory Matrix
open scoped MatrixOrder

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ} {lam h q Bv ε : ℝ} {ρ dρ ζ : EvolutionAmbientState d → ℝ}
  {β J : EvolutionAmbientState d → PDE.Mat d}

/-- The hypotheses on a non-zero slice, in the form used by the slice energy inequality. -/
structure SliceHyp (lam h q Bv ε : ℝ) (ρ dρ ζ : EvolutionAmbientState d → ℝ)
    (β J : EvolutionAmbientState d → PDE.Mat d) : Prop where
  lam_pos : 0 < lam
  one_lt : 1 < q
  eps_nonneg : 0 ≤ ε
  smooth_rho : ContDiff ℝ (⊤ : ℕ∞) ρ
  pos : ∀ y, 0 < ρ y
  smooth_beta : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) fun y => β y i j
  flux_eq : ∀ i j y, J y i j = ρ y * β y i j
  loewner : ∀ y, lam • (1 : PDE.Mat d) ≤ β y
  equation : ∀ y, dρ y + transportDerivative ρ y =
    lam * h ^ 2 / 2 * positionLaplacian ρ y - lam * h * mixedDivergence ρ y +
      ∑ i, ∑ j, velocityPartial i (velocityPartial j (fun y => J y i j)) y
  integrable : SliceIntegrable q ρ β J
  smooth_cutoff : ContDiff ℝ (⊤ : ℕ∞) ζ
  cutoff_nonneg : ∀ y, 0 ≤ ζ y
  cutoff_le_one : ∀ y, ζ y ≤ 1
  cutoff_inr : ∀ i y, coordPartial (Sum.inr i) ζ y = 0
  cutoff_vel : ∀ i y, |y.1 i * ζ y| ≤ Bv
  cutoff_inl : ∀ i y, |coordPartial (Sum.inl i) ζ y| ≤ ε

namespace SliceHyp

variable (H : SliceHyp lam h q Bv ε ρ dρ ζ β J)

include H

theorem smooth_flux : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) fun y => J y i j := fun i j => by
  have : (fun y => J y i j) = fun y => ρ y * β y i j := funext (H.flux_eq i j)
  rw [this]
  exact H.smooth_rho.mul (H.smooth_beta i j)

theorem abs_cutoff_le (y : EvolutionAmbientState d) : |ζ y| ≤ 1 := by
  rw [abs_of_nonneg (H.cutoff_nonneg y)]
  exact H.cutoff_le_one y

theorem abs_cutoff_partial_le (c : Fin d ⊕ Fin d) (y : EvolutionAmbientState d) :
    |coordPartial c ζ y| ≤ ε := by
  rcases c with i | i
  · exact H.cutoff_inl i y
  · rw [H.cutoff_inr]; simpa using H.eps_nonneg

/-- The three integrability statements for each component of the flux field. -/
theorem flux_integrable (c : Fin d ⊕ Fin d) :
    Integrable (fun y => ρ y ^ (q - 1) * fluxField lam h ρ J c y) ∧
      Integrable (fun y => ρ y ^ (q - 2) * coordPartial c ρ y * fluxField lam h ρ J c y) ∧
      Integrable (fun y => ρ y ^ (q - 1) * coordPartial c (fluxField lam h ρ J c) y) := by
  have hF := contDiff_fluxField (lam := lam) (h := h) H.smooth_rho H.smooth_flux
  rcases c with i | i
  · exact H.integrable.triple H.smooth_rho H.pos (hF (Sum.inl i)) (Sum.inl i)
      (K1 := |lam * h / 2|) (K2 := d) (K3 := |lam * h / 2|) (K4 := d)
      (by positivity) (fun y => abs_fluxV_le i y)
      (fun y => abs_coordPartial_fluxV_le H.smooth_rho H.smooth_flux (Sum.inl i) i y)
  · exact H.integrable.triple H.smooth_rho H.pos (hF (Sum.inr i)) (Sum.inr i)
      (K1 := |lam * h ^ 2 / 2| + |lam * h / 2|) (K2 := 0)
      (K3 := |lam * h ^ 2 / 2| + |lam * h / 2|) (K4 := 0) le_rfl
      (fun y => (abs_gradFluxZ_le i y).trans (le_of_eq (by ring)))
      (fun y => (abs_coordPartial_gradFluxZ_le H.smooth_rho (Sum.inr i) i y).trans
        (le_of_eq (by ring)))

/-- The integration by parts identity, summed over the flux field. -/
theorem integral_flux_by_parts :
    ∫ y, ζ y * (q * ρ y ^ (q - 1) * dρ y) =
      -(q * ∑ c, ∫ y, coordPartial c ζ y * (ρ y ^ (q - 1) * fluxField lam h ρ J c y)) -
        q * (q - 1) * ∑ c, ∫ y, ζ y * (ρ y ^ (q - 2) * coordPartial c ρ y *
          fluxField lam h ρ J c y) := by
  have hρ := H.smooth_rho
  have hJs := H.smooth_flux
  have hF := contDiff_fluxField (lam := lam) (h := h) hρ hJs
  have hdiv : ∀ y, dρ y = ∑ c, coordPartial c (fluxField lam h ρ J c) y -
      transportDerivative ρ y := fun y => by
    have := H.equation y
    rw [← div_fluxField_eq lam h hρ hJs y] at this
    linarith
  have hpt : ∀ y, ζ y * (q * ρ y ^ (q - 1) * dρ y) =
      q * ∑ c, ζ y * (ρ y ^ (q - 1) * coordPartial c (fluxField lam h ρ J c) y) -
        ζ y * (q * ρ y ^ (q - 1) * transportDerivative ρ y) := fun y => by
    rw [hdiv y]
    simp only [← Finset.mul_sum]
    ring
  obtain ⟨htr_int, htr⟩ := integral_cutoff_transport_eq_zero (q := q) hρ H.pos H.smooth_cutoff
    H.cutoff_inr H.cutoff_vel H.integrable.pow (fun i => by
      have := (H.integrable.grad)
      refine integrable_of_abs_le (K := 1) ((((contDiff_rpow_of_pos hρ H.pos _).continuous).mul
        (continuous_coordPartial hρ (Sum.inr i))).aestronglyMeasurable) this fun y => ?_
      refine (abs_rpow_mul_le (H.pos y) (energy_abs_coordPartial_le_gradNorm (Sum.inr i) ρ y)).trans
        (le_of_eq (by ring)))
  have hint1 : Integrable fun y => q * ∑ c, ζ y *
      (ρ y ^ (q - 1) * coordPartial c (fluxField lam h ρ J c) y) :=
    (integrable_finsetSum _ fun c _ => integrable_cutoff_mul H.smooth_cutoff.continuous
      H.abs_cutoff_le (H.flux_integrable c).2.2).const_mul q
  have hA : ∀ c, ∫ y, ζ y * (ρ y ^ (q - 1) * coordPartial c (fluxField lam h ρ J c) y) =
      -(∫ y, coordPartial c ζ y * (ρ y ^ (q - 1) * fluxField lam h ρ J c y)) -
        (q - 1) * ∫ y, ζ y * (ρ y ^ (q - 2) * coordPartial c ρ y *
          fluxField lam h ρ J c y) := fun c =>
    integral_cutoff_rpow_mul_coordPartial hρ H.pos (hF c) H.smooth_cutoff (A := 1)
      H.abs_cutoff_le c (B := ε) (H.abs_cutoff_partial_le c) (H.flux_integrable c).1
      (H.flux_integrable c).2.1 (H.flux_integrable c).2.2
  simp_rw [hpt]
  rw [integral_sub hint1 htr_int, htr, integral_const_mul,
    integral_finsetSum _ fun c _ => integrable_cutoff_mul H.smooth_cutoff.continuous
      H.abs_cutoff_le (H.flux_integrable c).2.2]
  simp_rw [hA]
  rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum]
  ring

end SliceHyp

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
