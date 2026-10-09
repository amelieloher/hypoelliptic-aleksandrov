module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Borel.SmoothInner
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelBoundary

/-!
# The smooth-to-Borel passage for full coefficients

The passage from smooth to Borel coefficients, localized form. The estimate for
smooth full coefficients with everywhere bounds implies the estimate for Borel symmetric
coefficients `A(t,x,v)` with `λ I ≤ A ≤ Λ I` almost everywhere, with the same constant.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

open HypoellipticAleksandrov.Parabolic MeasureTheory Set
open scoped MatrixOrder ENNReal

/-- The passage from smooth to Borel coefficients: the smooth estimate passes to Borel full
coefficients. -/
theorem full_abp_smooth_to_borel {d : ℕ} (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (p : ℝ) (hp : 1 ≤ p) (alpha C₀ : ℝ)
    (hsmooth : FullSmoothEstimate (d := d) lam Lam p alpha C₀)
    (A : FullKineticCoefficient d) (hBorel : Measurable (fullKineticCoefficientAt A))
    (hsymm : ∀ P : KineticPoint d, (fullKineticCoefficientAt A P).IsSymm)
    (hlo : ∀ᵐ P ∂(volume : Measure (KineticPoint d)),
      lam • (1 : PDE.Mat d) ≤ fullKineticCoefficientAt A P)
    (hhi : ∀ᵐ P ∂(volume : Measure (KineticPoint d)),
      fullKineticCoefficientAt A P ≤ Lam • (1 : PDE.Mat d))
    (P₀ : KineticPoint d) (R : ℝ) (hR : 0 < R) (u f : KineticPoint d → ℝ)
    (hcont : ContinuousOn u (closure (backwardCylinder P₀ R)))
    (hreg : IsKineticC112On u (backwardCylinder P₀ R))
    (hf : Measurable (fun P : backwardCylinder P₀ R => f P))
    (hLp : MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
      (volume.restrict (backwardCylinder P₀ R)))
    (hsub : ∀ᵐ P ∂(volume.restrict (backwardCylinder P₀ R)), backwardOperator A u P ≤ f P) :
    ∀ P ∈ closure (backwardCylinder P₀ R), u P ≤
      sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) + C₀ * R ^ alpha *
      (eLpNorm (borelSource true u f) (ENNReal.ofReal p)
        (volume.restrict (backwardCylinder P₀ R))).toReal := by
  obtain ⟨C, hC, hc⟩ := full_coefficient_approximation lam Lam hlam hLam A hBorel hsymm hlo hhi
  apply borel_boundary_limit p hp alpha C₀ true P₀ R hR u f hcont hLp
  intro n P hP
  have hk := isCompact_closure_reflected_innerCylinder P₀ R hR (borelInnerDelta R n)
    (borelInnerDelta_valid R hR n).1 (borelInnerDelta_valid R hR n).2
  have hKD := closure_reflected_innerCylinder_subset P₀ R hR (borelInnerDelta R n)
    (borelInnerDelta_valid R hR n).1 (borelInnerDelta_valid R hR n).2
  rw [kineticReflection_image_innerCylinder] at hk hKD
  have hμ := Measure.restrict_mono_set volume (subset_closure.trans hKD)
  have hfn : Measurable (fun P : backwardCylinder (borelInnerCentre P₀ R n)
      (borelInnerRadius R hR n) => f P) :=
    hf.comp (measurable_inclusion (subset_closure.trans hKD))
  exact full_smooth_inner_limit lam Lam hlam hLam p hp alpha C₀ hsmooth A hBorel hlo hhi C hC hc
    u f hreg (borelInnerCentre P₀ R n) (borelInnerRadius R hR n)
    (borelInnerRadius_pos R hR n) hk hKD hfn (hLp.mono_measure hμ)
    (hsub.filter_mono (ae_mono hμ)) P hP

/-- Target A4: the localized Aleksandrov estimate for Borel full coefficients follows from the
estimate for smooth full coefficients with everywhere bounds, with the same constant. -/
theorem kinetic_aleksandrov_fullCoefficient_of_smooth
    (d : ℕ) (_hd : 1 ≤ d) (lam Lam p : ℝ)
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (hp : 1 ≤ p)
    (hsmooth : ∃ C : ℝ, 0 ≤ C ∧
      ∀ (P₀ : KineticPoint d) (R : ℝ), 0 < R →
      ∀ (A : FullKineticCoefficient d),
        IsSmoothFullKineticCoefficient A →
        (∀ P : KineticPoint d, (fullKineticCoefficientAt A P).IsSymm) →
        (∀ P : KineticPoint d, lam • (1 : PDE.Mat d) ≤ fullKineticCoefficientAt A P ∧
          fullKineticCoefficientAt A P ≤ Lam • (1 : PDE.Mat d)) →
      ∀ (f u : KineticPoint d → ℝ),
        Measurable (fun P : backwardCylinder P₀ R => f P) →
        ContinuousOn u (closure (backwardCylinder P₀ R)) →
        Parabolic.IsKineticC112On u (backwardCylinder P₀ R) →
        (∀ᵐ P ∂(volume.restrict (backwardCylinder P₀ R)), backwardOperator A u P ≤ f P) →
        MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
          (volume.restrict (backwardCylinder P₀ R)) →
        ∀ P ∈ closure (backwardCylinder P₀ R),
          u P ≤ sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) +
            C * R ^ (2 - (4 * (d : ℝ) + 2) / p) *
              (eLpNorm ({P | 0 < u P}.indicator (fun P => max (f P) 0)) (ENNReal.ofReal p)
                (volume.restrict (backwardCylinder P₀ R))).toReal) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (P₀ : KineticPoint d) (R : ℝ), 0 < R →
      ∀ (A : FullKineticCoefficient d),
        Measurable (fullKineticCoefficientAt A) →
        (∀ P : KineticPoint d, (fullKineticCoefficientAt A P).IsSymm) →
        (∀ᵐ P ∂(volume : Measure (KineticPoint d)),
          lam • (1 : PDE.Mat d) ≤ fullKineticCoefficientAt A P) →
        (∀ᵐ P ∂(volume : Measure (KineticPoint d)),
          fullKineticCoefficientAt A P ≤ Lam • (1 : PDE.Mat d)) →
      ∀ (f u : KineticPoint d → ℝ),
        Measurable (fun P : backwardCylinder P₀ R => f P) →
        ContinuousOn u (closure (backwardCylinder P₀ R)) →
        Parabolic.IsKineticC112On u (backwardCylinder P₀ R) →
        (∀ᵐ P ∂(volume.restrict (backwardCylinder P₀ R)),
          backwardOperator A u P ≤ f P) →
        MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
          (volume.restrict (backwardCylinder P₀ R)) →
        ∀ P ∈ closure (backwardCylinder P₀ R),
          u P ≤ sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) +
            C * R ^ (2 - (4 * (d : ℝ) + 2) / p) *
              (eLpNorm ({P | 0 < u P}.indicator (fun P => max (f P) 0)) (ENNReal.ofReal p)
                (volume.restrict (backwardCylinder P₀ R))).toReal := by
  obtain ⟨C, hC0, hC⟩ := hsmooth
  refine ⟨C, hC0, ?_⟩
  intro P₀ R hR A hBorel hsymm hlo hhi f u hf hcont hreg hsub hLp
  exact full_abp_smooth_to_borel lam Lam hlam hLam p hp (2 - (4 * (d : ℝ) + 2) / p) C
    (fun P₀ R hR A hA hs hb f u hf hc hr hsub hLp => hC P₀ R hR A hA hs hb f u hf hc hr hsub hLp)
    A hBorel hsymm hlo hhi P₀ R hR u f hcont hreg hf hLp hsub

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
