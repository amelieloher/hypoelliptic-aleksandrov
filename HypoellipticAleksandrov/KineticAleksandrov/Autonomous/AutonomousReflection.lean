module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SmoothABP
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.SmoothEstimateReflection
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelSource

/-! # Reflection of the conditional smooth autonomous estimate -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Parabolic TheoremA

/-- The backward smooth estimate retains the positive-set source and the same constant. -/
theorem autonomous_smooth_localised_of_below_four_density
    (hdensity : BelowFourDensityStatement)
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) (p : ℝ)
    (hp : criticalP ⟨Lam / lam, (le_div_iff₀ hlam).2
      (by simpa only [one_mul] using hLam)⟩ < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam)
      (P₀ : Point) (R : ℝ), 0 < R → ∀ (u f : Point → ℝ),
      ContinuousOn u (closure (backwardCylinder P₀ R)) →
      IsKineticC112On u (backwardCylinder P₀ R) →
      MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
        (volume.restrict (backwardCylinder P₀ R)) →
      (∀ᵐ P ∂volume.restrict (backwardCylinder P₀ R),
        autonomousScalarOperator A.a u P ≤ f P) →
      ∀ P ∈ closure (backwardCylinder P₀ R), u P ≤
        sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) +
          C * R ^ (2 - 6 / p) *
            (eLpNorm ({P | 0 < u P}.indicator (fun P => max (f P) 0))
              (ENNReal.ofReal p) (volume.restrict (backwardCylinder P₀ R))).toReal := by
  obtain ⟨C, hC, hforward⟩ := forward_autonomous_abp_of_below_four_density hdensity
    hH hLE lam Lam hlam hLam p hp
  refine ⟨C, hC, ?_⟩
  intro A P₀ R hR u f hcont hreg hLp hsub P hP
  let B : SmoothAutonomous lam Lam :=
    ⟨reflectedAutonomous A.a, reflectedAutonomous_smooth A, reflectedAutonomous_bounds A⟩
  let Z₀ := kineticReflection P₀
  let Q := forwardCylinder Z₀ R hR
  let U := u ∘ kineticReflection
  let g := (fun P => max (f P) 0) ∘ kineticReflection
  have hmp := measurePreserving_reflection_forward P₀ R hR
  have hUc : ContinuousOn U (closure Q) := by
    have hc := hcont.comp (continuous_kineticReflection 1).continuousOn
      (fun x hx => hx : MapsTo kineticReflection
        (kineticReflection ⁻¹' closure (backwardCylinder P₀ R)) _)
    simpa only [preimage_closure_backwardCylinder_reflection P₀ R hR] using hc
  have hUr : IsKineticC112On U Q := by
    simpa only [preimage_backwardCylinder_reflection P₀ R hR] using
      isKineticC112On_kineticReflection u (backwardCylinder P₀ R) hreg
  have hgLp : MemLp g (ENNReal.ofReal p) (volume.restrict Q) :=
    hLp.comp_measurePreserving hmp
  have hUs : ∀ᵐ P ∂volume.restrict Q, -g P ≤ forwardScalarOperator B.a U P := by
    filter_upwards [hmp.quasiMeasurePreserving.ae hsub] with P hP
    rw [autonomousScalarOperator_reflection]
    exact neg_le_neg (hP.trans (le_max_left _ _))
  have hbound := hforward B Z₀ R hR U g hUc hUr (fun _ _ => le_max_right _ _) hgLp hUs
  have hPr : kineticReflection P ∈ closure Q := by
    rw [← preimage_closure_backwardCylinder_reflection P₀ R hR]
    change kineticReflection (kineticReflection P) ∈ closure (backwardCylinder P₀ R)
    rw [kineticReflection_involutive P]
    exact hP
  have hresult := hbound (kineticReflection P) hPr
  have hnorm : eLpNorm ({P | 0 < U P}.indicator g) (ENNReal.ofReal p)
      (volume.restrict Q) =
      eLpNorm ({P | 0 < u P}.indicator (fun P => max (f P) 0)) (ENNReal.ofReal p)
        (volume.restrict (backwardCylinder P₀ R)) := by
    have hL := borelSource_memLp (isOpen_backwardCylinder P₀ R hR) true u f
      hreg.continuousOn hLp
    change MemLp ({P | 0 < u P}.indicator (fun P => max (f P) 0)) _ _ at hL
    have hfun : {P | 0 < U P}.indicator g =
        ({P | 0 < u P}.indicator (fun P => max (f P) 0)) ∘ kineticReflection := rfl
    rw [hfun]
    exact eLpNorm_comp_measurePreserving hL.aestronglyMeasurable hmp
  rw [hnorm, boundarySup_reflection P₀ R hR u] at hresult
  simpa only [U, Function.comp_apply, kineticReflection_involutive P] using hresult

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
