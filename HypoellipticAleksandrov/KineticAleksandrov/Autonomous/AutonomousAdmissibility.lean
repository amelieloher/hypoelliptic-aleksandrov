module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.LocalisedAutonomous
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AutonomousAdmissibilitySource
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Setting
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonLinear
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonLinear
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonConstant
import HypoellipticAleksandrov.KineticAleksandrov.Holder.AffineGeometryTopology
import Mathlib.Tactic

/-! # Uniform autonomous admissibility at exponent six -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov Parabolic Autonomous Holder Set MeasureTheory
open scoped ENNReal

/-- The localized autonomous estimate gives a uniform admissibility constant before all
coefficient, domain and solution data, conditional on the exact density assertion. -/
theorem autonomous_admissibility_of_below_four_density
    (hdensity : Autonomous.BelowFourDensityStatement)
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ C_A : ℝ,
      ∀ a : ℝ → ℝ → ℝ,
        Measurable (Function.uncurry a) →
        (∀ x v : ℝ, lam ≤ a x v ∧ a x v ≤ Lam) →
      ∀ Omega : Set (KineticPoint 1), IsOpen Omega →
      ∀ u : KineticPoint 1 → ℝ,
        (∃ M : ℝ, ∀ P ∈ Omega, |u P| ≤ M) →
        Parabolic.IsKineticC112On u Omega →
        (∀ᵐ P ∂(volume.restrict Omega), autonomousScalarOperator a u P = 0) →
        IsAdmissibleSolution
          (fun _ x v => fun _ _ => a (x 0) (v 0)) Omega 6 C_A u := by
  have hp : 1 + bellmanAdjointExponent (Lam / lam)
      ((le_div_iff₀ hlam).2 (by simpa only [one_mul] using hLam)) < 6 := by
    have hc := (criticalP_bounds ⟨Lam / lam, (le_div_iff₀ hlam).2
      (by simpa only [one_mul] using hLam)⟩).2
    change 1 + bellmanAdjointExponent _ _ < 4 at hc
    linarith only [hc]
  obtain ⟨C_A, _hC, hestimate⟩ :=
    kinetic_aleksandrov_autonomous_localised_relative_of_below_four_density
      hdensity hH hLE lam Lam 6 hlam hLam hp
  refine ⟨C_A, ?_⟩
  intro a ha hb Omega _hOmega u _hbounded hu heq
  have hsup (w : Point → ℝ) (hw : IsKineticC112On w Omega)
      (heqw : ∀ᵐ P ∂volume.restrict Omega, autonomousScalarOperator a w P = 0) :
      IsAdmissibleSupersolution (autonomousCoefficient a) Omega 6 C_A w := by
    refine ⟨hw.continuousOn, ?_⟩
    intro P₀ R hR hQ psi hpsi
    obtain ⟨U, _hU, hUQ, hps⟩ := smoothNear_regular hpsi
    have hQQ : backwardCylinder P₀ R ⊆ Omega := subset_closure.trans hQ
    have hpr := comparison_regular_mono hps (subset_closure.trans hUQ)
    have hwr := comparison_regular_mono hw hQQ
    have hneg := comparison_regular_const_mul hwr (-1)
    have hdiff : IsKineticC112On (fun P => psi P - w P) (backwardCylinder P₀ R) := by
      simpa only [neg_one_mul, sub_eq_add_neg] using comparison_regular_add hpr hneg
    have hop : ∀ᵐ P ∂volume.restrict (backwardCylinder P₀ R),
        autonomousScalarOperator a (fun Q => psi Q - w Q) P ≤
          autonomousScalarOperator a psi P := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hQQ heqw,
        ae_restrict_mem (isOpen_backwardCylinder P₀ R hR).measurableSet] with P he hP
      have hadd := autonomous_operator_add hpr hneg a hP
      have hmul := autonomous_operator_const_mul hwr (-1) a hP
      simp only [neg_one_mul, ← sub_eq_add_neg] at hadd hmul
      rw [hadd, hmul, he]
      simp only [neg_zero, add_zero, le_refl]
    obtain ⟨hmeas, hLp⟩ := autonomous_test_source hlam ha hb P₀ R hR hpsi
    have hn : {P | 0 < psi P - w P} = {P | w P < psi P} := by
      ext P
      exact sub_pos
    have hbnd := hestimate P₀ R hR a ha hb (autonomousScalarOperator a psi)
      (fun P => psi P - w P) hmeas
      (hpsi.continuousOn.sub (hw.continuousOn.mono hQ)) hdiff hop hLp
    have hbnd' : ∀ P ∈ closure (backwardCylinder P₀ R), psi P - w P ≤
        sSup ((fun P => max (psi P - w P) 0) '' kineticBoundary P₀ R) +
          C_A * R ^ (2 - (4 * (1 : ℝ) + 2) / 6) *
            (eLpNorm (localizedSource (autonomousCoefficient a) psi w) (ENNReal.ofReal 6)
              (volume.restrict (backwardCylinder P₀ R))).toReal := by
      simpa only [hn, localizedSource, backwardOperator_autonomous,
        show 4 * (1 : ℝ) + 2 = 6 by norm_num] using hbnd
    apply csSup_le
    · exact (backwardCylinder_nonempty P₀ hR).closure.image _
    · rintro y ⟨P, hP, rfl⟩
      simpa only [Nat.cast_one] using hbnd' P hP
  refine ⟨hsup u hu heq, ?_⟩
  have hneg : IsKineticC112On (fun P => -u P) Omega := by
    simpa only [neg_one_mul] using comparison_regular_const_mul hu (-1)
  apply hsup (fun P => -u P) hneg
  filter_upwards [heq, ae_restrict_mem _hOmega.measurableSet] with P he hP
  have hm := autonomous_operator_const_mul hu (-1) a hP
  simpa only [neg_one_mul, he, neg_zero] using hm

end HypoellipticAleksandrov.KineticAleksandrov
