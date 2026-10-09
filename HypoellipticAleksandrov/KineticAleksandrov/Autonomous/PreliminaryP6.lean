module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PreliminaryP6Reflection
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SmoothAutonomousP6Statement
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AutonomousAdmissibilitySource
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelSource
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonLinear
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonLinear
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonConstant
import HypoellipticAleksandrov.KineticAleksandrov.Holder.AffineGeometryTopology
import Mathlib.Tactic

/-! # Preliminary autonomous admissibility without return-time estimates -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Parabolic Holder Set MeasureTheory
open scoped ENNReal

/-- Smooth autonomous homogeneous solutions satisfy the preliminary exponent-six comparison. -/
theorem smoothAutonomousP6_of_entrance (hentrance : EntranceStatement)
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    SmoothAutonomousP6Statement lam Lam := by
  obtain ⟨C_A, hC, hestimate⟩ := preliminary_backward_abp_of_entrance hentrance
    hH hLE lam Lam hlam hLam
  refine ⟨C_A, hC, ?_⟩
  intro A O hO u hu heq
  have hsup (w : Point → ℝ) (hw : IsKineticC112On w O)
      (heqw : ∀ᵐ P ∂volume.restrict O, autonomousScalarOperator A.a w P = 0) :
      IsAdmissibleSupersolution (autonomousCoefficient A.a) O 6 C_A w := by
    refine ⟨hw.continuousOn, ?_⟩
    intro P₀ R hR hQ psi hpsi
    obtain ⟨U, _hU, hUQ, hps⟩ := smoothNear_regular hpsi
    have hQQ : backwardCylinder P₀ R ⊆ O := subset_closure.trans hQ
    have hpr := comparison_regular_mono hps (subset_closure.trans hUQ)
    have hwr := comparison_regular_mono hw hQQ
    have hneg := comparison_regular_const_mul hwr (-1)
    have hdiff : IsKineticC112On (fun P => psi P - w P) (backwardCylinder P₀ R) := by
      simpa only [neg_one_mul, sub_eq_add_neg] using comparison_regular_add hpr hneg
    have hop : ∀ᵐ P ∂volume.restrict (backwardCylinder P₀ R),
        autonomousScalarOperator A.a (fun Q => psi Q - w Q) P ≤
          autonomousScalarOperator A.a psi P := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hQQ heqw,
        ae_restrict_mem (isOpen_backwardCylinder P₀ R hR).measurableSet] with P he hP
      have hadd := autonomous_operator_add hpr hneg A.a hP
      have hmul := autonomous_operator_const_mul hwr (-1) A.a hP
      simp only [neg_one_mul, ← sub_eq_add_neg] at hadd hmul
      rw [hadd, hmul, he]
      simp only [neg_zero, add_zero, le_refl]
    obtain ⟨_hmeas, hLp⟩ := autonomous_test_source hlam
      A.smooth.continuous.measurable A.bounds P₀ R hR hpsi
    have hn : {P | 0 < psi P - w P} = {P | w P < psi P} := by
      ext P
      exact sub_pos
    have hbnd := hestimate A P₀ R hR (fun P => psi P - w P)
      (autonomousScalarOperator A.a psi)
      (hpsi.continuousOn.sub (hw.continuousOn.mono hQ)) hdiff hLp hop
    have hbnd' : ∀ P ∈ closure (backwardCylinder P₀ R), psi P - w P ≤
        sSup ((fun P => max (psi P - w P) 0) '' kineticBoundary P₀ R) +
          C_A * R ^ (2 - (4 * (1 : ℝ) + 2) / 6) *
            (eLpNorm (localizedSource (autonomousCoefficient A.a) psi w) (ENNReal.ofReal 6)
              (volume.restrict (backwardCylinder P₀ R))).toReal := by
      simpa only [hn, localizedSource, backwardOperator_autonomous,
        show 4 * (1 : ℝ) + 2 = 6 by norm_num] using hbnd
    apply csSup_le
    · exact (backwardCylinder_nonempty P₀ hR).closure.image _
    · rintro y ⟨P, hP, rfl⟩
      simpa only [Nat.cast_one] using hbnd' P hP
  refine ⟨hsup u hu heq, ?_⟩
  have hneg : IsKineticC112On (fun P => -u P) O := by
    simpa only [neg_one_mul] using comparison_regular_const_mul hu (-1)
  apply hsup (fun P => -u P) hneg
  filter_upwards [heq, ae_restrict_mem hO.measurableSet] with P he hP
  have hm := autonomous_operator_const_mul hu (-1) A.a hP
  simpa only [neg_one_mul, he, neg_zero] using hm

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
