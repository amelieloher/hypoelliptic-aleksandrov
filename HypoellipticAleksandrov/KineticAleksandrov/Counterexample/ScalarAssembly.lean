module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarConstruction
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarPositionWeak
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarVelocityWeak
import Mathlib.Tactic

/-!
# Full Appendix C scalar profile

The literal Kummer construction satisfies the complete native one-dimensional interface.
The connection and differentiated tail estimates are proved upstream; no analytic package
is assumed by the exported existence theorem.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open MeasureTheory Set

/-- The actual Appendix C scalar profile satisfies the complete branch interface. -/
theorem counterProfileOne_exists (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1) :
    CounterProfileOneStatement alpha := by
  let gamma : ScalarGamma := ⟨alpha / 3, by constructor <;> linarith⟩
  have hga : 3 * gamma.1 = alpha := by dsimp only [gamma]; ring
  obtain ⟨Lam, hLam, hmatch⟩ := exists_matching_ratio gamma.1 gamma.2.1 gamma.2.2
  have hp : 0 < Lam := lt_trans zero_lt_one hLam
  obtain ⟨c, C0, hc, hcC, hcomp⟩ := scalarProfile_comparison gamma Lam hp hmatch
  obtain ⟨Cg, hCg, hgrad⟩ := scalarGv_gauge_bound gamma Lam hp hmatch
  let C : ℝ := max C0 Cg
  have hC0 : C0 ≤ C := le_max_left _ _
  have hCgC : Cg ≤ C := le_max_right _ _
  refine ⟨Lam, c, C, scalarProfile gamma Lam, scalarGx gamma Lam, scalarGv gamma Lam,
    scalarHess gamma Lam, hLam, hc, hCg.trans_le hCgC,
    scalarProfile_continuous gamma Lam hp hmatch, scalarProfile_zero gamma Lam, ?_, ?_,
    measurable_scalarGx gamma Lam, measurable_scalarGv gamma Lam,
    measurable_scalarHess gamma Lam, scalarJets_eq_ae gamma Lam,
    scalarJets_equation_ae gamma Lam hp, ?_, scalarJets_compact_bound gamma Lam hp hmatch,
    ?_, ?_, ?_⟩
  · intro r hr q
    simpa only [hga] using scalarProfile_homogeneous gamma Lam r hr q
  · intro q
    have hh := hcomp q
    rw [hga] at hh
    exact ⟨hh.1, hh.2.trans (mul_le_mul_of_nonneg_right hC0
      (Real.rpow_nonneg (rho_nonneg q) alpha))⟩
  · intro q hq
    have hh := hgrad q hq
    rw [hga] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hCgC
      (Real.rpow_nonneg (rho_nonneg q) (alpha - 1)))
  · intro r hr q
    simpa only [hga] using And.intro (scalarGx_homogeneous gamma Lam r hp hr q)
      (And.intro (scalarGv_homogeneous gamma Lam r hp hr q)
        (scalarHess_homogeneous gamma Lam r hp hr q))
  · intro test ht hs _hz
    refine ⟨?_, ?_, ?_⟩
    · intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact scalarProfile_position_weak gamma Lam hp hmatch test
        (ht.of_le (by norm_num)) hs
    · intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact scalarProfile_velocity_weak gamma Lam hp hmatch test
        (ht.of_le (by norm_num)) hs
    · intro i k
      have hi : i = 0 := Subsingleton.elim _ _
      have hk : k = 0 := Subsingleton.elim _ _
      subst i
      subst k
      exact scalarProfile_hessian_weak gamma Lam hp hmatch test ht hs
  · intro q hq
    exact (scalarProfile_contDiffAt_off_axis gamma Lam hp q hq).contDiffWithinAt

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
