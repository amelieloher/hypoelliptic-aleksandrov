module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.MinorantMassComparison
import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.UniquenessMeasure
import Mathlib.Tactic.Positivity

/-!
# Uniform lower mass for the common minorant

A smooth terminal cutoff and the stationary polynomial comparison give a
positive mass independent of the center, radius, terminal time and coefficients.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Decay

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set MeasureTheory
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped MatrixOrder

/-- Uniform mass bound at one parabolic radius before the terminal time. -/
theorem minorant_mass_floor (d : ℕ) (hd : 1 ≤ d)
    (lam Lam : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam) :
    ∃ Cstar q0 : ℝ, 0 < Cstar ∧ q0 = Real.exp (-Cstar / 9) ∧ 0 < q0 ∧
      ∀ (B : CoefficientField d), IsSectionTwoCoefficient lam Lam B →
      ∀ (v0 : PDE.Vec d) (ρ T R : ℝ), 0 < ρ → R = 4 * ρ →
      ∀ (K : MovingFiberKernel (PDE.euclideanBall v0 R) stationary),
        HasParabolicMarginalBundle (PDE.euclideanBall v0 R) stationary
          (PDE.isOpen_euclideanBall v0 R).measurableSet
          (zIndependentCoefficient B) K →
      ∀ (qlate : ParabolicEvolutionQuery (PDE.euclideanBall v0 R) stationary),
        qlate.1 = (T - ρ ^ 2, T, v0) →
        ENNReal.ofReal q0 ≤
          P K (PDE.isOpen_euclideanBall v0 R).measurableSet qlate
            (PDE.euclideanBall v0 R) := by
  obtain ⟨N, hN, _hchoice, hc⟩ := exists_retention_barrier_order d hd lam Lam hlam hlamLam
  let Cstar : ℝ := 2 * N * d * Lam
  have hLam : 0 < Lam := hlam.trans_le hlamLam
  have hNp : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hdp : 0 < (d : ℝ) := by exact_mod_cast hd
  have hC : 0 < Cstar := by dsimp [Cstar]; positivity
  refine ⟨Cstar, Real.exp (-Cstar / 9), hC, rfl, Real.exp_pos _, ?_⟩
  intro B hB v0 ρ T R hρ hR K hpar qlate hql
  subst R
  have hΩ := PDE.isOpen_euclideanBall v0 (4 * ρ)
  have hcompact := PDE.isCompact_euclideanClosedBall v0 (by positivity : 0 ≤ 3 * ρ)
  have hsub : PDE.euclideanClosedBall v0 (3 * ρ) ⊆ PDE.euclideanBall v0 (4 * ρ) :=
    PDE.euclideanClosedBall_subset_euclideanBall (by positivity) (by linarith)
  obtain ⟨φ, hφ, hφc, hφsupp, hφbound, hφone⟩ :=
    exists_smooth_cutoff hcompact hΩ hsub
  obtain ⟨V, hV, -, hVeval⟩ := exists_scalar_probe hΩ.measurableSet B K hpar
    φ hφ hφc hφsupp T
  let φ' : PDE.Vec d → ℝ := fun y => φ (parabolicAffine v0 ρ y)
  have hφ' : ContDiff ℝ (⊤ : ℕ∞) φ' := hφ.comp (contDiff_parabolicAffine v0 ρ)
  have hc' : HasCompactSupport φ' := hφc.comp_homeomorph (parabolicAffineHomeo v0 hρ)
  have hV0 : ParabolicProbe.IsClassicalScalarTerminalSolution
      (PDE.euclideanBall v0 (4 * ρ)) stationary (zIndependentCoefficient B)
      (T + ρ ^ 2 * 0) (smoothTestBorel φ hφ.continuous hφc) V := by
    simpa only [mul_zero, add_zero] using hV
  have hW := isClassicalScalarTerminalSolution_comp_minorantAffine hΩ B T v0 hρ
    (parabolicAffine_preimage_ball v0 hρ).symm 0
    (smoothTestBorel φ hφ.continuous hφc) (smoothTestBorel φ' hφ'.continuous hc')
    (fun _ => rfl) hV0
  have hdom : ∀ y : PDE.Vec d, barrier N 3 y ≤
      smoothTestBorel φ' hφ'.continuous hc' y := by
    intro y
    change barrier N 3 y ≤ φ (parabolicAffine v0 ρ y)
    by_cases hy : y ∈ PDE.euclideanBall 0 3
    · have hyc : parabolicAffine v0 ρ y ∈ PDE.euclideanClosedBall v0 (3 * ρ) := by
        change PDE.euclideanSqDist (v0 + ρ • y) v0 ≤ (3 * ρ) ^ 2
        rw [add_comm, PDE.euclideanSqDist_affine_center]
        change PDE.vecNormSq (y - 0) < 3 ^ 2 at hy
        rw [sub_zero] at hy
        simp only [PDE.euclideanSqDist, sub_zero]
        nlinarith [sq_pos_of_pos hρ]
      rw [hφone _ hyc]
      exact ((retention_polynomial_barrier (d := d) hN 3 (by norm_num)).2.1 y).2
    · rw [((retention_polynomial_barrier hN 3 (by norm_num)).2.2.2.2 y hy).1]
      exact (hφbound _).1
  have hfloor := minorant_scalar_barrier_floor hN lam Lam hlam hlamLam hc
    (normalizedParabolicCoefficient B T ρ v0)
    (normalizedParabolicCoefficient_sectionTwo lam Lam B hB T v0 ρ hρ)
    _ _ hW hdom
  have hpoint : minorantAffine T ρ v0 (-1, 0) = (T - ρ ^ 2, v0) := by
    simp [minorantAffine, scalarAffine, sub_eq_add_neg]
  change Real.exp (-Cstar / 9) ≤ V (minorantAffine T ρ v0 (-1, 0)) at hfloor
  rw [hpoint] at hfloor
  have hv0 : v0 ∈ movingDomain (PDE.euclideanBall v0 (4 * ρ)) stationary (T - ρ ^ 2) := by
    rw [movingDomain_stationary]
    change PDE.vecNormSq (v0 - v0) < (4 * ρ) ^ 2
    simp only [sub_self]
    simpa [PDE.vecNormSq, PDE.vecDot] using
      sq_pos_of_pos (show 0 < 4 * ρ by positivity)
  have heval := hVeval (T - ρ ^ 2) (by nlinarith [sq_nonneg ρ]) v0 hv0
  have hq : scalarQuery (T - ρ ^ 2) T (by nlinarith [sq_nonneg ρ]) v0 hv0 = qlate :=
    Subtype.ext hql.symm
  rw [hq] at heval
  rw [heval] at hfloor
  have hint := integral_le_measure (μ := P K hΩ.measurableSet qlate)
    (s := univ) (f := φ) (fun y _ => (hφbound y).2)
    (fun y hy => (hy (mem_univ y)).elim)
  have hmass : P K hΩ.measurableSet qlate univ =
      P K hΩ.measurableSet qlate (PDE.euclideanBall v0 (4 * ρ)) := by
    rw [← measure_add_measure_compl hΩ.measurableSet,
      P_compl_eq_zero_stationary, add_zero]
  exact (ENNReal.ofReal_le_ofReal hfloor).trans (hint.trans_eq hmass)

/-- The exact source normalized mass floor, with its uniformly chosen constant. -/
theorem normalized_minorant_mass_floor (d : ℕ) (hd : 1 ≤ d)
    (lam Lam : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam) :
    ∃ Cstar q0 : ℝ, 0 < Cstar ∧ q0 = Real.exp (-Cstar / 9) ∧ 0 < q0 ∧
      ∀ (m Lb : ℝ) (D : Set (PDE.Vec d)) (B : CoefficientField d)
        (b : PDE.Vec d → PDE.Vec d), SourceSetting lam Lam m Lb D B b →
      ∀ (T : ℝ), (0 : PDE.Vec d) ∈ D →
        PDE.euclideanBall (0 : PDE.Vec d) 4 ⊆ D →
      ∀ (S : TerminalOperatorFamily (PDE.euclideanBall (0 : PDE.Vec d) 4) stationary)
        (K : MovingFiberKernel (PDE.euclideanBall (0 : PDE.Vec d) 4) stationary),
        RealizesTerminalEvolution (PDE.euclideanBall (0 : PDE.Vec d) 4) stationary
          (PDE.isOpen_euclideanBall (0 : PDE.Vec d) 4).measurableSet
          (zIndependentCoefficient B) b S K →
        HasParabolicMarginalBundle (PDE.euclideanBall (0 : PDE.Vec d) 4) stationary
          (PDE.isOpen_euclideanBall (0 : PDE.Vec d) 4).measurableSet
          (zIndependentCoefficient B) K →
        IsDomainMonotoneEvolution (PDE.euclideanBall (0 : PDE.Vec d) 4) stationary
          (zIndependentCoefficient B) b K →
      ∀ (qlate : ParabolicEvolutionQuery (PDE.euclideanBall (0 : PDE.Vec d) 4) stationary),
        qlate.1 = (T - 1, T, 0) →
        ENNReal.ofReal q0 ≤
          P K (PDE.isOpen_euclideanBall 0 4).measurableSet qlate (PDE.euclideanBall 0 4) := by
  obtain ⟨C, q, hC, hq, hqpos, hmass⟩ := minorant_mass_floor d hd lam Lam hlam hlamLam
  refine ⟨C, q, hC, hq, hqpos, ?_⟩
  intro m Lb D B b hset T h0 hsub S K hreal hpar hmono qlate hql
  have _ := And.intro h0 (And.intro hsub (And.intro hreal hmono))
  have h := hmass B hset.1 0 1 T 4 (by norm_num) (by norm_num)
    K hpar qlate (by simpa only [one_pow] using hql)
  exact h

end HypoellipticAleksandrov.KineticAleksandrov.Decay
