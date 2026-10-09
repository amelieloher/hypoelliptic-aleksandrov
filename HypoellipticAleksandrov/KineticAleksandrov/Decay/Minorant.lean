module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.MinorantMass
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.MinorantChain
import Mathlib.Tactic.Positivity

/-!
# The common terminal minorant

Rescale the supplied scalar probe itself and apply the six-step Harnack theorem.
The mass floor uses the same original marginal kernel and uniform constants.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Decay

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set MeasureTheory
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped MatrixOrder

/-- The measure comparison after arbitrary parabolic translation and scaling. -/
theorem scaled_minorant_comparison (d : ℕ) (hd : 1 ≤ d)
    (lam Lam : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam) :
    ∃ h : ℝ, 0 < h ∧
      ∀ (B : CoefficientField d), IsSectionTwoCoefficient lam Lam B →
      ∀ (v0 : PDE.Vec d) (ρ T : ℝ), 0 < ρ →
      ∀ (K : MovingFiberKernel (PDE.euclideanBall v0 (4 * ρ)) stationary),
        HasParabolicMarginalBundle (PDE.euclideanBall v0 (4 * ρ)) stationary
          (PDE.isOpen_euclideanBall v0 (4 * ρ)).measurableSet
          (zIndependentCoefficient B) K →
      ∀ (qearly qlate : ParabolicEvolutionQuery (PDE.euclideanBall v0 (4 * ρ)) stationary),
        qearly.1 = (T - 4 * ρ ^ 2, T, qearly.1.2.2) →
        qlate.1 = (T - ρ ^ 2, T, v0) →
        qearly.1.2.2 ∈ PDE.euclideanBall v0 ρ →
        ENNReal.ofReal h • P K (PDE.isOpen_euclideanBall v0 (4 * ρ)).measurableSet qlate ≤
          P K (PDE.isOpen_euclideanBall v0 (4 * ρ)).measurableSet qearly := by
  obtain ⟨hf, hfpos, hfH⟩ := normalized_six_step_harnack d hd lam Lam hlam hlamLam
  refine ⟨hf ^ 6, pow_pos hfpos 6, ?_⟩
  intro B hB v0 ρ T hρ K hpar qearly qlate hqe hql hv
  have hΩo := PDE.isOpen_euclideanBall v0 (4 * ρ)
  rcases qearly with ⟨⟨σ, τ, y⟩, hστ, hy⟩
  rcases qlate with ⟨⟨σ', τ', y'⟩, hστ', hy'⟩
  dsimp only at hqe hql hv
  simp only [Prod.mk.injEq, and_true] at hqe hql
  obtain ⟨hσ, hτ⟩ := hqe
  obtain ⟨hσ', hτ', hy0⟩ := hql
  subst y'
  subst hσ hσ'
  have hT1 : T = τ := hτ.symm
  have hT2 : T = τ' := hτ'.symm
  subst hT1 hT2
  have hfin : IsFiniteMeasure (ENNReal.ofReal (hf ^ 6) •
      P K hΩo.measurableSet ⟨(T - ρ ^ 2, T, v0), hστ', hy'⟩) := by
    refine ⟨?_⟩
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  refine measure_le_of_smooth_integral_le hΩo ?_ ?_
  · rw [Measure.smul_apply, P_compl_eq_zero_stationary, smul_zero]
  · intro φ hφ hφc hφsupp h01
    obtain ⟨V, hV, -, hVeval⟩ := exists_scalar_probe hΩo.measurableSet B K hpar
      φ hφ hφc hφsupp T
    let φ' : PDE.Vec d → ℝ := fun w => φ (parabolicAffine v0 ρ w)
    have hφ' : ContDiff ℝ (⊤ : ℕ∞) φ' := hφ.comp (contDiff_parabolicAffine v0 ρ)
    have hc' : HasCompactSupport φ' := hφc.comp_homeomorph (parabolicAffineHomeo v0 hρ)
    have hV0 : ParabolicProbe.IsClassicalScalarTerminalSolution
        (PDE.euclideanBall v0 (4 * ρ)) stationary (zIndependentCoefficient B)
        (T + ρ ^ 2 * 0) (smoothTestBorel φ hφ.continuous hφc) V := by
      simpa only [mul_zero, add_zero] using hV
    let B' := normalizedParabolicCoefficient B T ρ v0
    let W : TimeVelocity d → ℝ := fun p => V (minorantAffine T ρ v0 p)
    have hW := isClassicalScalarTerminalSolution_comp_minorantAffine hΩo B T v0 hρ
      (parabolicAffine_preimage_ball v0 hρ).symm 0
      (smoothTestBorel φ hφ.continuous hφc) (smoothTestBorel φ' hφ'.continuous hc')
      (fun _ => rfl) hV0
    have hB' := normalizedParabolicCoefficient_sectionTwo lam Lam B hB T v0 ρ hρ
    have hcontB := continuous_coefficientAt_of_smooth hB'.2.2.1
    let w : PDE.Vec d := ρ⁻¹ • (y - v0)
    have hwpoint : parabolicAffine v0 ρ w = y := by
      simp [w, parabolicAffine, smul_smul, ne_of_gt hρ]
    have hw : w ∈ PDE.euclideanBall 0 1 := by
      change PDE.vecNormSq (w - 0) < 1 ^ 2
      simp only [sub_zero, one_pow]
      have heq : PDE.vecNormSq (y - v0) = ρ ^ 2 * PDE.vecNormSq w := by
        rw [← hwpoint]
        change PDE.euclideanSqDist (v0 + ρ • w) v0 = _
        rw [add_comm, PDE.euclideanSqDist_affine_center]
        simp only [PDE.euclideanSqDist, sub_zero]
      change PDE.vecNormSq (y - v0) < ρ ^ 2 at hv
      nlinarith [sq_pos_of_pos hρ]
    have hnonneg : IsNonnegativeOn (fun p => W (timeReversal 0 p))
        (Ioi (0 : ℝ) ×ˢ PDE.euclideanBall 0 4) := by
      intro p hp
      have hpball : parabolicAffine v0 ρ p.2 ∈ PDE.euclideanBall v0 (4 * ρ) := by
        rw [← parabolicAffine_preimage_ball v0 hρ] at hp
        exact hp.2
      have ht : T + ρ ^ 2 * (-p.1) ≤ T := by
        have hprod := mul_nonneg (sq_nonneg ρ) (show 0 ≤ p.1 from hp.1.le)
        nlinarith only [hprod]
      have heval := hVeval _ ht (parabolicAffine v0 ρ p.2)
        (by simpa only [movingDomain_stationary] using hpball)
      have he : timeReversal 0 p = (-p.1, p.2) := by
        simpa only [zero_sub] using timeReversal_apply 0 p.1 p.2
      change 0 ≤ W (timeReversal 0 p)
      rw [he]
      change 0 ≤ V (T + ρ ^ 2 * (-p.1), parabolicAffine v0 ρ p.2)
      rw [heval]
      exact integral_nonneg fun x => (h01 x).1
    have key := hfH (fun θ v => B' (0 + -1 * θ) (0 + (1 : ℝ) • v))
      (fun p => W (timeReversal 0 p))
      (hcontB.continuousOn.comp (contDiff_scalarAffine 0 (-1) 0 1).continuous.continuousOn
        (fun p _ => mem_univ _))
      (fun p _ => hB'.2.2.2.1 _ _)
      (fun p _ => hB'.2.2.2.2.1 _ _) (fun p _ => hB'.2.2.2.2.2 _ _)
      (timeReversed_isScalarC12On (PDE.isOpen_euclideanBall 0 4) hW)
      hnonneg (timeReversed_equation (PDE.isOpen_euclideanBall 0 4) hW) w hw
    have e1 : minorantAffine T ρ v0 (timeReversal 0 (1, 0)) =
        (T - ρ ^ 2, v0) := by
      simp [minorantAffine, scalarAffine, timeReversal, sub_eq_add_neg]
    have e4 : minorantAffine T ρ v0 (timeReversal 0 (4, w)) =
        (T - 4 * ρ ^ 2, y) := by
      rw [timeReversal_apply]
      simp only [zero_sub]
      change (T + ρ ^ 2 * (-4), parabolicAffine v0 ρ w) = _
      rw [hwpoint]
      congr 1
      ring
    change hf ^ 6 * V (minorantAffine T ρ v0 (timeReversal 0 (1, 0))) ≤
      V (minorantAffine T ρ v0 (timeReversal 0 (4, w))) at key
    rw [e1, e4] at key
    have hlate := hVeval (T - ρ ^ 2) hστ' v0 hy'
    have hearly := hVeval (T - 4 * ρ ^ 2) hστ y hy
    rw [integral_smul_measure, ENNReal.toReal_ofReal (pow_pos hfpos 6).le, smul_eq_mul]
    change hf ^ 6 * ∫ x, φ x ∂(P K hΩo.measurableSet
        (scalarQuery (T - ρ ^ 2) T hστ' v0 hy')) ≤
      ∫ x, φ x ∂(P K hΩo.measurableSet (scalarQuery (T - 4 * ρ ^ 2) T hστ y hy))
    rw [← hlate, ← hearly]
    exact key

/-- The source common terminal minorant for the same supplied marginal kernel. -/
theorem common_terminal_minorant (d : ℕ) (hd : 1 ≤ d)
    (lam Lam : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam) :
    ∃ h q0 : ℝ, 0 < h ∧ 0 < q0 ∧
      ∀ (m Lb : ℝ) (D : Set (PDE.Vec d)) (B : CoefficientField d)
        (b : PDE.Vec d → PDE.Vec d), SourceSetting lam Lam m Lb D B b →
      ∀ (v0 : PDE.Vec d) (ρ T : ℝ), v0 ∈ D → 0 < ρ →
        PDE.euclideanBall v0 (4 * ρ) ⊆ D →
      ∀ (S : TerminalOperatorFamily (PDE.euclideanBall v0 (4 * ρ)) stationary)
        (K : MovingFiberKernel (PDE.euclideanBall v0 (4 * ρ)) stationary),
        RealizesTerminalEvolution (PDE.euclideanBall v0 (4 * ρ)) stationary
          (PDE.isOpen_euclideanBall v0 (4 * ρ)).measurableSet
          (zIndependentCoefficient B) b S K →
        HasParabolicMarginalBundle (PDE.euclideanBall v0 (4 * ρ)) stationary
          (PDE.isOpen_euclideanBall v0 (4 * ρ)).measurableSet
          (zIndependentCoefficient B) K →
        IsDomainMonotoneEvolution (PDE.euclideanBall v0 (4 * ρ)) stationary
          (zIndependentCoefficient B) b K →
      ∀ (qearly qlate : ParabolicEvolutionQuery (PDE.euclideanBall v0 (4 * ρ)) stationary),
        qearly.1 = (T - 4 * ρ ^ 2, T, qearly.1.2.2) →
        qlate.1 = (T - ρ ^ 2, T, v0) →
        qearly.1.2.2 ∈ PDE.euclideanBall v0 ρ →
        ENNReal.ofReal h • P K (PDE.isOpen_euclideanBall v0 (4 * ρ)).measurableSet qlate ≤
          P K (PDE.isOpen_euclideanBall v0 (4 * ρ)).measurableSet qearly ∧
        ENNReal.ofReal q0 ≤
          P K (PDE.isOpen_euclideanBall v0 (4 * ρ)).measurableSet qlate
            (PDE.euclideanBall v0 (4 * ρ)) := by
  obtain ⟨h, hh, hcomp⟩ := scaled_minorant_comparison d hd lam Lam hlam hlamLam
  obtain ⟨C, q, _hC, _hq, hqpos, hmass⟩ := minorant_mass_floor d hd lam Lam hlam hlamLam
  refine ⟨h, q, hh, hqpos, ?_⟩
  intro m Lb D B b hset v0 ρ T hv0 hρ hsub S K hreal hpar hmono
    qearly qlate hqe hql hv
  have _ := And.intro hv0 (And.intro hsub (And.intro hreal hmono))
  exact ⟨hcomp B hset.1 v0 ρ T hρ K hpar qearly qlate hqe hql hv,
    hmass B hset.1 v0 ρ T (4 * ρ) hρ rfl K hpar qlate hql⟩

end HypoellipticAleksandrov.KineticAleksandrov.Decay
