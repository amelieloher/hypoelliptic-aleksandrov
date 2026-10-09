module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.ContinuedPhaseSupport
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.ContinuedPhaseStationary
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.BlockParameters
import Mathlib.MeasureTheory.Measure.Module
import Mathlib.Tactic.Linarith

/-! # Source block phase errors after continuation and trimming -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Decay
open Set MeasureTheory
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

/-- The two actual corridor phases remain in quarter-width strips after continuation. -/
theorem block_continued_phase_error {d : ℕ} (hd : 1 ≤ d)
    (lam Lam m Lb Cstar σ : ℝ) (D : Set (PDE.Vec d))
    (B : CoefficientField d) (b : PDE.Vec d → PDE.Vec d)
    (hsetting : SourceSetting lam Lam m Lb D B b) (hC : 0 < Cstar)
    (ξ v0 z0 : PDE.Vec d) (hξ : PDE.vecNormSq ξ = 1)
    (hfit : PDE.euclideanBall v0 (blockOuter Lb) ⊆ D)
    (γ1 γ2 : ℝ → PDE.Vec d)
    (hγ1 : IsContinuousPiecewiseC1 γ1) (hγ2 : IsContinuousPiecewiseC1 γ2)
    (hstart1 : γ1 σ = v0) (hstart2 : γ2 σ = v0)
    (hend1 : γ1 (σ + blockL0 m) = v0) (hend2 : γ2 (σ + blockL0 m) = v0)
    (htube1 : ∀ r, PDE.euclideanBall (γ1 r) (blockEta m Lb) ⊆ D)
    (htube2 : ∀ r, PDE.euclideanBall (γ2 r) (blockEta m Lb) ⊆ D)
    (hphase : phaseCenter ξ b γ2 σ (σ + blockL0 m) -
      phaseCenter ξ b γ1 σ (σ + blockL0 m) = Real.pi)
    (S1 : TerminalOperatorFamily (PDE.euclideanBall 0 (blockEta m Lb)) γ1)
    (K1 : MovingFiberKernel (PDE.euclideanBall 0 (blockEta m Lb)) γ1)
    (S2 : TerminalOperatorFamily (PDE.euclideanBall 0 (blockEta m Lb)) γ2)
    (K2 : MovingFiberKernel (PDE.euclideanBall 0 (blockEta m Lb)) γ2)
    (S0 : TerminalOperatorFamily (PDE.euclideanBall v0 (4 * blockRho Lb)) stationary)
    (K0 : MovingFiberKernel (PDE.euclideanBall v0 (4 * blockRho Lb)) stationary)
    (hreal1 : RealizesTerminalEvolution (PDE.euclideanBall 0 (blockEta m Lb)) γ1
      (PDE.isOpen_euclideanBall 0 (blockEta m Lb)).measurableSet
      (zIndependentCoefficient B) b S1 K1)
    (hreal2 : RealizesTerminalEvolution (PDE.euclideanBall 0 (blockEta m Lb)) γ2
      (PDE.isOpen_euclideanBall 0 (blockEta m Lb)).measurableSet
      (zIndependentCoefficient B) b S2 K2)
    (hreal0 : RealizesTerminalEvolution (PDE.euclideanBall v0 (4 * blockRho Lb)) stationary
      (PDE.isOpen_euclideanBall v0 (4 * blockRho Lb)).measurableSet
      (zIndependentCoefficient B) b S0 K0)
    (hpar1 : HasParabolicMarginalBundle (PDE.euclideanBall 0 (blockEta m Lb)) γ1
      (PDE.isOpen_euclideanBall 0 (blockEta m Lb)).measurableSet
      (zIndependentCoefficient B) K1)
    (hpar2 : HasParabolicMarginalBundle (PDE.euclideanBall 0 (blockEta m Lb)) γ2
      (PDE.isOpen_euclideanBall 0 (blockEta m Lb)).measurableSet
      (zIndependentCoefficient B) K2)
    (hpar0 : HasParabolicMarginalBundle (PDE.euclideanBall v0 (4 * blockRho Lb)) stationary
      (PDE.isOpen_euclideanBall v0 (4 * blockRho Lb)).measurableSet
      (zIndependentCoefficient B) K0)
    (q1 : EvolutionQuery (PDE.euclideanBall 0 (blockEta m Lb)) γ1)
    (q2 : EvolutionQuery (PDE.euclideanBall 0 (blockEta m Lb)) γ2)
    (hq1 : q1.1 = (σ, σ + blockL0 m, v0, z0))
    (hq2 : q2.1 = (σ, σ + blockL0 m, v0, z0))
    (R1 R2 : Measure (EvolutionState
      (PDE.euclideanBall v0 (4 * blockRho Lb)) stationary (σ + blockL0 m)))
    [IsFiniteMeasure R1] [IsFiniteMeasure R2]
    (hR1 : Measure.map Subtype.val R1 =
      ENNReal.ofReal (blockMass Cstar m Lb / (2 * (K1.master q1).real univ)) • K1.master q1)
    (hR2 : Measure.map Subtype.val R2 =
      ENNReal.ofReal (blockMass Cstar m Lb / (2 * (K2.master q2).real univ)) • K2.master q2)
    (hsT : σ + blockL0 m ≤ σ + blockTime m Lb)
    (E1 E2 F1 F2 : Measure (EvolutionAmbientState d))
    (hE1 : ∀ A, MeasurableSet A → E1 A =
      ∫⁻ p, K0.master (movingQuery (σ + blockL0 m) (σ + blockTime m Lb)
        hsT p.1.1 p.1.2 p.2.1) A ∂R1)
    (hE2 : ∀ A, MeasurableSet A → E2 A =
      ∫⁻ p, K0.master (movingQuery (σ + blockL0 m) (σ + blockTime m Lb)
        hsT p.1.1 p.1.2 p.2.1) A ∂R2)
    (hF1 : F1 ≤ E1) (hF2 : F2 ≤ E2) :
    let Φ1 := phaseCenter ξ b γ1 σ (σ + blockL0 m) +
      4 * blockRho Lb ^ 2 * PDE.vecDot ξ (b v0)
    let Φ2 := phaseCenter ξ b γ2 σ (σ + blockL0 m) +
      4 * blockRho Lb ^ 2 * PDE.vecDot ξ (b v0)
    Φ2 - Φ1 = Real.pi ∧
    (∀ᵐ x ∂E1, |phaseCoordinate ξ z0 x - Φ1| ≤ 1 / 4) ∧
    (∀ᵐ x ∂E2, |phaseCoordinate ξ z0 x - Φ2| ≤ 1 / 4) ∧
    (∀ᵐ x ∂F1, |phaseCoordinate ξ z0 x - Φ1| ≤ 1 / 4) ∧
    (∀ᵐ x ∂F2, |phaseCoordinate ξ z0 x - Φ2| ≤ 1 / 4) := by
  have hm : 0 < m := hsetting.2.2.1
  have hLb : 0 < Lb := hm.trans_le hsetting.2.2.2.1
  have hρ := blockRho_pos hLb
  have hη := blockEta_pos hm hLb
  have hστ : σ ≤ σ + blockL0 m := le_add_of_nonneg_right (blockL0_pos hm).le
  have hsmall := add_le_add (Lb_mul_blockEta_mul_blockL0_le hm hLb)
    (sixteen_Lb_mul_blockRho_pow_three_le hLb)
  have hbound (γ : ℝ → PDE.Vec d) (hγ : IsContinuousPiecewiseC1 γ)
      (S : TerminalOperatorFamily (PDE.euclideanBall 0 (blockEta m Lb)) γ)
      (K : MovingFiberKernel (PDE.euclideanBall 0 (blockEta m Lb)) γ)
      (hreal : RealizesTerminalEvolution (PDE.euclideanBall 0 (blockEta m Lb)) γ
        (PDE.isOpen_euclideanBall 0 (blockEta m Lb)).measurableSet
        (zIndependentCoefficient B) b S K)
      (q : EvolutionQuery (PDE.euclideanBall 0 (blockEta m Lb)) γ)
      (hq : q.1 = (σ, σ + blockL0 m, v0, z0))
      (R : Measure (EvolutionState (PDE.euclideanBall v0 (4 * blockRho Lb))
        stationary (σ + blockL0 m))) [IsFiniteMeasure R]
      (hR : R.map Subtype.val =
        ENNReal.ofReal (blockMass Cstar m Lb / (2 * (K.master q).real univ)) • K.master q)
      (E : Measure (EvolutionAmbientState d))
      (hE : ∀ A, MeasurableSet A → E A =
        ∫⁻ p, K0.master (movingQuery (σ + blockL0 m) (σ + blockTime m Lb)
          hsT p.1.1 p.1.2 p.2.1) A ∂R) :
      ∀ᵐ x ∂E, |phaseCoordinate ξ z0 x -
        (phaseCenter ξ b γ σ (σ + blockL0 m) +
          4 * blockRho Lb ^ 2 * PDE.vecDot ξ (b v0))| ≤ 1 / 4 := by
    have hv : v0 ∈ movingDomain (PDE.euclideanBall 0 (blockEta m Lb)) γ σ := by
      have h := q.2.2.1
      simpa only [hq] using h
    have hq' : q = movingQuery σ (σ + blockL0 m) hστ v0 z0 hv := Subtype.ext hq
    have hphase := phase_localization_of_continuous_curve d lam Lam m Lb D B b
      hsetting σ (σ + blockL0 m) (blockEta m Lb) γ hη hγ.1 S K hreal ξ z0 v0 hξ hστ hv
    rw [← hq'] at hphase
    have hRphase : ∀ᵐ p ∂R, |phaseCoordinate ξ z0 p.1 -
        phaseCenter ξ b γ σ (σ + blockL0 m)| ≤ Lb * blockEta m Lb * blockL0 m := by
      have h := Measure.ae_smul_measure hphase
        (ENNReal.ofReal (blockMass Cstar m Lb / (2 * (K.master q).real univ)))
      rw [← hR] at h
      have h' := ae_of_ae_map measurable_subtype_coe.aemeasurable h
      simpa only [add_sub_cancel_left] using h'
    have hKphase : ∀ᵐ p ∂R, ∀ᵐ x ∂continuationKernel K0 hsT p,
        |phaseCoordinate ξ p.1.2 x -
          (4 * blockRho Lb ^ 2 * PDE.vecDot ξ (b v0))| ≤
            16 * Lb * blockRho Lb ^ 3 := by
      apply Filter.Eventually.of_forall
      intro p
      have hp := stationary_phase_localization d lam Lam m Lb D B b hsetting
        (σ + blockL0 m) (σ + blockTime m Lb) (4 * blockRho Lb) v0
        (mul_pos (by norm_num) hρ) S0 K0 hreal0 ξ p.1.2 p.1.1 hξ hsT p.2.1
      have hc : phaseCenter ξ b (fun _ => v0) (σ + blockL0 m)
          (σ + blockTime m Lb) = 4 * blockRho Lb ^ 2 * PDE.vecDot ξ (b v0) := by
        unfold phaseCenter blockTime
        rw [intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        ring
      rw [hc] at hp
      have he : Lb * (4 * blockRho Lb) *
          (σ + blockTime m Lb - (σ + blockL0 m)) = 16 * Lb * blockRho Lb ^ 3 := by
        unfold blockTime
        ring
      simpa only [he, continuationKernel_apply, evolutionQueryOfState_eq, movingQuery] using hp
    have h := continuation_phase_support Subtype.val measurable_subtype_coe ξ z0
      (phaseCenter ξ b γ σ (σ + blockL0 m))
      (4 * blockRho Lb ^ 2 * PDE.vecDot ξ (b v0))
      (Lb * blockEta m Lb * blockL0 m) (16 * Lb * blockRho Lb ^ 3)
      R (continuationKernel K0 hsT) hRphase hKphase E hE
    exact h.mono (fun x hx => hx.trans (by linarith only [hsmall]))
  have he1 := hbound γ1 hγ1 S1 K1 hreal1 q1 hq1 R1 hR1 E1 hE1
  have he2 := hbound γ2 hγ2 S2 K2 hreal2 q2 hq2 R2 hR2 E2 hE2
  refine ⟨?_, he1, he2, ?_, ?_⟩
  · linarith only [hphase]
  · exact he1.filter_mono (ae_mono hF1)
  · exact he2.filter_mono (ae_mono hF2)

end HypoellipticAleksandrov.KineticAleksandrov.Decay
