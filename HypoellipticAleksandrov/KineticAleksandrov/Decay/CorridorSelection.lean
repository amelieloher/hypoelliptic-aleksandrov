module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.RetentionCurve
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.BlockParameters
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierGeometry
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! # Retained corridor measures and their full-domain domination -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Decay
open Set MeasureTheory
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

private theorem normalized_half_mass {d : ℕ}
    (μ : Measure (EvolutionAmbientState d)) [IsFiniteMeasure μ]
    (a : ℝ) (ha : 0 < a) (hμ : a ≤ μ.real univ) :
    (ENNReal.ofReal (a / (2 * μ.real univ)) • μ).real univ = a / 2 ∧
    ENNReal.ofReal (a / (2 * μ.real univ)) • μ ≤ ENNReal.ofReal (1 / 2) • μ := by
  have hp : 0 < μ.real univ := ha.trans_le hμ
  have hc : 0 ≤ a / (2 * μ.real univ) := by positivity
  constructor
  · rw [measureReal_ennreal_smul_apply, ENNReal.toReal_ofReal hc]
    field_simp
  · have hcoef : ENNReal.ofReal (a / (2 * μ.real univ)) ≤
        ENNReal.ofReal (1 / 2) := by
      apply ENNReal.ofReal_le_ofReal
      apply (div_le_iff₀ (by positivity : 0 < 2 * μ.real univ)).mpr
      linarith only [hμ]
    intro A
    simp only [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul_left hcoef _


/-- The retained source corridors normalize to half the uniform mass floor and
are jointly dominated by the supplied full-domain evolution. -/
theorem corridors_retained_dominated (d : ℕ) (hd : 1 ≤ d)
    (lam Lam : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam) :
    ∃ Cstar : ℝ, 0 < Cstar ∧
      ∀ (m Lb σ : ℝ) (D : Set (PDE.Vec d)) (B : CoefficientField d)
        (b : PDE.Vec d → PDE.Vec d), SourceSetting lam Lam m Lb D B b →
      ∀ (SD : TerminalOperatorFamily D stationary) (KD : MovingFiberKernel D stationary)
        (hD : MeasurableSet D),
        RealizesTerminalEvolution D stationary hD (zIndependentCoefficient B) b SD KD →
        IsDomainMonotoneEvolution D stationary (zIndependentCoefficient B) b KD →
      ∀ (γ1 γ2 : ℝ → PDE.Vec d) (v0 z0 : PDE.Vec d),
        IsContinuousPiecewiseC1 γ1 → IsContinuousPiecewiseC1 γ2 →
        γ1 σ = v0 → γ2 σ = v0 → γ1 (σ + blockL0 m) = v0 → γ2 (σ + blockL0 m) = v0 →
        HasCurveSpeedOn (1 / 2) γ1 σ (σ + blockL0 m) →
        HasCurveSpeedOn (1 / 2) γ2 σ (σ + blockL0 m) →
        (∀ r, PDE.euclideanBall (γ1 r) (blockEta m Lb) ⊆ D) →
        (∀ r, PDE.euclideanBall (γ2 r) (blockEta m Lb) ⊆ D) →
      ∀ (S1 : TerminalOperatorFamily (PDE.euclideanBall 0 (blockEta m Lb)) γ1)
        (K1 : MovingFiberKernel (PDE.euclideanBall 0 (blockEta m Lb)) γ1)
        (S2 : TerminalOperatorFamily (PDE.euclideanBall 0 (blockEta m Lb)) γ2)
        (K2 : MovingFiberKernel (PDE.euclideanBall 0 (blockEta m Lb)) γ2),
        RealizesTerminalEvolution (PDE.euclideanBall 0 (blockEta m Lb)) γ1
          (PDE.isOpen_euclideanBall 0 (blockEta m Lb)).measurableSet
          (zIndependentCoefficient B) b S1 K1 →
        RealizesTerminalEvolution (PDE.euclideanBall 0 (blockEta m Lb)) γ2
          (PDE.isOpen_euclideanBall 0 (blockEta m Lb)).measurableSet
          (zIndependentCoefficient B) b S2 K2 →
        HasParabolicMarginalBundle (PDE.euclideanBall 0 (blockEta m Lb)) γ1
          (PDE.isOpen_euclideanBall 0 (blockEta m Lb)).measurableSet
          (zIndependentCoefficient B) K1 →
        HasParabolicMarginalBundle (PDE.euclideanBall 0 (blockEta m Lb)) γ2
          (PDE.isOpen_euclideanBall 0 (blockEta m Lb)).measurableSet
          (zIndependentCoefficient B) K2 →
      ∀ (q1 : EvolutionQuery (PDE.euclideanBall 0 (blockEta m Lb)) γ1)
        (q2 : EvolutionQuery (PDE.euclideanBall 0 (blockEta m Lb)) γ2)
        (qD : EvolutionQuery D stationary),
        q1.1 = (σ, σ + blockL0 m, v0, z0) →
        q2.1 = (σ, σ + blockL0 m, v0, z0) → qD.1 = (σ, σ + blockL0 m, v0, z0) →
        let μ1 := K1.master q1
        let μ2 := K2.master q2
        let m0 := blockMass Cstar m Lb
        let R1 := ENNReal.ofReal (m0 / (2 * μ1.real univ)) • μ1
        let R2 := ENNReal.ofReal (m0 / (2 * μ2.real univ)) • μ2
        m0 ≤ μ1.real univ ∧ μ1.real univ ≤ 1 ∧
        m0 ≤ μ2.real univ ∧ μ2.real univ ≤ 1 ∧
        μ1 ((PDE.euclideanBall v0 (blockEta m Lb) ×ˢ univ)ᶜ) = 0 ∧
        μ2 ((PDE.euclideanBall v0 (blockEta m Lb) ×ˢ univ)ᶜ) = 0 ∧
        R1.real univ = m0 / 2 ∧ R2.real univ = m0 / 2 ∧ R1 + R2 ≤ KD.master qD := by
  obtain ⟨Cstar, hCstar, hret⟩ := moving_ball_retention_of_curve d hd lam Lam hlam hlamLam
  refine ⟨Cstar, hCstar, ?_⟩
  intro m Lb σ D B b hsetting SD KD hD hrealD hmono γ1 γ2 v0 z0
    hγ1 hγ2 hstart1 hstart2 hend1 hend2 hspeed1 hspeed2 hfit1 hfit2
    S1 K1 S2 K2 hreal1 hreal2 hpar1 hpar2 q1 q2 qD hq1 hq2 hqD
  have hm : 0 < m := hsetting.2.2.1
  have hLb : 0 < Lb := hm.trans_le hsetting.2.2.2.1
  have hη := blockEta_pos hm hLb
  have htime : σ ≤ σ + blockL0 m := le_add_of_nonneg_right (blockL0_pos hm).le
  have hball (γ : ℝ → PDE.Vec d) (hs : γ σ = v0) :
      v0 ∈ movingDomain (PDE.euclideanBall 0 (blockEta m Lb)) γ σ := by
    rw [mem_movingDomain_euclideanBall_iff, hs]
    simp only [add_zero, sub_self, PDE.vecNormSq, PDE.vecDot, Pi.zero_apply,
      zero_mul, Finset.sum_const_zero]
    exact sq_pos_of_pos hη
  have hq1' : q1 = movingQuery σ (σ + blockL0 m) htime v0 z0 (hball γ1 hstart1) :=
    Subtype.ext hq1
  have hq2' : q2 = movingQuery σ (σ + blockL0 m) htime v0 z0 (hball γ2 hstart2) :=
    Subtype.ext hq2
  have hmass1 := hret m Lb D B b hsetting σ (σ + blockL0 m) (1 / 2)
    (blockEta m Lb) γ1 htime hη hγ1 hspeed1 (fun r _ => hfit1 r)
    S1 K1 hreal1 hpar1 z0 htime (by simpa only [hstart1] using hball γ1 hstart1)
  have hmass2 := hret m Lb D B b hsetting σ (σ + blockL0 m) (1 / 2)
    (blockEta m Lb) γ2 htime hη hγ2 hspeed2 (fun r _ => hfit2 r)
    S2 K2 hreal2 hpar2 z0 htime (by simpa only [hstart2] using hball γ2 hstart2)
  have hfloor1 : blockMass Cstar m Lb ≤ (K1.master q1).real univ := by
    have hmass : ENNReal.ofReal (Real.exp (-Cstar *
        ((blockEta m Lb)⁻¹ ^ 2 + (1 / 2) ^ 2) * (σ + blockL0 m - σ))) ≤
        K1.master q1 (PDE.euclideanBall v0 (blockEta m Lb) ×ˢ univ) := by
      simpa only [hq1', hstart1, hend1] using hmass1
    have h := hmass.trans (measure_mono (subset_univ _))
    have hf : IsFiniteMeasure (K1.master q1) :=
      ⟨(K1.mass_le_one q1).trans_lt ENNReal.one_lt_top⟩
    have hh := ENNReal.toReal_mono (measure_ne_top _ _) h
    simpa only [measureReal_def, blockMass, add_sub_cancel_left, one_div, div_pow,
      one_pow, show (2 : ℝ) ^ 2 = 4 by norm_num,
      show (2 : ℝ)⁻¹ ^ 2 = 4⁻¹ by norm_num,
      ENNReal.toReal_ofReal (Real.exp_pos _).le] using hh
  have hfloor2 : blockMass Cstar m Lb ≤ (K2.master q2).real univ := by
    have hmass : ENNReal.ofReal (Real.exp (-Cstar *
        ((blockEta m Lb)⁻¹ ^ 2 + (1 / 2) ^ 2) * (σ + blockL0 m - σ))) ≤
        K2.master q2 (PDE.euclideanBall v0 (blockEta m Lb) ×ˢ univ) := by
      simpa only [hq2', hstart2, hend2] using hmass2
    have h := hmass.trans (measure_mono (subset_univ _))
    have hf : IsFiniteMeasure (K2.master q2) :=
      ⟨(K2.mass_le_one q2).trans_lt ENNReal.one_lt_top⟩
    have hh := ENNReal.toReal_mono (measure_ne_top _ _) h
    simpa only [measureReal_def, blockMass, add_sub_cancel_left, one_div, div_pow,
      one_pow, show (2 : ℝ) ^ 2 = 4 by norm_num,
      show (2 : ℝ)⁻¹ ^ 2 = 4⁻¹ by norm_num,
      ENNReal.toReal_ofReal (Real.exp_pos _).le] using hh
  have hsub (γ : ℝ → PDE.Vec d)
      (hfit : ∀ r, PDE.euclideanBall (γ r) (blockEta m Lb) ⊆ D) :
      ∀ r, movingDomain (PDE.euclideanBall 0 (blockEta m Lb)) γ r ⊆
        movingDomain D stationary r := by
    intro r v hv
    rw [mem_movingDomain_euclideanBall_iff] at hv
    apply (mem_movingDomain_iff).mpr
    simpa only [stationary, sub_zero] using hfit r (by
      simpa only [add_zero, PDE.euclideanBall, PDE.euclideanSqDist,
        mem_ofPred_eq] using hv)
  have hadm : IsAdmissibleEvolutionDomain (PDE.euclideanBall (0 : PDE.Vec d)
      (blockEta m Lb)) := Or.inr (Or.inl ⟨0, blockEta m Lb, hη, rfl⟩)
  have hdom1 := domainMonotone_of_realizes (zIndependentCoefficient B) b KD hmono
    _ γ1 hadm hγ1 (hsub γ1 hfit1) S1 K1 hreal1 q1
  have hdom2 := domainMonotone_of_realizes (zIndependentCoefficient B) b KD hmono
    _ γ2 hadm hγ2 (hsub γ2 hfit2) S2 K2 hreal2 q2
  have hlarge1 : largeQueryOfSmall (hsub γ1 hfit1) q1 = qD :=
    Subtype.ext (hq1.trans hqD.symm)
  have hlarge2 : largeQueryOfSmall (hsub γ2 hfit2) q2 = qD :=
    Subtype.ext (hq2.trans hqD.symm)
  rw [hlarge1] at hdom1
  rw [hlarge2] at hdom2
  have hf1 : IsFiniteMeasure (K1.master q1) :=
    ⟨(K1.mass_le_one q1).trans_lt ENNReal.one_lt_top⟩
  have hf2 : IsFiniteMeasure (K2.master q2) :=
    ⟨(K2.mass_le_one q2).trans_lt ENNReal.one_lt_top⟩
  have hnorm1 := normalized_half_mass (K1.master q1) (blockMass Cstar m Lb)
    (Real.exp_pos _) hfloor1
  have hnorm2 := normalized_half_mass (K2.master q2) (blockMass Cstar m Lb)
    (Real.exp_pos _) hfloor2
  have hsupp (γ : ℝ → PDE.Vec d) (K : MovingFiberKernel
      (PDE.euclideanBall 0 (blockEta m Lb)) γ) (q : EvolutionQuery
      (PDE.euclideanBall 0 (blockEta m Lb)) γ)
      (hq : q.1 = (σ, σ + blockL0 m, v0, z0)) (hend : γ (σ + blockL0 m) = v0) :
      K.master q (PDE.euclideanBall v0 (blockEta m Lb) ×ˢ univ)ᶜ = 0 := by
    have he : evolutionStateSet (PDE.euclideanBall 0 (blockEta m Lb)) γ q.1.2.1 =
        PDE.euclideanBall v0 (blockEta m Lb) ×ˢ univ := by
      simp only [evolutionStateSet, hq]
      congr 1
      ext v
      rw [mem_movingDomain_euclideanBall_iff, hend]
      simp only [add_zero, PDE.euclideanBall, PDE.euclideanSqDist, mem_ofPred_eq]
    have hr := K.terminal_support q
    rw [he] at hr
    rw [← hr, Measure.restrict_apply
      ((PDE.isOpen_euclideanBall v0 (blockEta m Lb)).measurableSet.prod
        MeasurableSet.univ).compl, compl_inter_self, measure_empty]
  refine ⟨hfloor1, ?_, hfloor2, ?_, hsupp γ1 K1 q1 hq1 hend1,
    hsupp γ2 K2 q2 hq2 hend2, hnorm1.1, hnorm2.1, ?_⟩
  · simpa only [measureReal_def, ENNReal.toReal_one] using
      ENNReal.toReal_mono ENNReal.one_ne_top (K1.mass_le_one q1)
  · simpa only [measureReal_def, ENNReal.toReal_one] using
      ENNReal.toReal_mono ENNReal.one_ne_top (K2.mass_le_one q2)
  · calc
      _ ≤ ENNReal.ofReal (1 / 2) • KD.master qD +
          ENNReal.ofReal (1 / 2) • KD.master qD :=
        add_le_add (hnorm1.2.trans (fun A => by
          simpa only [Measure.smul_apply, smul_eq_mul] using
            mul_le_mul_right (hdom1 A) (ENNReal.ofReal (1 / 2))))
          (hnorm2.2.trans (fun A => by
          simpa only [Measure.smul_apply, smul_eq_mul] using
            mul_le_mul_right (hdom2 A) (ENNReal.ofReal (1 / 2))))
      _ = KD.master qD := by
        rw [← add_smul, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
        norm_num

end HypoellipticAleksandrov.KineticAleksandrov.Decay
