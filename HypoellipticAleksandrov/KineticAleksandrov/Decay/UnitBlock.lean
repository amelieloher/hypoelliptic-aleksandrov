module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.UnitBlockEvolution
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.UnitBlockRetentionLift
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.CorridorSelection
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.ContinuedSelection
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.CommonSelection
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.ContinuedPhase
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.BlockInterior
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.OppositePaths
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierGeometry
import Mathlib.Tactic.Linarith

/-! # The source unit-frequency block in case W -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Decay
open Set MeasureTheory
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

/-- The exact case-W unit-block conditions, conditional only on the authorized
terminal-evolution existence statement. -/
theorem unit_frequency_block_W (hEvol : IterationEvolutionStatement)
    (d : ℕ) (hd : 1 ≤ d) (lam Lam : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam) :
    UnitBlockStatementW d hd lam Lam 1 1 hlam hlamLam zero_lt_one le_rfl := by
  obtain ⟨Cstar, hC, hcorr⟩ := corridors_retained_dominated d hd lam Lam hlam hlamLam
  obtain ⟨h, q0, hh, hq0, hcommon⟩ :=
    continued_common_minorant_trimming d hd lam Lam hlam hlamLam
  let δ0 := (3 / 4) * blockMass Cstar 1 1 * h * q0
  have hδ0 : 0 < δ0 := by
    exact mul_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 3 / 4)
      (Real.exp_pos _)) hh) hq0
  let δ := min δ0 (1 / 2)
  have hδ : 0 < δ := lt_min hδ0 (by norm_num)
  have hδ1 : δ < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have htime := (block_parameters Cstar h q0 1 1 hC hh hq0 zero_lt_one le_rfl).2.2.2.2.2.2.1
  refine ⟨blockTime 1 1, δ, htime, hδ, hδ1, ?_⟩
  intro D B b hsetting hDW hD S K hreal hmono hpar hcov ξ hξ σ v hv hL ν hν
  subst D
  let ρ := blockRho 1
  let η := blockEta 1 1
  let s := σ + blockL0 1
  let T := σ + blockTime 1 1
  let Ω := PDE.euclideanBall v (4 * ρ)
  have hρ : 0 < ρ := blockRho_pos zero_lt_one
  have hη : 0 < η := blockEta_pos zero_lt_one zero_lt_one
  have hηρ : η < ρ := blockEta_lt_rho zero_lt_one
  have hστ : σ ≤ s := le_add_of_nonneg_right (blockL0_pos zero_lt_one).le
  have hsT : s ≤ T := by
    dsimp only [s, T, blockTime]
    nlinarith only [sq_nonneg ρ]
  have hfit : PDE.euclideanBall v (blockOuter 1) ⊆ (univ : Set (PDE.Vec d)) := subset_univ _
  obtain ⟨α, -, -, hpaths⟩ := exists_opposite_paths 1 1 σ zero_lt_one le_rfl
    univ b hsetting.2.1 hsetting.2.2.2.2.1 ξ v hξ hfit
  let γ1 : ℝ → PDE.Vec d := fun _ => v
  let γ2 : ℝ → PDE.Vec d := fun r =>
    v + (α * tent (blockL0 1) (max 0 (min (blockL0 1) (r - σ)))) • ξ
  obtain ⟨hγ1, hγ2, hstart1, hstart2, hend1, hend2,
    hspeed1, hspeed2, htube, hphase⟩ := hpaths
  change γ1 σ = v at hstart1
  change γ2 σ = v at hstart2
  have hadm : IsAdmissibleEvolutionDomain (PDE.euclideanBall (0 : PDE.Vec d) η) :=
    Or.inr (Or.inl ⟨0, η, hη, rfl⟩)
  have hΩadm : IsAdmissibleEvolutionDomain Ω :=
    Or.inr (Or.inl ⟨v, 4 * ρ, mul_pos (by norm_num) hρ, rfl⟩)
  obtain ⟨S1, K1, hreal1, -, hpar1, -⟩ :=
    exists_unitBlock_evolution hEvol hd lam Lam 1 1 univ B b hsetting _ γ1 hadm hγ1
  obtain ⟨S2, K2, hreal2, -, hpar2, -⟩ :=
    exists_unitBlock_evolution hEvol hd lam Lam 1 1 univ B b hsetting _ γ2 hadm hγ2
  obtain ⟨S0, K0, hreal0, hmono0, hpar0, -⟩ :=
    exists_unitBlock_evolution hEvol hd lam Lam 1 1 univ B b hsetting Ω stationary
      hΩadm (zeroCurve_piecewiseC1 d)
  have hv1 : v ∈ movingDomain (PDE.euclideanBall 0 η) γ1 σ := by
    rw [mem_movingDomain_euclideanBall_iff, hstart1]
    simp only [add_zero, sub_self, PDE.vecNormSq, PDE.vecDot, Pi.zero_apply,
      zero_mul, Finset.sum_const_zero]
    exact sq_pos_of_pos hη
  have hv2 : v ∈ movingDomain (PDE.euclideanBall 0 η) γ2 σ := by
    rw [mem_movingDomain_euclideanBall_iff, hstart2]
    simp only [add_zero, sub_self, PDE.vecNormSq, PDE.vecDot, Pi.zero_apply,
      zero_mul, Finset.sum_const_zero]
    exact sq_pos_of_pos hη
  let q1 := movingQuery σ s hστ v 0 hv1
  let q2 := movingQuery σ s hστ v 0 hv2
  let qD := movingQuery σ s hστ v 0 hv
  let qT := movingQuery σ T hL v 0 hv
  obtain ⟨-, -, -, -, hsupp1, hsupp2, hmass1, hmass2, hdom⟩ :=
    hcorr 1 1 σ univ B b hsetting S K hD hreal hmono γ1 γ2 v 0
      hγ1 hγ2 hstart1 hstart2 hend1 hend2 hspeed1 hspeed2
      (fun r => (htube r).1) (fun r => (htube r).2)
      S1 K1 S2 K2 hreal1 hreal2 hpar1 hpar2 q1 q2 qD rfl rfl rfl
  let μ1 := K1.master q1
  let μ2 := K2.master q2
  have hfμ1 : IsFiniteMeasure μ1 := ⟨(K1.mass_le_one q1).trans_lt ENNReal.one_lt_top⟩
  have hfμ2 : IsFiniteMeasure μ2 := ⟨(K2.mass_le_one q2).trans_lt ENNReal.one_lt_top⟩
  let N1 := ENNReal.ofReal (blockMass Cstar 1 1 / (2 * μ1.real univ)) • μ1
  let N2 := ENNReal.ofReal (blockMass Cstar 1 1 / (2 * μ2.real univ)) • μ2
  have hfN1 : IsFiniteMeasure N1 := by
    refine ⟨?_⟩
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ1 univ)
  have hfN2 : IsFiniteMeasure N2 := by
    refine ⟨?_⟩
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ2 univ)
  have hN1supp : N1 (PDE.euclideanBall v η ×ˢ univ)ᶜ = 0 := by
    rw [Measure.smul_apply, hsupp1, smul_zero]
  have hN2supp : N2 (PDE.euclideanBall v η ×ˢ univ)ᶜ = 0 := by
    rw [Measure.smul_apply, hsupp2, smul_zero]
  let R1 := N1.comap (Subtype.val : EvolutionState Ω stationary s → EvolutionAmbientState d)
  let R2 := N2.comap (Subtype.val : EvolutionState Ω stationary s → EvolutionAmbientState d)
  have hη4ρ : η ≤ 4 * ρ := by linarith only [hηρ, hρ]
  obtain ⟨hR1, hmR1, hsupport1⟩ := retained_ball_comap_properties v η (4 * ρ) s
    hη.le hη4ρ N1 hN1supp
  obtain ⟨hR2, hmR2, hsupport2⟩ := retained_ball_comap_properties v η (4 * ρ) s
    hη.le hη4ρ N2 hN2supp
  have hfR1 : IsFiniteMeasure R1 := inferInstance
  have hfR2 : IsFiniteMeasure R2 := inferInstance
  let E1 := continuedMeasure K0 hsT R1
  let E2 := continuedMeasure K0 hsT R2
  have hE1 : ∀ A, MeasurableSet A → E1 A =
      ∫⁻ p, K0.master (movingQuery s T hsT p.1.1 p.1.2 p.2.1) A ∂R1 :=
    fun A hA => continuedMeasure_apply K0 hsT R1 hA
  have hE2 : ∀ A, MeasurableSet A → E2 A =
      ∫⁻ p, K0.master (movingQuery s T hsT p.1.1 p.1.2 p.2.1) A ∂R2 :=
    fun A hA => continuedMeasure_apply K0 hsT R2 hA
  let M := K.master qT
  have hfM : IsFiniteMeasure M := ⟨(K.mass_le_one qT).trans_lt ENNReal.one_lt_top⟩
  have hcontinued : E1 + E2 ≤ M := by
    apply continued_measures_dominated univ Ω hD (PDE.isOpen_euclideanBall v (4 * ρ)).measurableSet
      B b S K S0 K0 hreal hreal0 hmono hΩadm (subset_univ _) σ s T hστ hsT qD qT
      ⟨rfl, rfl⟩ rfl R1 R2 _ E1 E2 hE1 hE2
    rw [hR1, hR2]
    exact hdom
  have hs : s = T - 4 * ρ ^ 2 := by dsimp only [s, T, blockTime]; ring
  have ha : 0 < blockMass Cstar 1 1 / 2 := div_pos (Real.exp_pos _) (by norm_num)
  have hvΩ : v ∈ movingDomain Ω stationary (T - ρ ^ 2) := by
    rw [movingDomain_stationary]
    change PDE.vecNormSq (v - v) < (4 * ρ) ^ 2
    simpa only [sub_self, PDE.vecNormSq, PDE.vecDot, Pi.zero_apply,
      zero_mul, Finset.sum_const_zero] using sq_pos_of_pos (mul_pos (by norm_num) hρ)
  let qlate := scalarQuery (T - ρ ^ 2) T (sub_le_self _ (sq_nonneg ρ)) v hvΩ
  obtain ⟨-, -, hfloor, F1, F2, hF1, hF2, hFsum, hmap1, hmap2⟩ :=
    hcommon 1 1 univ B b hsetting v ρ T (mem_univ _) hρ (subset_univ _)
      S0 K0 hreal0 hpar0 hmono0 s (blockMass Cstar 1 1 / 2) η hs hsT ha hη hηρ
      R1 R2 hfR1 hfR2 (hmR1.trans hmass1) (hmR2.trans hmass2) hsupport1 hsupport2
      E1 E2 M hfM hE1 hE2 hcontinued qlate rfl
  let Θ := ENNReal.ofReal (blockMass Cstar 1 1 / 2 * h) •
    P K0 (PDE.isOpen_euclideanBall v (4 * ρ)).measurableSet qlate
  have hfE1 : IsFiniteMeasure E1 := inferInstance
  have hfE2 : IsFiniteMeasure E2 := inferInstance
  have hfF1 : IsFiniteMeasure F1 := isFiniteMeasure_of_le _ hF1
  have hfF2 : IsFiniteMeasure F2 := isFiniteMeasure_of_le _ hF2
  obtain ⟨hΦ, -, -, hf1, hf2⟩ := block_continued_phase_error hd lam Lam 1 1 Cstar σ
    univ B b hsetting hC ξ v 0 hξ hfit γ1 γ2 hγ1 hγ2 hstart1 hstart2 hend1 hend2
    (fun r => (htube r).1) (fun r => (htube r).2) hphase
    S1 K1 S2 K2 S0 K0 hreal1 hreal2 hreal0 hpar1 hpar2 hpar0 q1 q2 rfl rfl
    R1 R2 hR1 hR2 hsT E1 E2 F1 F2 hE1 hE2 hF1 hF2
  have hMone : M.real univ ≤ 1 := by
    simpa only [measureReal_def, ENNReal.toReal_one] using
      ENNReal.toReal_mono ENNReal.one_ne_top (K.mass_le_one qT)
  have hmass : blockMass Cstar 1 1 * h * q0 / 2 ≤ Θ.real univ := by
    convert hfloor using 1
    ring
  have hphaseν : IsPhaseProjection (phaseCoordinate ξ (0 : PDE.Vec d)) M ν := by
    intro A hA
    exact hν A hA
  have hcancel := (block_interior_cancellation ξ 0 M F1 F2 Θ (blockMass Cstar 1 1)
    h q0 _ _ hMone hFsum hmap1 hmap2 hmass hΦ hf1 hf2 ν hphaseν).2
  exact hcancel.trans (sub_le_sub_left (min_le_left δ0 (1 / 2)) 1)

end HypoellipticAleksandrov.KineticAleksandrov.Decay
