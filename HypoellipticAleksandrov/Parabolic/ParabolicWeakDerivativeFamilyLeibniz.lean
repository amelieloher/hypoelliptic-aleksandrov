module

public import HypoellipticAleksandrov.Parabolic.TimeVelocityMultiIndexSplitSuccessor
public import HypoellipticAleksandrov.Parabolic.LocalWeakTimeProduct
public import HypoellipticAleksandrov.Parabolic.MeasurableSpatialC1WeakLeibniz
public import HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamily
public import HypoellipticAleksandrov.Parabolic.TimeVelocityMultiIndexLocalCalculus

/-! # Weak multi-index Leibniz families

This module constructs the finite family of weak parabolic derivatives of a
product between a classical coefficient and a selected weak derivative family.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped ENNReal BigOperators

/-- The literal multi-index Leibniz representative for multiplication of a
selected weak derivative family by a classical coefficient. -/
noncomputable def parabolicWeakMulRepresentative
    {d L : ℕ}
    (q : TimeVelocity d → ℝ)
    {U : Set (TimeVelocity d)} {u : TimeVelocity d → ℝ}
    (Du : ParabolicWeakDerivativeFamily d L U u)
    (beta : ParabolicDerivativeIndex d L) :
    TimeVelocity d → ℝ :=
  fun z =>
    ∑ gamma : TimeVelocityMultiIndex.Split beta.1,
      (beta.1.choose gamma.left : ℝ) *
        TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left q z *
        Du.representative
          (ParabolicDerivativeIndex.splitRight beta gamma) z

private theorem coordinateIteratedFDeriv_contDiffAt
    {d : ℕ} (alpha : TimeVelocityMultiIndex d) (m : ℕ)
    (f : TimeVelocity d → ℝ) (z : TimeVelocity d)
    (hf : ContDiffAt ℝ (m + alpha.order) f z) :
    ContDiffAt ℝ m (TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha f) z := by
  unfold TimeVelocityMultiIndex.coordinateIteratedFDeriv
  have hi := hf.iteratedFDeriv_right
    (m := m) (i := alpha.coordinateList.length) (by simp)
  exact (contDiffAt_const (c := ContinuousMultilinearMap.apply ℝ _ _
    (fun i ↦ timeVelocityBasis (alpha.coordinateList.get i)))).clm_apply hi

private theorem order_le_parabolicWeight {d : ℕ} (alpha : TimeVelocityMultiIndex d) :
    alpha.order ≤ alpha.parabolicWeight := by
  simp [TimeVelocityMultiIndex.order, TimeVelocityMultiIndex.timeOrder,
    TimeVelocityMultiIndex.velocity, VelocityMultiIndex.order,
    TimeVelocityMultiIndex.parabolicWeight, VelocityMultiIndex.parabolicWeight]
  omega

private theorem timeDerivative_coordinateIteratedFDeriv
    {d : ℕ} {U : Set (TimeVelocity d)} (alpha : TimeVelocityMultiIndex d)
    (f : TimeVelocity d → ℝ) (z : TimeVelocity d) (hz : z ∈ U)
    (hU : IsOpen U) (hf : ContDiffOn ℝ (alpha.order + 1) f U) :
    timeDerivative (TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha f) z =
      TimeVelocityMultiIndex.coordinateIteratedFDeriv
        (alpha + Pi.single (timeCoord d) 1) f z := by
  rw [TimeVelocityMultiIndex.coordinateIteratedFDeriv_add_single_at
    alpha (timeCoord d) f z]
  · simp [timeDerivative]
  · simpa [add_comm] using hf.contDiffAt (hU.mem_nhds hz)

private theorem velocityGradient_coordinateIteratedFDeriv
    {d : ℕ} {U : Set (TimeVelocity d)} (alpha : TimeVelocityMultiIndex d)
    (f : TimeVelocity d → ℝ) (i : Fin d) (z : TimeVelocity d) (hz : z ∈ U)
    (hU : IsOpen U) (hf : ContDiffOn ℝ (alpha.order + 1) f U) :
    velocityGradient (TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha f) z i =
      TimeVelocityMultiIndex.coordinateIteratedFDeriv
        (alpha + Pi.single (velocityCoord i) 1) f z := by
  rw [TimeVelocityMultiIndex.coordinateIteratedFDeriv_add_single_at
    alpha (velocityCoord i) f z]
  · unfold velocityGradient
    rfl
  · simpa [add_comm] using hf.contDiffAt (hU.mem_nhds hz)

private theorem index_order_le {d L : ℕ} (alpha : ParabolicDerivativeIndex d L) :
    alpha.1.order ≤ L := by
  have heq : alpha.1.order + alpha.1.timeOrder = alpha.1.parabolicWeight := by
    simp [TimeVelocityMultiIndex.order, TimeVelocityMultiIndex.timeOrder,
    TimeVelocityMultiIndex.velocity, VelocityMultiIndex.order,
    TimeVelocityMultiIndex.parabolicWeight, VelocityMultiIndex.parabolicWeight]
    omega
  omega

private theorem split_left_weight_le {d : ℕ} {beta : TimeVelocityMultiIndex d}
    (gamma : TimeVelocityMultiIndex.Split beta) :
    gamma.left.parabolicWeight ≤ beta.parabolicWeight := by
  have hw : gamma.left.parabolicWeight + gamma.right.parabolicWeight =
      beta.parabolicWeight := by
    rw [← TimeVelocityMultiIndex.parabolicWeight_add,
      gamma.left_add_right]
  omega

private theorem split_right_weight_le {d : ℕ} {beta : TimeVelocityMultiIndex d}
    (gamma : TimeVelocityMultiIndex.Split beta) :
    gamma.right.parabolicWeight ≤ beta.parabolicWeight := by
  have hw : gamma.left.parabolicWeight + gamma.right.parabolicWeight =
      beta.parabolicWeight := by
    rw [← TimeVelocityMultiIndex.parabolicWeight_add,
      gamma.left_add_right]
  omega

private theorem split_zero_eq {d : ℕ}
    (gamma : TimeVelocityMultiIndex.Split (0 : TimeVelocityMultiIndex d)) :
  gamma = default := by
  funext c
  exact Fin.eq_zero _

private theorem representative_zero
    {d L : ℕ} (q : TimeVelocity d → ℝ)
    {U : Set (TimeVelocity d)} {u : TimeVelocity d → ℝ}
    (Du : ParabolicWeakDerivativeFamily d L U u) :
    parabolicWeakMulRepresentative q Du (ParabolicDerivativeIndex.zero d L) =
      fun z => q z * Du.representative (ParabolicDerivativeIndex.zero d L) z := by
  funext z
  unfold parabolicWeakMulRepresentative
  rw [Fintype.sum_eq_single
    (default : TimeVelocityMultiIndex.Split (ParabolicDerivativeIndex.zero d L).1)]
  · have hleft : (default : TimeVelocityMultiIndex.Split
        (ParabolicDerivativeIndex.zero d L).1).left = 0 := by
      funext c
      rfl
    have hright : ParabolicDerivativeIndex.splitRight
        (ParabolicDerivativeIndex.zero d L) default =
        ParabolicDerivativeIndex.zero d L := by
      apply Subtype.ext
      funext c
      simp [ParabolicDerivativeIndex.splitRight, TimeVelocityMultiIndex.Split.right]
    rw [hleft, hright]
    simp [TimeVelocityMultiIndex.coordinateIteratedFDeriv_zero]
  · intro b hb
    exact (hb (split_zero_eq b)).elim

private theorem ae_restrict_of_forall_mem
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (S : Set α) (hS : MeasurableSet S) {P : α → Prop} (hP : ∀ x ∈ S, P x) :
    ∀ᵐ x ∂μ.restrict S, P x := by
  filter_upwards [ae_restrict_mem hS] with x hx
  exact hP x hx

private theorem toReal_eLpNorm_mul_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p : ℝ≥0∞} {a f : α → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (ha : AEStronglyMeasurable a μ)
    (hf : MemLp f p μ) (haM : ∀ᵐ x ∂μ, |a x| ≤ M) :
    MemLp (fun x => a x * f x) p μ ∧
      ENNReal.toReal (eLpNorm (fun x => a x * f x) p μ) ≤
        M * ENNReal.toReal (eLpNorm f p μ) := by
  have hmeas : AEStronglyMeasurable (fun x => a x * f x) μ := ha.mul hf.aestronglyMeasurable
  have hpoint : ∀ᵐ x ∂μ, ‖a x * f x‖ ≤ M * ‖f x‖ := by
    filter_upwards [haM] with x hx
    simpa only [Real.norm_eq_abs, abs_mul] using
      mul_le_mul hx le_rfl (abs_nonneg (f x)) hM
  have haf : MemLp (fun x => a x * f x) p μ := MemLp.of_le_mul hf hmeas hpoint
  have hle := eLpNorm_le_mul_eLpNorm_of_ae_le_mul hmeas hpoint p
  have htop : ENNReal.ofReal M * eLpNorm f p μ ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf.eLpNorm_ne_top
  have hr := ENNReal.toReal_mono htop hle
  exact ⟨haf, by simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hM] using hr⟩

private theorem mulTerm_memLp_norm
    {d : ℕ} {U : Set (TimeVelocity d)} (hU : IsOpen U)
    (B : ℝ) (hB : 0 ≤ B) (a f : TimeVelocity d → ℝ)
    (ha : ContinuousOn a U) (haB : ∀ z ∈ U, |a z| ≤ B)
    (hf : ParabolicMemLpOn U 2 f) :
    ParabolicMemLpOn U 2 (fun z => a z * f z) ∧
      ENNReal.toReal (eLpNorm (fun z => a z * f z) 2 (timeVelocityVolumeOn U)) ≤
        B * ENNReal.toReal (eLpNorm f 2 (timeVelocityVolumeOn U)) := by
  have haMeas : AEStronglyMeasurable a (timeVelocityVolumeOn U) :=
    ha.aestronglyMeasurable hU.measurableSet
  have haAE : ∀ᵐ z ∂timeVelocityVolumeOn U, |a z| ≤ B :=
    ae_restrict_of_forall_mem U hU.measurableSet haB
  exact toReal_eLpNorm_mul_le hB haMeas hf haAE

private theorem toReal_eLpNorm_fin_sum_le
    {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    {μ : Measure α} (f : ι → α → ℝ)
    (hf : ∀ i, MemLp (f i) 2 μ) :
    ENNReal.toReal (eLpNorm (fun x => ∑ i, f i x) 2 μ) ≤
      ∑ i, ENNReal.toReal (eLpNorm (f i) 2 μ) := by
  classical
  have hle := eLpNorm_sum_le (f := f) (μ := μ) (s := Finset.univ)
    (show (1 : ℝ≥0∞) ≤ 2 by norm_num)
  have hfun : (∑ i, f i) = fun x => ∑ i, f i x := by
    funext x
    simp only [Finset.sum_apply]
  rw [hfun] at hle
  have htop : (∑ i, eLpNorm (f i) 2 μ) ≠ ∞ := by
    rw [ENNReal.sum_ne_top]
    intro i hi
    exact (hf i).eLpNorm_ne_top
  have hr := ENNReal.toReal_mono htop hle
  rw [ENNReal.toReal_sum (fun i _ => (hf i).eLpNorm_ne_top)] at hr
  exact hr

private def leftAddIndex {d L : ℕ} (beta : ParabolicDerivativeIndex d L)
    (gamma : TimeVelocityMultiIndex.Split beta.1) (c : TimeVelocityCoord d)
    (hadd : (gamma.left + Pi.single c 1).parabolicWeight ≤ L) :
    ParabolicDerivativeIndex d L := ⟨_, hadd⟩

private def rightAddIndex {d L : ℕ} (beta : ParabolicDerivativeIndex d L)
    (gamma : TimeVelocityMultiIndex.Split beta.1) (c : TimeVelocityCoord d)
    (hadd : (gamma.right + Pi.single c 1).parabolicWeight ≤ L) :
    ParabolicDerivativeIndex d L := ⟨_, hadd⟩


private theorem weight_add_time_single {d : ℕ}
    (a : TimeVelocityMultiIndex d) :
    (a + Pi.single (timeCoord d) 1).parabolicWeight =
      a.parabolicWeight + 2 := by
  have ht : (a + Pi.single (timeCoord d) 1).timeOrder = a.timeOrder + 1 := by
    simp [TimeVelocityMultiIndex.timeOrder, timeCoord]
  have hv : (a + Pi.single (timeCoord d) 1).velocity = a.velocity := by
    funext i
    simp [TimeVelocityMultiIndex.velocity, velocityCoord, timeCoord]
  rw [TimeVelocityMultiIndex.parabolicWeight,
    VelocityMultiIndex.parabolicWeight, ht, hv]
  simp [TimeVelocityMultiIndex.parabolicWeight, VelocityMultiIndex.parabolicWeight]
  omega
private theorem weight_add_velocity_single {d : ℕ}
    (a : TimeVelocityMultiIndex d) (i : Fin d) :
    (a + Pi.single (velocityCoord i) 1).parabolicWeight =
      a.parabolicWeight + 1 := by
  simp only [TimeVelocityMultiIndex.parabolicWeight, VelocityMultiIndex.parabolicWeight,
    VelocityMultiIndex.order, TimeVelocityMultiIndex.timeOrder,
    TimeVelocityMultiIndex.velocity, Pi.add_apply]
  rw [Finset.sum_add_distrib]
  simp [velocityCoord, timeCoord, Pi.single_apply]
  omega
/-- Multiplication by a bounded finite-order classical coefficient preserves a
coherent weak parabolic derivative family on an arbitrary open carrier. -/
noncomputable def ParabolicWeakDerivativeFamily.mulContDiffOn
    {d L : ℕ} {U : Set (TimeVelocity d)} (hU : IsOpen U)
    (Bq : ParabolicDerivativeIndex d L → ℝ)
    (hBq : ∀ alpha, 0 ≤ Bq alpha)
    (q : TimeVelocity d → ℝ) (hq : ContDiffOn ℝ L q U)
    (hqBound :
      ∀ (alpha : ParabolicDerivativeIndex d L) z, z ∈ U →
        |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 q z| ≤
          Bq alpha)
    (u : TimeVelocity d → ℝ)
    (Du : ParabolicWeakDerivativeFamily d L U u) :
    ParabolicWeakDerivativeFamily d L U (fun z => q z * u z) where
  representative := parabolicWeakMulRepresentative q Du
  memLp := by
    intro beta
    apply memLp_finset_sum Finset.univ
    intro gamma hgamma
    let a := fun z => (beta.1.choose gamma.left : ℝ) *
      TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left q z
    have hcont : ContinuousOn a U := fun z hz => by
      apply ContinuousAt.continuousWithinAt
      apply continuousAt_const.mul
      exact (coordinateIteratedFDeriv_contDiffAt gamma.left 0 q z
        ((hq.contDiffAt (hU.mem_nhds hz)).of_le (by
          simpa using gamma.order_left_le.trans (index_order_le beta)))).continuousAt
    have hb : ∀ z ∈ U, |a z| ≤
        (beta.1.choose gamma.left : ℝ) *
          Bq (ParabolicDerivativeIndex.splitLeft beta gamma) := by
      intro z hz
      dsimp [a]
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      exact mul_le_mul_of_nonneg_left
        (hqBound (ParabolicDerivativeIndex.splitLeft beta gamma) z hz)
        (Nat.cast_nonneg _)
    exact (mulTerm_memLp_norm hU _
      (mul_nonneg (Nat.cast_nonneg _) (hBq _)) a _ hcont hb (Du.memLp _)).1
  zero_ae := by
    filter_upwards [Du.zero_ae] with z hz
    rw [representative_zero]
    exact congrArg (fun x => q z * x) hz
  hasWeakTimeSucc := by
    classical
    intro beta h
    let c : TimeVelocityCoord d := timeCoord d
    let I := TimeVelocityMultiIndex.Split beta.1
    let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
    let val : I → TimeVelocity d → ℝ := fun gamma z ↦
      (beta.1.choose gamma.left : ℝ) *
        TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left q z *
        Du.representative (ParabolicDerivativeIndex.splitRight beta gamma) z
    let der : I → TimeVelocity d → ℝ := fun gamma z ↦
      (beta.1.choose gamma.left : ℝ) *
        (TimeVelocityMultiIndex.coordinateIteratedFDeriv
            (gamma.left + Pi.single c 1) q z *
            Du.representative (ParabolicDerivativeIndex.splitRight beta gamma) z +
          TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left q z *
            Du.representative (rightAddIndex beta gamma c (by
              have hr := gamma.parabolicWeight_right_le
              rw [show c = timeCoord d from rfl, weight_add_time_single]
              omega)) z)
    have hdata (gamma : I) :
        ParabolicMemLpOn U 2 (val gamma) ∧ ParabolicMemLpOn U 2 (der gamma) ∧
          HasWeakTimeDerivOn U (val gamma) (der gamma) := by
      have hleft : gamma.left.order + 1 ≤ L := by
        have hlo := gamma.order_left_le
        have hob : beta.1.order ≤ beta.1.parabolicWeight := by
          simp [TimeVelocityMultiIndex.order, TimeVelocityMultiIndex.parabolicWeight,
            VelocityMultiIndex.parabolicWeight]
          omega
        omega
      have hC1 : ContDiffOn ℝ 1
          (TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left q) U := by
        intro z hz
        have ht := coordinateIteratedFDeriv_contDiffAt gamma.left 1 q z
          ((hq.contDiffAt (hU.mem_nhds hz)).of_le (by
            exact_mod_cast (show 1 + gamma.left.order ≤ L by omega)))
        simpa using ht.contDiffWithinAt
      have hladd : (gamma.left + Pi.single c 1).parabolicWeight ≤ L := by
        have hl := gamma.parabolicWeight_left_le
        rw [show c = timeCoord d from rfl, weight_add_time_single]
        omega
      have hradd : (gamma.right + Pi.single c 1).parabolicWeight ≤ L := by
        have hr := gamma.parabolicWeight_right_le
        rw [show c = timeCoord d from rfl, weight_add_time_single]
        omega
      have hrsucc : gamma.right.parabolicWeight + 2 ≤ L := by
        have hr := gamma.parabolicWeight_right_le
        omega
      have hrightEq : rightAddIndex beta gamma c hradd =
          ParabolicDerivativeIndex.timeSucc
            (ParabolicDerivativeIndex.splitRight beta gamma) hrsucc := by
        apply Subtype.ext
        rw [ParabolicDerivativeIndex.coe_timeSucc_eq_add_single
          (ParabolicDerivativeIndex.splitRight beta gamma) hrsucc]
        rfl
      have hweak := Du.hasWeakTimeSucc
        (ParabolicDerivativeIndex.splitRight beta gamma) hrsucc
      have hprod := timeC1_mul_hasWeakTimeDerivOn_memLp_eLpNorm_le
        hU
        (Bq (ParabolicDerivativeIndex.splitLeft beta gamma))
        (Bq (leftAddIndex beta gamma c hladd))
        (hBq _) (hBq _)
        (TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left q) hC1
        (by intro z hz; exact hqBound (ParabolicDerivativeIndex.splitLeft beta gamma) z hz)
        (by
          intro z hz
          rw [show timeDerivative
              (TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left q) z =
              TimeVelocityMultiIndex.coordinateIteratedFDeriv
                (gamma.left + Pi.single c 1) q z by
            rw [TimeVelocityMultiIndex.coordinateIteratedFDeriv_add_single_at]
            · simp [timeDerivative, c, timeVelocityBasis_time]
            · exact (hq.contDiffAt (hU.mem_nhds hz)).of_le (by
                exact_mod_cast hleft)]
          exact hqBound (leftAddIndex beta gamma c hladd) z hz)
        (Du.representative (ParabolicDerivativeIndex.splitRight beta gamma))
        (Du.representative (rightAddIndex beta gamma c hradd))
        (Du.memLp _) (Du.memLp _)
        (by simpa only [hrightEq] using hweak)
      have hp := hprod.2.2.2.1
      have hs := hp.smul (beta.1.choose gamma.left : ℝ)
      have hderAE :
          ((beta.1.choose gamma.left : ℝ) • fun z =>
            TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left q z *
                Du.representative (rightAddIndex beta gamma c hradd) z +
              timeDerivative
                  (TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left q) z *
                Du.representative (ParabolicDerivativeIndex.splitRight beta gamma) z) =ᵐ[
            timeVelocityVolumeOn U] der gamma := by
        filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
        have hd := TimeVelocityMultiIndex.coordinateIteratedFDeriv_add_single_at
          gamma.left c q z ((hq.contDiffAt (hU.mem_nhds hz)).of_le (by
            exact_mod_cast hleft))
        simp only [der, Pi.smul_apply, smul_eq_mul, mul_add]
        rw [hd]
        simp [timeDerivative, c, timeVelocityBasis_time]
        ring
      have hvmem : ParabolicMemLpOn U 2 (val gamma) := by
        simpa only [val, Pi.smul_apply, smul_eq_mul, mul_assoc] using
          hprod.2.1.const_mul (beta.1.choose gamma.left : ℝ)
      have hdmem : ParabolicMemLpOn U 2 (der gamma) := by
        exact (memLp_congr_ae hderAE).mp
          (hprod.2.2.1.const_mul (beta.1.choose gamma.left : ℝ))
      refine ⟨hvmem, hdmem, ?_⟩
      apply hs.congr_ae
      · filter_upwards [] with z
        simp [val]
        ring
      · exact hderAE
    have hterm (gamma : I) := (hdata gamma).2.2
    have hvalLoc (gamma : I) : LocallyIntegrableOn (val gamma) U volume :=
      (hdata gamma).1.locallyIntegrableOn (by norm_num)
    have hderMem (gamma : I) : ParabolicMemLpOn U 2 (der gamma) := (hdata gamma).2.1
    have hderLoc (gamma : I) : LocallyIntegrableOn (der gamma) U volume :=
      (hderMem gamma).locallyIntegrableOn (by norm_num)
    have hsum := HasWeakTimeDerivOn.fin_sum
      (u := fun j => val (e.symm j)) (du := fun j => der (e.symm j))
      (fun j => hterm (e.symm j)) (fun j => hvalLoc (e.symm j))
      (fun j => hderLoc (e.symm j))
    have hvalsum : (fun z => ∑ j, val (e.symm j) z) =
        parabolicWeakMulRepresentative q Du beta := by
      funext z
      unfold parabolicWeakMulRepresentative
      exact Equiv.sum_comp e.symm (fun gamma => val gamma z)
    have hdersum : (fun z => ∑ j, der (e.symm j) z) =
        parabolicWeakMulRepresentative q Du
          (ParabolicDerivativeIndex.timeSucc beta h) := by
      funext z
      unfold parabolicWeakMulRepresentative
      rw [Equiv.sum_comp e.symm (fun gamma => der gamma z)]
      let F : TimeVelocityMultiIndex d → TimeVelocityMultiIndex d → ℝ := fun a b =>
        if hb : b.parabolicWeight ≤ L then
          TimeVelocityMultiIndex.coordinateIteratedFDeriv a q z *
            Du.representative ⟨b, hb⟩ z
        else 0
      calc
        (∑ gamma : I, der gamma z) =
            ∑ gamma : I, (beta.1.choose gamma.left : ℝ) *
              (F (gamma.left + Pi.single c 1) gamma.right +
                F gamma.left (gamma.right + Pi.single c 1)) := by
          apply Finset.sum_congr rfl
          intro gamma hgamma
          have hr0 : gamma.right.parabolicWeight ≤ L :=
            gamma.parabolicWeight_right_le.trans beta.2
          have hr1 : (gamma.right + Pi.single c 1).parabolicWeight ≤ L := by
            rw [show c = timeCoord d from rfl, weight_add_time_single]
            have hr := gamma.parabolicWeight_right_le
            omega
          simp only [der, F, dif_pos hr0, dif_pos hr1]
          congr 3
        _ = ∑ delta : TimeVelocityMultiIndex.Split
              (ParabolicDerivativeIndex.timeSucc beta h).1,
            ((ParabolicDerivativeIndex.timeSucc beta h).1.choose delta.left : ℝ) *
              F delta.left delta.right :=
          by
            rw [ParabolicDerivativeIndex.coe_timeSucc_eq_add_single]
            exact TimeVelocityMultiIndex.sum_choose_split_add_single beta.1 c F
        _ = ∑ delta : TimeVelocityMultiIndex.Split
              (ParabolicDerivativeIndex.timeSucc beta h).1,
            ((ParabolicDerivativeIndex.timeSucc beta h).1.choose delta.left : ℝ) *
              TimeVelocityMultiIndex.coordinateIteratedFDeriv delta.left q z *
                Du.representative
                  (ParabolicDerivativeIndex.splitRight
                    (ParabolicDerivativeIndex.timeSucc beta h) delta) z := by
          apply Finset.sum_congr rfl
          intro delta hdelta
          have hdr : delta.right.parabolicWeight ≤ L :=
            delta.parabolicWeight_right_le.trans
              (ParabolicDerivativeIndex.timeSucc beta h).2
          simp only [F, dif_pos hdr, mul_assoc]
          congr 2
    rw [hvalsum, hdersum] at hsum
    exact hsum

  hasWeakVelocitySucc := by
    classical
    intro beta i h
    let c : TimeVelocityCoord d := velocityCoord i
    let I := TimeVelocityMultiIndex.Split beta.1
    let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
    let val : I → TimeVelocity d → ℝ := fun gamma z ↦
      (beta.1.choose gamma.left : ℝ) *
        TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left q z *
        Du.representative (ParabolicDerivativeIndex.splitRight beta gamma) z
    let der : I → TimeVelocity d → ℝ := fun gamma z ↦
      (beta.1.choose gamma.left : ℝ) *
        (TimeVelocityMultiIndex.coordinateIteratedFDeriv
            (gamma.left + Pi.single c 1) q z *
            Du.representative (ParabolicDerivativeIndex.splitRight beta gamma) z +
          TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left q z *
            Du.representative (rightAddIndex beta gamma c (by
              have hr := gamma.parabolicWeight_right_le
              rw [show c = velocityCoord i from rfl, weight_add_velocity_single]
              omega)) z)
    have hdata (gamma : I) :
        ParabolicMemLpOn U 2 (val gamma) ∧ ParabolicMemLpOn U 2 (der gamma) ∧
          HasWeakVelocityPartialDerivOn U i (val gamma) (der gamma) := by
      have hleft : gamma.left.order + 1 ≤ L := by
        have hlo := gamma.order_left_le
        have hob : beta.1.order ≤ beta.1.parabolicWeight := by
          simp [TimeVelocityMultiIndex.order, TimeVelocityMultiIndex.parabolicWeight,
            VelocityMultiIndex.parabolicWeight]
          omega
        omega
      have hC1 : ContDiffOn ℝ 1
          (TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left q) U := by
        intro z hz
        have ht := coordinateIteratedFDeriv_contDiffAt gamma.left 1 q z
          ((hq.contDiffAt (hU.mem_nhds hz)).of_le (by
            exact_mod_cast (show 1 + gamma.left.order ≤ L by omega)))
        simpa using ht.contDiffWithinAt
      have hladd : (gamma.left + Pi.single c 1).parabolicWeight ≤ L := by
        have hl := gamma.parabolicWeight_left_le
        rw [show c = velocityCoord i from rfl, weight_add_velocity_single]
        omega
      have hradd : (gamma.right + Pi.single c 1).parabolicWeight ≤ L := by
        have hr := gamma.parabolicWeight_right_le
        rw [show c = velocityCoord i from rfl, weight_add_velocity_single]
        omega
      have hrsucc : gamma.right.parabolicWeight + 1 ≤ L := by
        have hr := gamma.parabolicWeight_right_le
        omega
      have hrightEq : rightAddIndex beta gamma c hradd =
          ParabolicDerivativeIndex.velocitySucc
            (ParabolicDerivativeIndex.splitRight beta gamma) i (by
              exact hrsucc) := by
        apply Subtype.ext
        rw [ParabolicDerivativeIndex.coe_velocitySucc_eq_add_single
          (ParabolicDerivativeIndex.splitRight beta gamma) i hrsucc]
        rfl
      have hweak := Du.hasWeakVelocitySucc
        (ParabolicDerivativeIndex.splitRight beta gamma) i
        hrsucc
      have hprod := velocityC1_mul_hasWeakVelocityPartialDerivOn_memLp_eLpNorm_le
        hU i
        (Bq (ParabolicDerivativeIndex.splitLeft beta gamma))
        (Bq (leftAddIndex beta gamma c hladd))
        (hBq _) (hBq _)
        (TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left q) hC1
        (by intro z hz; exact hqBound (ParabolicDerivativeIndex.splitLeft beta gamma) z hz)
        (by
          intro z hz
          rw [show velocityGradient
              (TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left q) z i =
              TimeVelocityMultiIndex.coordinateIteratedFDeriv
                (gamma.left + Pi.single c 1) q z by
            rw [TimeVelocityMultiIndex.coordinateIteratedFDeriv_add_single_at]
            · simp [velocityGradient, c, timeVelocityBasis_velocity, PDE.basisVec]
            · exact (hq.contDiffAt (hU.mem_nhds hz)).of_le (by
                exact_mod_cast hleft)]
          exact hqBound (leftAddIndex beta gamma c hladd) z hz)
        (Du.representative (ParabolicDerivativeIndex.splitRight beta gamma))
        (Du.representative (rightAddIndex beta gamma c hradd))
        (Du.memLp _) (Du.memLp _)
        (by simpa only [hrightEq] using hweak)
      have hp := hprod.2.2.2.1
      have hs := hp.smul (beta.1.choose gamma.left : ℝ)
      have hderAE :
          ((beta.1.choose gamma.left : ℝ) • fun z =>
            TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left q z *
                Du.representative (rightAddIndex beta gamma c hradd) z +
              velocityGradient
                  (TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left q) z i *
                Du.representative (ParabolicDerivativeIndex.splitRight beta gamma) z) =ᵐ[
            timeVelocityVolumeOn U] der gamma := by
        filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
        have hd := TimeVelocityMultiIndex.coordinateIteratedFDeriv_add_single_at
          gamma.left c q z ((hq.contDiffAt (hU.mem_nhds hz)).of_le (by
            exact_mod_cast hleft))
        simp only [der, Pi.smul_apply, smul_eq_mul, mul_add]
        rw [hd]
        simp [velocityGradient, c, timeVelocityBasis_velocity, PDE.basisVec]
        ring
      have hvmem : ParabolicMemLpOn U 2 (val gamma) := by
        simpa only [val, Pi.smul_apply, smul_eq_mul, mul_assoc] using
          hprod.2.1.const_mul (beta.1.choose gamma.left : ℝ)
      have hdmem : ParabolicMemLpOn U 2 (der gamma) := by
        exact (memLp_congr_ae hderAE).mp
          (hprod.2.2.1.const_mul (beta.1.choose gamma.left : ℝ))
      refine ⟨hvmem, hdmem, ?_⟩
      apply hs.congr_ae
      · filter_upwards [] with z
        simp [val]
        ring
      · exact hderAE
    have hterm (gamma : I) := (hdata gamma).2.2
    have hvalLoc (gamma : I) : LocallyIntegrableOn (val gamma) U volume :=
      (hdata gamma).1.locallyIntegrableOn (by norm_num)
    have hderMem (gamma : I) : ParabolicMemLpOn U 2 (der gamma) := (hdata gamma).2.1
    have hderLoc (gamma : I) : LocallyIntegrableOn (der gamma) U volume :=
      (hderMem gamma).locallyIntegrableOn (by norm_num)
    have hsum := HasWeakVelocityPartialDerivOn.fin_sum
      (u := fun j => val (e.symm j)) (du := fun j => der (e.symm j))
      (fun j => hterm (e.symm j)) (fun j => hvalLoc (e.symm j))
      (fun j => hderLoc (e.symm j))
    have hvalsum : (fun z => ∑ j, val (e.symm j) z) =
        parabolicWeakMulRepresentative q Du beta := by
      funext z
      unfold parabolicWeakMulRepresentative
      exact Equiv.sum_comp e.symm (fun gamma => val gamma z)
    have hdersum : (fun z => ∑ j, der (e.symm j) z) =
        parabolicWeakMulRepresentative q Du
          (ParabolicDerivativeIndex.velocitySucc beta i h) := by
      funext z
      unfold parabolicWeakMulRepresentative
      rw [Equiv.sum_comp e.symm (fun gamma => der gamma z)]
      let F : TimeVelocityMultiIndex d → TimeVelocityMultiIndex d → ℝ := fun a b =>
        if hb : b.parabolicWeight ≤ L then
          TimeVelocityMultiIndex.coordinateIteratedFDeriv a q z *
            Du.representative ⟨b, hb⟩ z
        else 0
      calc
        (∑ gamma : I, der gamma z) =
            ∑ gamma : I, (beta.1.choose gamma.left : ℝ) *
              (F (gamma.left + Pi.single c 1) gamma.right +
                F gamma.left (gamma.right + Pi.single c 1)) := by
          apply Finset.sum_congr rfl
          intro gamma hgamma
          have hr0 : gamma.right.parabolicWeight ≤ L :=
            gamma.parabolicWeight_right_le.trans beta.2
          have hr1 : (gamma.right + Pi.single c 1).parabolicWeight ≤ L := by
            rw [show c = velocityCoord i from rfl, weight_add_velocity_single]
            have hr := gamma.parabolicWeight_right_le
            omega
          simp only [der, F, dif_pos hr0, dif_pos hr1]
          congr 3
        _ = ∑ delta : TimeVelocityMultiIndex.Split
              (ParabolicDerivativeIndex.velocitySucc beta i h).1,
            ((ParabolicDerivativeIndex.velocitySucc beta i h).1.choose delta.left : ℝ) *
              F delta.left delta.right :=
          by
            rw [ParabolicDerivativeIndex.coe_velocitySucc_eq_add_single]
            exact TimeVelocityMultiIndex.sum_choose_split_add_single beta.1 c F
        _ = ∑ delta : TimeVelocityMultiIndex.Split
              (ParabolicDerivativeIndex.velocitySucc beta i h).1,
            ((ParabolicDerivativeIndex.velocitySucc beta i h).1.choose delta.left : ℝ) *
              TimeVelocityMultiIndex.coordinateIteratedFDeriv delta.left q z *
                Du.representative
                  (ParabolicDerivativeIndex.splitRight
                    (ParabolicDerivativeIndex.velocitySucc beta i h) delta) z := by
          apply Finset.sum_congr rfl
          intro delta hdelta
          have hdr : delta.right.parabolicWeight ≤ L :=
            delta.parabolicWeight_right_le.trans
              (ParabolicDerivativeIndex.velocitySucc beta i h).2
          simp only [F, dif_pos hdr, mul_assoc]
          congr 2
    rw [hvalsum, hdersum] at hsum
    exact hsum

/-- The selected representative of `mulContDiffOn` is definitionally the
literal multi-index Leibniz sum. -/
@[simp] theorem ParabolicWeakDerivativeFamily.mulContDiffOn_representative
    {d L : ℕ} {U : Set (TimeVelocity d)} (hU : IsOpen U)
    (Bq : ParabolicDerivativeIndex d L → ℝ)
    (hBq : ∀ alpha, 0 ≤ Bq alpha)
    (q : TimeVelocity d → ℝ) (hq : ContDiffOn ℝ L q U)
    (hqBound :
      ∀ (alpha : ParabolicDerivativeIndex d L) z, z ∈ U →
        |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 q z| ≤
          Bq alpha)
    (u : TimeVelocity d → ℝ)
    (Du : ParabolicWeakDerivativeFamily d L U u)
    (beta : ParabolicDerivativeIndex d L) :
    (Du.mulContDiffOn hU Bq hBq q hq hqBound).representative beta =
      parabolicWeakMulRepresentative q Du beta :=
  rfl

/-- The sharp componentwise `L²` norm bound for the weak Leibniz family. -/
theorem ParabolicWeakDerivativeFamily.mulContDiffOn_eLpNorm_toReal_le
    {d L : ℕ} {U : Set (TimeVelocity d)} (hU : IsOpen U)
    (Bq : ParabolicDerivativeIndex d L → ℝ)
    (hBq : ∀ alpha, 0 ≤ Bq alpha)
    (q : TimeVelocity d → ℝ) (hq : ContDiffOn ℝ L q U)
    (hqBound :
      ∀ (alpha : ParabolicDerivativeIndex d L) z, z ∈ U →
        |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 q z| ≤
          Bq alpha)
    (u : TimeVelocity d → ℝ)
    (Du : ParabolicWeakDerivativeFamily d L U u)
    (beta : ParabolicDerivativeIndex d L) :
    ENNReal.toReal
        (eLpNorm
          ((Du.mulContDiffOn hU Bq hBq q hq hqBound).representative beta)
          2 (timeVelocityVolumeOn U)) ≤
      ∑ gamma : TimeVelocityMultiIndex.Split beta.1,
        (beta.1.choose gamma.left : ℝ) *
          Bq (ParabolicDerivativeIndex.splitLeft beta gamma) *
          ENNReal.toReal
            (eLpNorm
              (Du.representative
                (ParabolicDerivativeIndex.splitRight beta gamma))
              2 (timeVelocityVolumeOn U)) := by
  let term := fun gamma : TimeVelocityMultiIndex.Split beta.1 => fun z =>
    (beta.1.choose gamma.left : ℝ) *
      TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left q z *
      Du.representative (ParabolicDerivativeIndex.splitRight beta gamma) z
  have hterm (gamma : TimeVelocityMultiIndex.Split beta.1) :
      ParabolicMemLpOn U 2 (term gamma) ∧
        ENNReal.toReal (eLpNorm (term gamma) 2 (timeVelocityVolumeOn U)) ≤
          (beta.1.choose gamma.left : ℝ) *
            Bq (ParabolicDerivativeIndex.splitLeft beta gamma) *
            ENNReal.toReal (eLpNorm
              (Du.representative (ParabolicDerivativeIndex.splitRight beta gamma))
              2 (timeVelocityVolumeOn U)) := by
    let a := fun z => (beta.1.choose gamma.left : ℝ) *
      TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left q z
    have hcont : ContinuousOn a U := fun z hz => by
      apply ContinuousAt.continuousWithinAt
      apply continuousAt_const.mul
      exact (coordinateIteratedFDeriv_contDiffAt gamma.left 0 q z
        ((hq.contDiffAt (hU.mem_nhds hz)).of_le (by
          simpa using gamma.order_left_le.trans (index_order_le beta)))).continuousAt
    have hb : ∀ z ∈ U, |a z| ≤
        (beta.1.choose gamma.left : ℝ) *
          Bq (ParabolicDerivativeIndex.splitLeft beta gamma) := by
      intro z hz
      dsimp [a]
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      exact mul_le_mul_of_nonneg_left
        (hqBound (ParabolicDerivativeIndex.splitLeft beta gamma) z hz)
        (Nat.cast_nonneg _)
    simpa [term, a] using mulTerm_memLp_norm hU _
      (mul_nonneg (Nat.cast_nonneg _) (hBq _)) a _ hcont hb (Du.memLp _)
  calc
    _ = ENNReal.toReal (eLpNorm (fun z => ∑ gamma, term gamma z) 2
          (timeVelocityVolumeOn U)) := by rfl
    _ ≤ ∑ gamma, ENNReal.toReal
          (eLpNorm (term gamma) 2 (timeVelocityVolumeOn U)) :=
      toReal_eLpNorm_fin_sum_le term (fun gamma => (hterm gamma).1)
    _ ≤ _ := Finset.sum_le_sum fun gamma _ => (hterm gamma).2

end HypoellipticAleksandrov.Parabolic
