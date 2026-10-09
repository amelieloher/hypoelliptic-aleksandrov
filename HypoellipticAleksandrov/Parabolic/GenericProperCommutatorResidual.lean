module

public import HypoellipticAleksandrov.Parabolic.ProperSplitIndexArithmetic
public import HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamilyLeibniz
public import HypoellipticAleksandrov.Coefficients.Ellipticity
public import HypoellipticAleksandrov.Analysis.BoundedMultiplierLp

/-!
# Generic proper commutator residual

This module isolates and estimates the proper coefficient-derivative terms in
a differentiated scalar parabolic equation.  The right factors use only one
additional unit of parabolic weight.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped BigOperators

/-- The source derivative minus all proper coefficient commutators at one
bounded parabolic multi-index. -/
noncomputable def properDifferentiatedScalarCommutatorResidual
    {d M : ℕ} {U : Set (TimeVelocity d)}
    {u : TimeVelocity d → ℝ} {F : ℝ → PDE.Vec d → ℝ}
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ)
    (D : ParabolicWeakDerivativeFamily d (M + 1) U u)
    (E : ParabolicWeakDerivativeFamily d M U
      (fun z : TimeVelocity d => F z.1 z.2))
    (beta : ParabolicDerivativeIndex d M) : TimeVelocity d → ℝ :=
  fun z =>
    E.representative beta z -
      (∑ i, ∑ j, ∑ gamma : TimeVelocityMultiIndex.Split beta.1,
        if hproper : gamma.left ≠ 0 then
          (beta.1.choose gamma.left : ℝ) *
            TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left
              (fun x : TimeVelocity d => a x.1 x.2 i j) z *
            D.representative
              (ParabolicDerivativeIndex.properSplitRightVelocityTwo
                beta gamma hproper j i) z
        else 0) -
      (∑ j, ∑ gamma : TimeVelocityMultiIndex.Split beta.1,
        if hproper : gamma.left ≠ 0 then
          (beta.1.choose gamma.left : ℝ) *
            TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left
              (fun x : TimeVelocity d => b x.1 x.2 j) z *
            D.representative
              (ParabolicDerivativeIndex.properSplitRightVelocity
                beta gamma hproper j) z
        else 0) -
      (∑ gamma : TimeVelocityMultiIndex.Split beta.1,
        if hproper : gamma.left ≠ 0 then
          (beta.1.choose gamma.left : ℝ) *
            TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left
              (fun x : TimeVelocity d => c x.1 x.2) z *
            D.representative
              (ParabolicDerivativeIndex.properSplitRightValue
                beta gamma hproper) z
        else 0)

private theorem coordinateIteratedFDeriv_continuousOn
    {d M : ℕ} {U : Set (TimeVelocity d)} (hU : IsOpen U)
    (q : TimeVelocity d → ℝ) (hq : ContDiffOn ℝ M q U)
    (alpha : TimeVelocityMultiIndex d) (halpha : alpha.order ≤ M) :
    ContinuousOn (TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha q) U := by
  intro z hz
  apply ContinuousAt.continuousWithinAt
  unfold TimeVelocityMultiIndex.coordinateIteratedFDeriv
  have hi := (hq.contDiffAt (hU.mem_nhds hz)).iteratedFDeriv_right
    (m := 0) (i := alpha.coordinateList.length) (by simpa using halpha)
  exact (contDiffAt_const (c := ContinuousMultilinearMap.apply ℝ _ _
    (fun i ↦ timeVelocityBasis (alpha.coordinateList.get i)))).clm_apply hi |>.continuousAt

private theorem splitLeft_order_le
    {d M : ℕ} (beta : ParabolicDerivativeIndex d M)
    (gamma : TimeVelocityMultiIndex.Split beta.1) :
    gamma.left.order ≤ M := by
  have horder_weight : beta.1.order ≤ beta.1.parabolicWeight := by
    simp [TimeVelocityMultiIndex.order, TimeVelocityMultiIndex.timeOrder,
      TimeVelocityMultiIndex.velocity, VelocityMultiIndex.order,
      TimeVelocityMultiIndex.parabolicWeight, VelocityMultiIndex.parabolicWeight]
    omega
  exact gamma.order_left_le.trans (horder_weight.trans beta.2)

private theorem ae_restrict_of_forall_mem
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (S : Set α) (hS : MeasurableSet S) {P : α → Prop} (hP : ∀ x ∈ S, P x) :
    ∀ᵐ x ∂μ.restrict S, P x := by
  filter_upwards [ae_restrict_mem hS] with x hx
  exact hP x hx

private theorem properAtom_memLp_and_eLpNorm_toReal_le
    {d M : ℕ} (U : Set (TimeVelocity d)) (hU : IsOpen U)
    (q : TimeVelocity d → ℝ) (hq : ContDiffOn ℝ M q U)
    (B : ParabolicDerivativeIndex d M → ℝ)
    (hB : ∀ alpha, 0 ≤ B alpha)
    (hqBound : ∀ alpha z, z ∈ U →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 q z| ≤ B alpha)
    (beta : ParabolicDerivativeIndex d M)
    (gamma : TimeVelocityMultiIndex.Split beta.1)
    (f : gamma.left ≠ 0 → TimeVelocity d → ℝ)
    (hf : ∀ hproper, ParabolicMemLpOn U 2 (f hproper)) :
    ParabolicMemLpOn U 2 (fun z =>
      if hproper : gamma.left ≠ 0 then
        (beta.1.choose gamma.left : ℝ) *
          TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left q z *
          f hproper z
      else 0) ∧
    ENNReal.toReal (eLpNorm (fun z =>
      if hproper : gamma.left ≠ 0 then
        (beta.1.choose gamma.left : ℝ) *
          TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left q z *
          f hproper z
      else 0) 2 (timeVelocityVolumeOn U)) ≤
      if hproper : gamma.left ≠ 0 then
        (beta.1.choose gamma.left : ℝ) *
          B (ParabolicDerivativeIndex.splitLeft beta gamma) *
          ENNReal.toReal (eLpNorm (f hproper) 2 (timeVelocityVolumeOn U))
      else 0 := by
  classical
  by_cases hproper : gamma.left ≠ 0
  · simp only [dif_pos hproper]
    let multiplier := fun z : TimeVelocity d =>
      (beta.1.choose gamma.left : ℝ) *
        TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left q z
    have hcontinuous : ContinuousOn multiplier U :=
      continuousOn_const.mul (coordinateIteratedFDeriv_continuousOn hU q hq gamma.left
        (splitLeft_order_le beta gamma))
    have hmeas : AEStronglyMeasurable multiplier (timeVelocityVolumeOn U) :=
      hcontinuous.aestronglyMeasurable hU.measurableSet
    have hbound : ∀ᵐ z ∂timeVelocityVolumeOn U,
        |multiplier z| ≤ (beta.1.choose gamma.left : ℝ) *
          B (ParabolicDerivativeIndex.splitLeft beta gamma) :=
      ae_restrict_of_forall_mem U hU.measurableSet fun z hz => by
        dsimp [multiplier]
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
        exact mul_le_mul_of_nonneg_left
          (hqBound (ParabolicDerivativeIndex.splitLeft beta gamma) z hz)
          (Nat.cast_nonneg _)
    simpa only [multiplier] using
      HypoellipticAleksandrov.Analysis.memLp_mul_eLpNorm_toReal_le_of_ae_abs_le
        (mul_nonneg (Nat.cast_nonneg _) (hB _)) hmeas (hf hproper) hbound
  · simp only [dif_neg hproper]
    exact ⟨MemLp.zero', by simp⟩

private theorem eLpNorm_fin_sum_toReal_le
    {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    {μ : Measure α} (f : ι → α → ℝ)
    (hf : ∀ i, MemLp (f i) 2 μ) :
    ENNReal.toReal (eLpNorm (fun x => ∑ i, f i x) 2 μ) ≤
      ∑ i, ENNReal.toReal (eLpNorm (f i) 2 μ) := by
  classical
  have hle : eLpNorm (∑ i, f i) 2 μ ≤ ∑ i, eLpNorm (f i) 2 μ :=
    eLpNorm_sum_le (s := Finset.univ) (by norm_num)
  have hfun : (∑ i, f i) = fun x => ∑ i, f i x := by
    funext x
    simp only [Finset.sum_apply]
  rw [hfun] at hle
  have htop : (∑ i, eLpNorm (f i) 2 μ) ≠ ⊤ := by
    rw [ENNReal.sum_ne_top]
    intro i hi
    exact (hf i).eLpNorm_ne_top
  have hr := ENNReal.toReal_mono htop hle
  rw [ENNReal.toReal_sum (fun i _ => (hf i).eLpNorm_ne_top)] at hr
  exact hr

private theorem eLpNorm_sub_toReal_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f g : α → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ENNReal.toReal (eLpNorm (fun x => f x - g x) 2 μ) ≤
      ENNReal.toReal (eLpNorm f 2 μ) + ENNReal.toReal (eLpNorm g 2 μ) := by
  have hle : eLpNorm (f - g) 2 μ ≤ eLpNorm f 2 μ + eLpNorm g 2 μ :=
    eLpNorm_sub_le (by norm_num)
  have htop : eLpNorm f 2 μ + eLpNorm g 2 μ ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hf.eLpNorm_ne_top, hg.eLpNorm_ne_top⟩
  have hr := ENNReal.toReal_mono htop hle
  rw [ENNReal.toReal_add hf.eLpNorm_ne_top hg.eLpNorm_ne_top] at hr
  exact hr

/-- The proper commutator residual is in restricted `L²` and obeys the literal
componentwise convolution bound with no principal split. -/
theorem properDifferentiatedScalarCommutatorResidual_memLp_and_eLpNorm_toReal_le
    {d M : ℕ} (U : Set (TimeVelocity d)) (hU : IsOpen U)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ)
    (u : TimeVelocity d → ℝ)
    (F : ℝ → PDE.Vec d → ℝ)
    (D : ParabolicWeakDerivativeFamily d (M + 1) U u)
    (E : ParabolicWeakDerivativeFamily d M U
      (fun z : TimeVelocity d => F z.1 z.2))
    (Ba : Fin d → Fin d → ParabolicDerivativeIndex d M → ℝ)
    (Bb : Fin d → ParabolicDerivativeIndex d M → ℝ)
    (Bc : ParabolicDerivativeIndex d M → ℝ)
    (hBa : ∀ i j alpha, 0 ≤ Ba i j alpha)
    (hBb : ∀ j alpha, 0 ≤ Bb j alpha)
    (hBc : ∀ alpha, 0 ≤ Bc alpha)
    (ha : ∀ i j, ContDiffOn ℝ M
      (fun z : TimeVelocity d => a z.1 z.2 i j) U)
    (hb : ∀ j, ContDiffOn ℝ M
      (fun z : TimeVelocity d => b z.1 z.2 j) U)
    (hc : ContDiffOn ℝ M
      (fun z : TimeVelocity d => c z.1 z.2) U)
    (haBound : ∀ i j alpha z, z ∈ U →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
        (fun x : TimeVelocity d => a x.1 x.2 i j) z| ≤ Ba i j alpha)
    (hbBound : ∀ j alpha z, z ∈ U →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
        (fun x : TimeVelocity d => b x.1 x.2 j) z| ≤ Bb j alpha)
    (hcBound : ∀ alpha z, z ∈ U →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
        (fun x : TimeVelocity d => c x.1 x.2) z| ≤ Bc alpha)
    (beta : ParabolicDerivativeIndex d M) :
    ParabolicMemLpOn U 2
      (properDifferentiatedScalarCommutatorResidual a b c D E beta) ∧
    ENNReal.toReal (eLpNorm
      (properDifferentiatedScalarCommutatorResidual a b c D E beta)
      2 (timeVelocityVolumeOn U)) ≤
      ENNReal.toReal (eLpNorm (E.representative beta) 2
        (timeVelocityVolumeOn U)) +
      (∑ i, ∑ j, ∑ gamma : TimeVelocityMultiIndex.Split beta.1,
        if hproper : gamma.left ≠ 0 then
          (beta.1.choose gamma.left : ℝ) *
            Ba i j (ParabolicDerivativeIndex.splitLeft beta gamma) *
            ENNReal.toReal (eLpNorm
              (D.representative
                (ParabolicDerivativeIndex.properSplitRightVelocityTwo
                  beta gamma hproper j i)) 2 (timeVelocityVolumeOn U))
        else 0) +
      (∑ j, ∑ gamma : TimeVelocityMultiIndex.Split beta.1,
        if hproper : gamma.left ≠ 0 then
          (beta.1.choose gamma.left : ℝ) *
            Bb j (ParabolicDerivativeIndex.splitLeft beta gamma) *
            ENNReal.toReal (eLpNorm
              (D.representative
                (ParabolicDerivativeIndex.properSplitRightVelocity
                  beta gamma hproper j)) 2 (timeVelocityVolumeOn U))
        else 0) +
      (∑ gamma : TimeVelocityMultiIndex.Split beta.1,
        if hproper : gamma.left ≠ 0 then
          (beta.1.choose gamma.left : ℝ) *
            Bc (ParabolicDerivativeIndex.splitLeft beta gamma) *
            ENNReal.toReal (eLpNorm
              (D.representative
                (ParabolicDerivativeIndex.properSplitRightValue
                  beta gamma hproper)) 2 (timeVelocityVolumeOn U))
        else 0) := by
  classical
  let A : TimeVelocity d → ℝ := fun z =>
    ∑ i, ∑ j, ∑ gamma : TimeVelocityMultiIndex.Split beta.1,
      if hproper : gamma.left ≠ 0 then
        (beta.1.choose gamma.left : ℝ) *
          TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left
            (fun x : TimeVelocity d => a x.1 x.2 i j) z *
          D.representative
            (ParabolicDerivativeIndex.properSplitRightVelocityTwo
              beta gamma hproper j i) z
      else 0
  let B : TimeVelocity d → ℝ := fun z =>
    ∑ j, ∑ gamma : TimeVelocityMultiIndex.Split beta.1,
      if hproper : gamma.left ≠ 0 then
        (beta.1.choose gamma.left : ℝ) *
          TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left
            (fun x : TimeVelocity d => b x.1 x.2 j) z *
          D.representative
            (ParabolicDerivativeIndex.properSplitRightVelocity
              beta gamma hproper j) z
      else 0
  let C : TimeVelocity d → ℝ := fun z =>
    ∑ gamma : TimeVelocityMultiIndex.Split beta.1,
      if hproper : gamma.left ≠ 0 then
        (beta.1.choose gamma.left : ℝ) *
          TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left
            (fun x : TimeVelocity d => c x.1 x.2) z *
          D.representative
            (ParabolicDerivativeIndex.properSplitRightValue
              beta gamma hproper) z
      else 0
  have hAatom (i j : Fin d) (gamma : TimeVelocityMultiIndex.Split beta.1) :=
    properAtom_memLp_and_eLpNorm_toReal_le U hU
      (fun x : TimeVelocity d => a x.1 x.2 i j) (ha i j) (Ba i j) (hBa i j)
      (haBound i j) beta gamma
      (fun hproper => D.representative
        (ParabolicDerivativeIndex.properSplitRightVelocityTwo
          beta gamma hproper j i))
      (fun hproper => D.memLp _)
  have hBatom (j : Fin d) (gamma : TimeVelocityMultiIndex.Split beta.1) :=
    properAtom_memLp_and_eLpNorm_toReal_le U hU
      (fun x : TimeVelocity d => b x.1 x.2 j) (hb j) (Bb j) (hBb j)
      (hbBound j) beta gamma
      (fun hproper => D.representative
        (ParabolicDerivativeIndex.properSplitRightVelocity beta gamma hproper j))
      (fun hproper => D.memLp _)
  have hCatom (gamma : TimeVelocityMultiIndex.Split beta.1) :=
    properAtom_memLp_and_eLpNorm_toReal_le U hU
      (fun x : TimeVelocity d => c x.1 x.2) hc Bc hBc hcBound beta gamma
      (fun hproper => D.representative
        (ParabolicDerivativeIndex.properSplitRightValue beta gamma hproper))
      (fun hproper => D.memLp _)
  have hAmem : ParabolicMemLpOn U 2 A := by
    apply memLp_finset_sum Finset.univ
    intro i hi
    apply memLp_finset_sum Finset.univ
    intro j hj
    apply memLp_finset_sum Finset.univ
    intro gamma hgamma
    exact (hAatom i j gamma).1
  have hBmem : ParabolicMemLpOn U 2 B := by
    apply memLp_finset_sum Finset.univ
    intro j hj
    apply memLp_finset_sum Finset.univ
    intro gamma hgamma
    exact (hBatom j gamma).1
  have hCmem : ParabolicMemLpOn U 2 C :=
    memLp_finset_sum Finset.univ fun gamma _ => (hCatom gamma).1
  have hAnorm : ENNReal.toReal (eLpNorm A 2 (timeVelocityVolumeOn U)) ≤
      ∑ i, ∑ j, ∑ gamma : TimeVelocityMultiIndex.Split beta.1,
        if hproper : gamma.left ≠ 0 then
          (beta.1.choose gamma.left : ℝ) *
            Ba i j (ParabolicDerivativeIndex.splitLeft beta gamma) *
            ENNReal.toReal (eLpNorm
              (D.representative
                (ParabolicDerivativeIndex.properSplitRightVelocityTwo
                  beta gamma hproper j i)) 2 (timeVelocityVolumeOn U))
        else 0 := by
    calc
      _ ≤ ∑ i, ENNReal.toReal (eLpNorm (fun z => ∑ j, ∑ gamma,
            if hproper : gamma.left ≠ 0 then
              (beta.1.choose gamma.left : ℝ) *
                TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left
                  (fun x : TimeVelocity d => a x.1 x.2 i j) z *
                D.representative
                  (ParabolicDerivativeIndex.properSplitRightVelocityTwo
                    beta gamma hproper j i) z
            else 0) 2 (timeVelocityVolumeOn U)) :=
        eLpNorm_fin_sum_toReal_le _ fun i =>
          memLp_finset_sum Finset.univ fun j _ =>
            memLp_finset_sum Finset.univ fun gamma _ => (hAatom i j gamma).1
      _ ≤ ∑ i, ∑ j, ENNReal.toReal (eLpNorm (fun z => ∑ gamma,
            if hproper : gamma.left ≠ 0 then
              (beta.1.choose gamma.left : ℝ) *
                TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left
                  (fun x : TimeVelocity d => a x.1 x.2 i j) z *
                D.representative
                  (ParabolicDerivativeIndex.properSplitRightVelocityTwo
                    beta gamma hproper j i) z
            else 0) 2 (timeVelocityVolumeOn U)) :=
        Finset.sum_le_sum fun i _ => eLpNorm_fin_sum_toReal_le _ fun j =>
          memLp_finset_sum Finset.univ fun gamma _ => (hAatom i j gamma).1
      _ ≤ _ := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
        (eLpNorm_fin_sum_toReal_le _ fun gamma => (hAatom i j gamma).1).trans
          (Finset.sum_le_sum fun gamma _ => (hAatom i j gamma).2)
  have hBnorm : ENNReal.toReal (eLpNorm B 2 (timeVelocityVolumeOn U)) ≤
      ∑ j, ∑ gamma : TimeVelocityMultiIndex.Split beta.1,
        if hproper : gamma.left ≠ 0 then
          (beta.1.choose gamma.left : ℝ) *
            Bb j (ParabolicDerivativeIndex.splitLeft beta gamma) *
            ENNReal.toReal (eLpNorm
              (D.representative
                (ParabolicDerivativeIndex.properSplitRightVelocity
                  beta gamma hproper j)) 2 (timeVelocityVolumeOn U))
        else 0 := by
    calc
      _ ≤ ∑ j, ENNReal.toReal (eLpNorm (fun z => ∑ gamma,
            if hproper : gamma.left ≠ 0 then
              (beta.1.choose gamma.left : ℝ) *
                TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left
                  (fun x : TimeVelocity d => b x.1 x.2 j) z *
                D.representative
                  (ParabolicDerivativeIndex.properSplitRightVelocity
                    beta gamma hproper j) z
            else 0) 2 (timeVelocityVolumeOn U)) :=
        eLpNorm_fin_sum_toReal_le _ fun j =>
          memLp_finset_sum Finset.univ fun gamma _ => (hBatom j gamma).1
      _ ≤ _ := Finset.sum_le_sum fun j _ =>
        (eLpNorm_fin_sum_toReal_le _ fun gamma => (hBatom j gamma).1).trans
          (Finset.sum_le_sum fun gamma _ => (hBatom j gamma).2)
  have hCnorm : ENNReal.toReal (eLpNorm C 2 (timeVelocityVolumeOn U)) ≤
      ∑ gamma : TimeVelocityMultiIndex.Split beta.1,
        if hproper : gamma.left ≠ 0 then
          (beta.1.choose gamma.left : ℝ) *
            Bc (ParabolicDerivativeIndex.splitLeft beta gamma) *
            ENNReal.toReal (eLpNorm
              (D.representative
                (ParabolicDerivativeIndex.properSplitRightValue
                  beta gamma hproper)) 2 (timeVelocityVolumeOn U))
        else 0 :=
    (eLpNorm_fin_sum_toReal_le _ fun gamma => (hCatom gamma).1).trans
      (Finset.sum_le_sum fun gamma _ => (hCatom gamma).2)
  have hEA : ParabolicMemLpOn U 2 (fun z => E.representative beta z - A z) :=
    (E.memLp beta).sub hAmem
  have hEAB : ParabolicMemLpOn U 2
      (fun z => (E.representative beta z - A z) - B z) := hEA.sub hBmem
  have hsubB : ENNReal.toReal (eLpNorm (fun z =>
        (E.representative beta z - A z) - B z) 2 (timeVelocityVolumeOn U)) ≤
      ENNReal.toReal (eLpNorm (fun z => E.representative beta z - A z) 2
        (timeVelocityVolumeOn U)) +
      ENNReal.toReal (eLpNorm B 2 (timeVelocityVolumeOn U)) :=
    eLpNorm_sub_toReal_le _ _ hEA hBmem
  have hsubA : ENNReal.toReal (eLpNorm (fun z => E.representative beta z - A z) 2
        (timeVelocityVolumeOn U)) ≤
      ENNReal.toReal (eLpNorm (E.representative beta) 2 (timeVelocityVolumeOn U)) +
      ENNReal.toReal (eLpNorm A 2 (timeVelocityVolumeOn U)) :=
    eLpNorm_sub_toReal_le _ _ (E.memLp beta) hAmem
  refine ⟨?_, ?_⟩
  · convert hEAB.sub hCmem using 1
    funext z
    rfl
  · change ENNReal.toReal (eLpNorm (fun z =>
        ((E.representative beta z - A z) - B z) - C z) 2
          (timeVelocityVolumeOn U)) ≤ _
    calc
      _ ≤ ENNReal.toReal (eLpNorm (fun z =>
            (E.representative beta z - A z) - B z) 2 (timeVelocityVolumeOn U)) +
          ENNReal.toReal (eLpNorm C 2 (timeVelocityVolumeOn U)) :=
        eLpNorm_sub_toReal_le _ _ hEAB hCmem
      _ ≤ (ENNReal.toReal (eLpNorm (fun z => E.representative beta z - A z) 2
            (timeVelocityVolumeOn U)) +
          ENNReal.toReal (eLpNorm B 2 (timeVelocityVolumeOn U))) +
          ENNReal.toReal (eLpNorm C 2 (timeVelocityVolumeOn U)) :=
        add_le_add hsubB
          (le_refl (ENNReal.toReal (eLpNorm C 2 (timeVelocityVolumeOn U))))
      _ ≤ ((ENNReal.toReal (eLpNorm (E.representative beta) 2
            (timeVelocityVolumeOn U)) +
          ENNReal.toReal (eLpNorm A 2 (timeVelocityVolumeOn U))) +
          ENNReal.toReal (eLpNorm B 2 (timeVelocityVolumeOn U))) +
          ENNReal.toReal (eLpNorm C 2 (timeVelocityVolumeOn U)) :=
        add_le_add
          (add_le_add hsubA
            (le_refl (ENNReal.toReal (eLpNorm B 2 (timeVelocityVolumeOn U)))))
          (le_refl (ENNReal.toReal (eLpNorm C 2 (timeVelocityVolumeOn U))))
      _ ≤ _ := by
        exact add_le_add
          (add_le_add
            (add_le_add
              (le_refl (ENNReal.toReal (eLpNorm (E.representative beta) 2
                (timeVelocityVolumeOn U)))) hAnorm)
            hBnorm)
          hCnorm

end HypoellipticAleksandrov.Parabolic
