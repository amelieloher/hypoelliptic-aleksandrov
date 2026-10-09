module

public import HypoellipticAleksandrov.Ambient.MatrixContraction
public import HypoellipticAleksandrov.Coefficients.ParabolicRegularization
public import HypoellipticAleksandrov.Parabolic.ParabolicMollifierConvergence
public import PDEFoundation.Measure.LpDominatedConvergence

/-!
# Decay of the parabolic convolution commutator

This module proves the finite-`L^p` decay of the residual obtained by
convolving a bounded coefficient field and a matrix field separately.
It contains no equation or solution-theoretic assertion.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter MeasureTheory Set
open scoped Convolution ENNReal Topology

/-- The entrywise right convolution of a time--velocity matrix field. -/
noncomputable def parabolicMatrixConvolution
    {d : Nat} (H : TimeVelocity d → PDE.Mat d) (n : Nat) :
    TimeVelocity d → PDE.Mat d :=
  fun z i j => parabolicConvolution
    (fun y => H y i j) (parabolicMollifier d n) z

/-- The residual caused by convolving a coefficient and a Hessian separately. -/
noncomputable def parabolicConvolutionCommutator
    {d : Nat} (A : CoefficientField d)
    (H : TimeVelocity d → PDE.Mat d) (n : Nat) : TimeVelocity d → Real :=
  fun z =>
    parabolicConvolution
      (fun y => matrixContraction (coefficientAt A y) (H y))
      (parabolicMollifier d n) z -
    matrixContraction
      (coefficientAt (parabolicMollifyCoefficient A n) z)
      (parabolicMatrixConvolution H n z)

/-- A bounded a.e.-convergent multiplier commutes with two strongly
convergent finite-`L^p` approximations. -/
theorem tendsto_eLpNorm_bounded_multiplier_commutator
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {p : ENNReal}
    (hpOne : 1 ≤ p) (hpTop : p ≠ ∞)
    {a h c : α → Real}
    {an hn cn : Nat → α → Real} {M : Real}
    (hM : 0 ≤ M)
    (ha : AEStronglyMeasurable a μ)
    (han : ∀ n, AEStronglyMeasurable (an n) μ)
    (hh : MemLp h p μ)
    (hhn : ∀ n, AEStronglyMeasurable (hn n) μ)
    (hc : c =ᵐ[μ] fun x => a x * h x)
    (hcn : ∀ n, AEStronglyMeasurable (cn n) μ)
    (haBound : ∀ n, ∀ᵐ x ∂μ, |an n x| ≤ M)
    (haLimitBound : ∀ᵐ x ∂μ, |a x| ≤ M)
    (hae : ∀ᵐ x ∂μ,
      Tendsto (fun n => an n x) atTop (nhds (a x)))
    (hhnSub : Tendsto (fun n => eLpNorm (hn n - h) p μ)
      atTop (nhds 0))
    (hcnSub : Tendsto (fun n => eLpNorm (cn n - c) p μ)
      atTop (nhds 0)) :
    Tendsto (fun n => eLpNorm
      (cn n - fun x => an n x * hn n x) p μ) atTop (nhds 0) := by
  have hmiddleMem : MemLp (fun x => (2 * M) * |h x|) p μ :=
    hh.abs.const_mul (2 * M)
  have hmiddleMeas (n : Nat) : AEStronglyMeasurable
      (fun x => (a x - an n x) * h x) μ :=
    (ha.sub (han n)).mul hh.aestronglyMeasurable
  have hmiddleBound (n : Nat) : ∀ᵐ x ∂μ,
      ‖(a x - an n x) * h x‖ ≤ ‖(2 * M) * |h x|‖ := by
    filter_upwards [haLimitBound, haBound n] with x hax hanx
    simp only [Pi.mul_apply, Pi.sub_apply, Real.norm_eq_abs, abs_mul]
    have htwoM : 0 ≤ 2 * M := by linarith
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_nonneg hM, abs_abs]
    have hsub : |a x - an n x| ≤ 2 * M := by
      calc
        |a x - an n x| ≤ |a x| + |an n x| := abs_sub _ _
        _ ≤ 2 * M := by linarith
    exact mul_le_mul_of_nonneg_right hsub (abs_nonneg _)
  have hmiddleAe : ∀ᵐ x ∂μ,
      Tendsto (fun n => (a x - an n x) * h x) atTop (nhds 0) := by
    filter_upwards [hae] with x hx
    have hdiff :=
      (tendsto_const_nhds : Tendsto (fun _ : Nat => a x) atTop (nhds (a x))).sub hx
    have hmul := hdiff.mul_const (h x)
    simpa using hmul
  have hmiddle : Tendsto (fun n => eLpNorm
      (fun x => (a x - an n x) * h x) p μ) atTop (nhds 0) := by
    simpa using PDE.tendsto_eLpNorm_sub_zero_of_tendsto_ae_of_dominated
      (F := fun n x => (a x - an n x) * h x) (f := (0 : α → Real))
      (bound := fun x => (2 * M) * |h x|)
      hpOne hpTop hmiddleMeas MemLp.zero hmiddleMem hmiddleBound hmiddleAe
  have hlastBound (n : Nat) :
      eLpNorm (fun x => an n x * (hn n x - h x)) p μ ≤
        ENNReal.ofReal M * eLpNorm (hn n - h) p μ := by
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul
      ((han n).mul ((hhn n).sub hh.aestronglyMeasurable)) ?_ _
    filter_upwards [haBound n] with x hx
    simp only [Pi.mul_apply, Pi.sub_apply, Real.norm_eq_abs, abs_mul]
    change |an n x| * |hn n x - h x| ≤ M * |hn n x - h x|
    exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)
  have hlast : Tendsto (fun n => eLpNorm
      (fun x => an n x * (hn n x - h x)) p μ) atTop (nhds 0) := by
    have hlastRhs : Tendsto (fun n => ENNReal.ofReal M *
        eLpNorm (hn n - h) p μ) atTop (nhds 0) := by
      simpa using ENNReal.Tendsto.const_mul hhnSub
        (a := ENNReal.ofReal M) (Or.inr ENNReal.ofReal_ne_top)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds : Tendsto (fun _ : Nat => (0 : ENNReal)) atTop (nhds 0))
    · exact hlastRhs
    · exact Filter.Eventually.of_forall fun n => bot_le
    · exact Filter.Eventually.of_forall hlastBound
  have hlast' : Tendsto (fun n => eLpNorm
      (fun x => an n x * (h x - hn n x)) p μ) atTop (nhds 0) := by
    have hlastEq : (fun n => eLpNorm
        (fun x => an n x * (h x - hn n x)) p μ) =
        fun n => eLpNorm (fun x => an n x * (hn n x - h x)) p μ := by
      funext n
      rw [show (fun x => an n x * (h x - hn n x)) =
        -(fun x => an n x * (hn n x - h x)) by
          funext x
          simp only [Pi.neg_apply]
          ring, eLpNorm_neg]
    rw [hlastEq]
    exact hlast
  have hcMeas : AEStronglyMeasurable c μ :=
    (ha.mul hh.aestronglyMeasurable).congr hc.symm
  let r : Nat → α → Real := fun n x =>
    (cn n x - c x) +
      ((a x - an n x) * h x + an n x * (h x - hn n x))
  have hrBound (n : Nat) : eLpNorm (r n) p μ ≤
      eLpNorm (cn n - c) p μ +
        eLpNorm (fun x => (a x - an n x) * h x) p μ +
        eLpNorm (fun x => an n x * (h x - hn n x)) p μ := by
    change eLpNorm ((cn n - c) +
      ((fun x => (a x - an n x) * h x) +
        fun x => an n x * (h x - hn n x))) p μ ≤ _
    calc
      eLpNorm ((cn n - c) +
          (fun x => (a x - an n x) * h x + an n x * (h x - hn n x))) p μ ≤
          eLpNorm (cn n - c) p μ + eLpNorm
            (fun x => (a x - an n x) * h x + an n x * (h x - hn n x)) p μ :=
        eLpNorm_add_le (μ := μ) (p := p) hpOne
      _ ≤ _ := by
        calc
          eLpNorm (cn n - c) p μ +
              eLpNorm (fun x => (a x - an n x) * h x +
                an n x * (h x - hn n x)) p μ ≤
              eLpNorm (cn n - c) p μ +
                (eLpNorm (fun x => (a x - an n x) * h x) p μ +
                  eLpNorm (fun x => an n x * (h x - hn n x)) p μ) :=
            add_le_add_right
              (eLpNorm_add_le (μ := μ) (p := p)
                (f := fun x => (a x - an n x) * h x)
                (g := fun x => an n x * (h x - hn n x))
                hpOne) _
          _ = _ := (add_assoc _ _ _).symm
  have hrRhs : Tendsto (fun n => eLpNorm (cn n - c) p μ +
      eLpNorm (fun x => (a x - an n x) * h x) p μ +
      eLpNorm (fun x => an n x * (h x - hn n x)) p μ) atTop (nhds 0) := by
    simpa using (hcnSub.add hmiddle).add hlast'
  have hr : Tendsto (fun n => eLpNorm (r n) p μ) atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds : Tendsto (fun _ : Nat => (0 : ENNReal)) atTop (nhds 0))
      hrRhs
    · exact Filter.Eventually.of_forall fun n => bot_le
    · exact Filter.Eventually.of_forall hrBound
  have heq (n : Nat) :
      (cn n - fun x => an n x * hn n x) =ᵐ[μ] r n := by
    filter_upwards [hc] with x hcx
    dsimp [r]
    rw [hcx]
    ring
  have heLp (n : Nat) : eLpNorm (cn n - fun x => an n x * hn n x) p μ =
      eLpNorm (r n) p μ := eLpNorm_congr_ae (heq n)
  simpa only [heLp] using hr

private theorem parabolicConvolution_eq_leftConvolution {d : Nat}
    (f rho : TimeVelocity d → Real) :
    parabolicConvolution f rho =
      rho ⋆[ContinuousLinearMap.lsmul Real Real,
        (volume : Measure (TimeVelocity d))] f := by
  rw [← convolution_flip]
  ext z
  simp only [parabolicConvolution, convolution_def]
  apply integral_congr_ae
  filter_upwards with y
  change f y * rho (z - y) = rho (z - y) * f y
  exact mul_comm _ _

private theorem abs_parabolicConvolution_le_of_abs_le
    {d : Nat} {f : TimeVelocity d → Real} {M : Real}
    (hf : LocallyIntegrable f volume) (hbound : ∀ z, |f z| ≤ M)
    (n : Nat) (z : TimeVelocity d) :
    |parabolicConvolution f (parabolicMollifier d n) z| ≤ M := by
  have hconstLoc (c : Real) : LocallyIntegrable (fun _ : TimeVelocity d => c) volume :=
    locallyIntegrable_const c
  have hexists (g : TimeVelocity d → Real) (hg : LocallyIntegrable g volume) :
      ConvolutionExistsAt (parabolicMollifier d n) g z
        (ContinuousLinearMap.lsmul Real Real) volume :=
    (hasCompactSupport_parabolicMollifier d n).convolutionExists_left
      (ContinuousLinearMap.lsmul Real Real)
      (contDiff_parabolicMollifier d n).continuous hg z
  rw [parabolicConvolution_eq_leftConvolution]
  rw [abs_le]
  constructor
  · have hmono := convolution_mono_right
      (hexists (fun _ : TimeVelocity d => -M) (hconstLoc (-M)))
      (hexists f hf) (parabolicMollifier_nonneg d n)
      (fun y => (abs_le.mp (hbound y)).1)
    have hconst :
        (parabolicMollifier d n ⋆[ContinuousLinearMap.lsmul Real Real, volume]
          (fun _ : TimeVelocity d => -M)) z = -M := by
      exact ContDiffBump.normed_convolution_eq_right
        (φ := parabolicMollifierBump d n) (μ := volume) (fun _ _ => rfl)
    exact hconst.symm.le.trans hmono
  · have hmono := convolution_mono_right (hexists f hf)
      (hexists (fun _ : TimeVelocity d => M) (hconstLoc M))
      (parabolicMollifier_nonneg d n) (fun y => (abs_le.mp (hbound y)).2)
    have hconst :
        (parabolicMollifier d n ⋆[ContinuousLinearMap.lsmul Real Real, volume]
          (fun _ : TimeVelocity d => M)) z = M := by
      exact ContDiffBump.normed_convolution_eq_right
        (φ := parabolicMollifierBump d n) (μ := volume) (fun _ _ => rfl)
    exact hmono.trans hconst.le

private theorem parabolicConvolution_finset_sum {d : Nat} {ι : Type*}
    (s : Finset ι) (f : ι → TimeVelocity d → Real)
    (hf : ∀ i ∈ s, LocallyIntegrable (f i) volume) (n : Nat) :
    parabolicConvolution (fun z => ∑ i ∈ s, f i z) (parabolicMollifier d n) =
      fun z => ∑ i ∈ s, parabolicConvolution (f i) (parabolicMollifier d n) z := by
  letI : DecidableEq ι := Classical.decEq _
  induction s using Finset.induction_on with
  | empty =>
    rw [parabolicConvolution_eq_leftConvolution]
    exact convolution_zero
  | insert a s has ih =>
    have hsum : LocallyIntegrable (fun z => ∑ i ∈ s, f i z) volume := by
      exact locallyIntegrable_finset_sum s fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have ha : LocallyIntegrable (f a) volume := hf a (Finset.mem_insert_self _ _)
    have hconv : parabolicConvolution (f a + (fun z => ∑ i ∈ s, f i z))
        (parabolicMollifier d n) =
        parabolicConvolution (f a) (parabolicMollifier d n) +
          parabolicConvolution (fun z => ∑ i ∈ s, f i z) (parabolicMollifier d n) := by
      apply ConvolutionExists.add_distrib
      · exact (hasCompactSupport_parabolicMollifier d n).convolutionExists_right
          (ContinuousLinearMap.mul Real Real) ha
          (contDiff_parabolicMollifier d n).continuous
      · exact (hasCompactSupport_parabolicMollifier d n).convolutionExists_right
          (ContinuousLinearMap.mul Real Real) hsum
          (contDiff_parabolicMollifier d n).continuous
    simp_rw [Finset.sum_insert has]
    change parabolicConvolution (f a + (fun z => ∑ i ∈ s, f i z))
      (parabolicMollifier d n) = _
    rw [hconv, ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]
    rfl

private theorem parabolicConvolution_matrixContraction_eq_sum
    {d : Nat} (A : CoefficientField d) (H : TimeVelocity d → PDE.Mat d)
    (hprod : ∀ i j : Fin d,
      LocallyIntegrable (fun z => coefficientAt A z i j * H z i j) volume)
    (n : Nat) :
    parabolicConvolution (fun z => matrixContraction (coefficientAt A z) (H z))
      (parabolicMollifier d n) =
      fun z => ∑ i : Fin d, ∑ j : Fin d,
        parabolicConvolution (fun y => coefficientAt A y i j * H y i j)
          (parabolicMollifier d n) z := by
  letI : DecidableEq (Fin d) := Classical.decEq _
  have hrow (i : Fin d) : LocallyIntegrable
      (fun z => ∑ j : Fin d, coefficientAt A z i j * H z i j) volume := by
    exact locallyIntegrable_finset_sum Finset.univ fun j _ => hprod i j
  calc
    parabolicConvolution (fun z => matrixContraction (coefficientAt A z) (H z))
        (parabolicMollifier d n) =
        parabolicConvolution
          (fun z => ∑ i : Fin d, ∑ j : Fin d, coefficientAt A z i j * H z i j)
          (parabolicMollifier d n) := by
          rfl
    _ = fun z => ∑ i : Fin d, parabolicConvolution
        (fun y => ∑ j : Fin d, coefficientAt A y i j * H y i j)
        (parabolicMollifier d n) z :=
      parabolicConvolution_finset_sum Finset.univ
        (fun i z => ∑ j : Fin d, coefficientAt A z i j * H z i j)
        (fun i _ => hrow i) n
    _ = fun z => ∑ i : Fin d, ∑ j : Fin d,
        parabolicConvolution (fun y => coefficientAt A y i j * H y i j)
          (parabolicMollifier d n) z := by
      ext z
      apply Finset.sum_congr rfl
      intro i _
      exact congrFun (parabolicConvolution_finset_sum Finset.univ
        (fun j y => coefficientAt A y i j * H y i j)
        (fun j _ => hprod i j) n) z

/-- The entrywise parabolic convolution commutator tends to zero in finite
`L^(d + 1)` norm on every compact carrier. -/
theorem tendsto_eLpNorm_parabolicConvolutionCommutator_on_compact
    {d : Nat} (A : CoefficientField d)
    (H : TimeVelocity d → PDE.Mat d)
    (K : Set (TimeVelocity d)) (hK : IsCompact K)
    (M : Real) (hM : 0 ≤ M)
    (hAmeas : ∀ i j : Fin d,
      AEStronglyMeasurable (fun z => coefficientAt A z i j) volume)
    (hALoc : ∀ i j : Fin d,
      LocallyIntegrable (fun z => coefficientAt A z i j) volume)
    (hABound : ∀ i j : Fin d, ∀ z,
      |coefficientAt A z i j| ≤ M)
    (hHMem : ∀ i j : Fin d,
      MemLp (fun z => H z i j) (parabolicExponent d) volume) :
    Tendsto (fun n => eLpNorm
      (parabolicConvolutionCommutator A H n)
      (parabolicExponent d) (volume.restrict K)) atTop (nhds 0) := by
  letI : DecidableEq (Fin d) := Classical.decEq _
  let μK : Measure (TimeVelocity d) := volume.restrict K
  letI : IsFiniteMeasure μK := isFiniteMeasure_restrict.mpr hK.measure_ne_top
  let p : ENNReal := parabolicExponent d
  have hpOne : (1 : ENNReal) ≤ p := by
    change 1 ≤ (d : ENNReal) + 1
    have hd : (0 : ENNReal) ≤ (d : ENNReal) := bot_le
    simpa only [zero_add] using add_le_add_left hd (1 : ENNReal)
  have hpTop : p ≠ ∞ := by
    change (d : ENNReal) + 1 ≠ ∞
    rw [ENNReal.add_ne_top]
    exact ⟨ENNReal.coe_ne_top, ENNReal.one_ne_top⟩
  let a : Fin d → Fin d → TimeVelocity d → Real :=
    fun i j z => coefficientAt A z i j
  let an : Fin d → Fin d → Nat → TimeVelocity d → Real :=
    fun i j n z => parabolicConvolution (a i j) (parabolicMollifier d n) z
  let h : Fin d → Fin d → TimeVelocity d → Real :=
    fun i j z => H z i j
  let hn : Fin d → Fin d → Nat → TimeVelocity d → Real :=
    fun i j n z => parabolicConvolution (h i j) (parabolicMollifier d n) z
  let c : Fin d → Fin d → TimeVelocity d → Real :=
    fun i j z => a i j z * h i j z
  let cn : Fin d → Fin d → Nat → TimeVelocity d → Real :=
    fun i j n z => parabolicConvolution (c i j) (parabolicMollifier d n) z
  let residual : Fin d → Fin d → Nat → TimeVelocity d → Real :=
    fun i j n z => cn i j n z - an i j n z * hn i j n z
  have hprodMem (i j : Fin d) : MemLp (c i j) p volume := by
    refine MemLp.of_le_mul (c := M) (hHMem i j) ?_ ?_
    · exact (hAmeas i j).mul (hHMem i j).aestronglyMeasurable
    · filter_upwards with z
      dsimp [c, a, h]
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hABound i j z) (abs_nonneg _)
  have hprodLoc (i j : Fin d) : LocallyIntegrable (c i j) volume :=
    (hprodMem i j).locallyIntegrable hpOne
  have hconvMatrix (n : Nat) :
      parabolicConvolution
        (fun z => matrixContraction (coefficientAt A z) (H z))
        (parabolicMollifier d n) =
        fun z => ∑ i : Fin d, ∑ j : Fin d,
          cn i j n z := by
    simpa only [cn, c, a, h] using
      parabolicConvolution_matrixContraction_eq_sum A H
        (fun i j => hprodLoc i j) n
  have hhnSub (i j : Fin d) : Tendsto
      (fun n => eLpNorm (hn i j n - h i j) p μK) atTop (nhds 0) := by
    have hglobal := tendsto_eLpNorm_parabolicConvolution_sub hpOne hpTop (hHMem i j)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds : Tendsto (fun _ : Nat => (0 : ENNReal)) atTop (nhds 0))
      hglobal
    · exact Filter.Eventually.of_forall fun n => bot_le
    · filter_upwards with n
      exact eLpNorm_restrict_le _ p volume K
  have hcnSub (i j : Fin d) : Tendsto
      (fun n => eLpNorm (cn i j n - c i j) p μK) atTop (nhds 0) := by
    have hglobal := tendsto_eLpNorm_parabolicConvolution_sub hpOne hpTop (hprodMem i j)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds : Tendsto (fun _ : Nat => (0 : ENNReal)) atTop (nhds 0))
      hglobal
    · exact Filter.Eventually.of_forall fun n => bot_le
    · filter_upwards with n
      exact eLpNorm_restrict_le _ p volume K
  have haMeas (i j : Fin d) : AEStronglyMeasurable (a i j) μK := by
    exact (hAmeas i j).mono_measure Measure.restrict_le_self
  have hanMeas (i j : Fin d) (n : Nat) : AEStronglyMeasurable (an i j n) μK := by
    exact AEStronglyMeasurable.mono_measure
      ((contDiff_parabolicConvolution (hALoc i j)
      (contDiff_parabolicMollifier d n)
      (hasCompactSupport_parabolicMollifier d n)).continuous.aestronglyMeasurable)
      Measure.restrict_le_self
  have hhMem (i j : Fin d) : MemLp (h i j) p μK := by
    exact (hHMem i j).restrict K
  have hhnMeas (i j : Fin d) (n : Nat) : AEStronglyMeasurable (hn i j n) μK := by
    exact AEStronglyMeasurable.mono_measure
      ((contDiff_parabolicConvolution ((hHMem i j).locallyIntegrable hpOne)
      (contDiff_parabolicMollifier d n)
      (hasCompactSupport_parabolicMollifier d n)).continuous.aestronglyMeasurable)
      Measure.restrict_le_self
  have hcnMeas (i j : Fin d) (n : Nat) : AEStronglyMeasurable (cn i j n) μK := by
    exact AEStronglyMeasurable.mono_measure
      ((contDiff_parabolicConvolution (hprodLoc i j)
      (contDiff_parabolicMollifier d n)
      (hasCompactSupport_parabolicMollifier d n)).continuous.aestronglyMeasurable)
      Measure.restrict_le_self
  have hanBound (i j : Fin d) (n : Nat) : ∀ᵐ z ∂μK, |an i j n z| ≤ M := by
    filter_upwards with z
    exact abs_parabolicConvolution_le_of_abs_le (hALoc i j) (hABound i j) n z
  have haLimitBound (i j : Fin d) : ∀ᵐ z ∂μK, |a i j z| ≤ M := by
    exact Filter.Eventually.of_forall (hABound i j)
  have hae (i j : Fin d) : ∀ᵐ z ∂μK,
      Tendsto (fun n => an i j n z) atTop (nhds (a i j z)) := by
    exact Filter.Eventually.filter_mono
      (ae_mono Measure.restrict_le_self)
      (tendsto_ae_parabolicConvolution_of_locallyIntegrable (hALoc i j))
  have hcoord (i j : Fin d) : Tendsto
      (fun n => eLpNorm (residual i j n) p μK) atTop (nhds 0) := by
    exact tendsto_eLpNorm_bounded_multiplier_commutator hpOne hpTop hM
      (haMeas i j) (hanMeas i j) (hhMem i j) (hhnMeas i j)
      (EventuallyEq.rfl) (hcnMeas i j) (hanBound i j) (haLimitBound i j)
      (hae i j) (hhnSub i j) (hcnSub i j)
  have hreconstruction (n : Nat) : parabolicConvolutionCommutator A H n =
      fun z => ∑ i : Fin d, ∑ j : Fin d, residual i j n z := by
    funext z
    unfold parabolicConvolutionCommutator parabolicMatrixConvolution
    rw [hconvMatrix n]
    change (∑ i : Fin d, ∑ j : Fin d, cn i j n z) -
      ∑ i : Fin d, ∑ j : Fin d, an i j n z * hn i j n z =
      ∑ i : Fin d, ∑ j : Fin d, residual i j n z
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_sub_distrib]
  have hresMeas (i j : Fin d) (n : Nat) :
      AEStronglyMeasurable (residual i j n) μK := by
    exact (hcnMeas i j n).sub ((hanMeas i j n).mul (hhnMeas i j n))
  have hsumBound (n : Nat) : eLpNorm (parabolicConvolutionCommutator A H n) p μK ≤
      ∑ i : Fin d, ∑ j : Fin d, eLpNorm (residual i j n) p μK := by
    rw [hreconstruction n, ← Finset.sum_fn]
    calc
      eLpNorm (∑ i : Fin d, fun z => ∑ j : Fin d, residual i j n z) p μK ≤
          ∑ i : Fin d, eLpNorm (fun z => ∑ j : Fin d, residual i j n z) p μK :=
        eLpNorm_sum_le hpOne
      _ ≤ ∑ i : Fin d, ∑ j : Fin d, eLpNorm (residual i j n) p μK := by
        apply Finset.sum_le_sum
        intro i _
        rw [← Finset.sum_fn]
        exact eLpNorm_sum_le hpOne
  have hsumTendsto : Tendsto
      (fun n => ∑ i : Fin d, ∑ j : Fin d, eLpNorm (residual i j n) p μK)
      atTop (nhds 0) := by
    simpa only [Finset.sum_const_zero] using
      tendsto_finset_sum Finset.univ (fun i _ =>
        tendsto_finset_sum Finset.univ (fun j _ => hcoord i j))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : Nat => (0 : ENNReal)) atTop (nhds 0))
    hsumTendsto
  · exact Filter.Eventually.of_forall fun n => bot_le
  · exact Filter.Eventually.of_forall hsumBound

end HypoellipticAleksandrov.Parabolic
