module

public import HypoellipticAleksandrov.Parabolic.MeasurableSpatialC1RawWeakDerivative
public import HypoellipticAleksandrov.Parabolic.TimeVelocitySmoothCompactPlateau
public import HypoellipticAleksandrov.Parabolic.WeakJetProduct
public import HypoellipticAleksandrov.Parabolic.WeakDerivativesCompactGlobalization
public import HypoellipticAleksandrov.Parabolic.WeakDerivativeSpacetimeMollification
public import HypoellipticAleksandrov.Parabolic.SpacetimeMollifierL2
public import HypoellipticAleksandrov.Analysis.L2ProductConvergence
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Weak Leibniz rule for measurable-time, spatially smooth multipliers

This module proves the quantitative weak velocity product rule for bounded
jointly measurable scalar multipliers whose fixed-time spatial slices are
`C¹`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter Function MeasureTheory Set Topology
open scoped ENNReal Topology
open SpacetimeMollifier

private theorem ae_restrict_of_forall_mem
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (S : Set α) (hS : MeasurableSet S) {P : α → Prop} (hP : ∀ x ∈ S, P x) :
    ∀ᵐ x ∂μ.restrict S, P x := by
  filter_upwards [ae_restrict_mem hS] with x hx
  exact hP x hx

private theorem memLp_mul_of_abs_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p : ℝ≥0∞} {a f : α → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (ha : AEStronglyMeasurable a μ)
    (hf : MemLp f p μ) (haM : ∀ᵐ x ∂μ, |a x| ≤ M) :
    MemLp (fun x => a x * f x) p μ ∧
      eLpNorm (fun x => a x * f x) p μ ≤
        ENNReal.ofReal M * eLpNorm f p μ := by
  have hmeas : AEStronglyMeasurable (fun x => a x * f x) μ := ha.mul hf.aestronglyMeasurable
  have hpoint : ∀ᵐ x ∂μ, ‖a x * f x‖ ≤ M * ‖f x‖ := by
    filter_upwards [haM] with x hx
    simpa only [Real.norm_eq_abs, abs_mul] using
      mul_le_mul hx le_rfl (abs_nonneg (f x)) hM
  exact ⟨MemLp.of_le_mul hf hmeas hpoint,
    eLpNorm_le_mul_eLpNorm_of_ae_le_mul hmeas hpoint p⟩

private theorem toReal_eLpNorm_mul_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p : ℝ≥0∞} {a f : α → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (ha : AEStronglyMeasurable a μ)
    (hf : MemLp f p μ) (haM : ∀ᵐ x ∂μ, |a x| ≤ M) :
    MemLp (fun x => a x * f x) p μ ∧
      ENNReal.toReal (eLpNorm (fun x => a x * f x) p μ) ≤
        M * ENNReal.toReal (eLpNorm f p μ) := by
  obtain ⟨haf, hle⟩ := memLp_mul_of_abs_le hM ha hf haM
  refine ⟨haf, ?_⟩
  have htop : ENNReal.ofReal M * eLpNorm f p μ ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf.eLpNorm_ne_top
  have hr := ENNReal.toReal_mono htop hle
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hM] using hr

private theorem aestronglyMeasurable_of_restrict_of_support_subset
    {d : ℕ} {U : Set (TimeVelocity d)} (hU : MeasurableSet U)
    {f : TimeVelocity d → ℝ}
    (hf : AEStronglyMeasurable f (timeVelocityVolumeOn U))
    (hsupp : Function.support f ⊆ U) :
    AEStronglyMeasurable f (volume : Measure (TimeVelocity d)) := by
  have hindicator : U.indicator f = f := by
    funext z
    by_cases hz : z ∈ U
    · simp [hz]
    · have hfz : f z = 0 := by
        by_contra hn
        exact hz (hsupp (Function.mem_support.mpr hn))
      simp [hz, hfz]
  rw [← hindicator]
  exact (aestronglyMeasurable_indicator_iff hU).2 hf

private theorem velocityGradient_eq_zero_of_eq_one_on
    {d : ℕ} {b : TimeVelocity d → ℝ} {K : Set (TimeVelocity d)}
    {δ : ℝ} (hδ : 0 < δ) (hb : Set.EqOn b 1 (Metric.cthickening δ K))
    (k : Fin d) {z : TimeVelocity d} (hz : z ∈ K) :
    velocityGradient b z k = 0 := by
  have heq : b =ᶠ[𝓝 z] (fun _ => (1 : ℝ)) := by
    filter_upwards [Metric.ball_mem_nhds z hδ] with y hy
    apply hb
    exact Metric.mem_cthickening_of_dist_le y z δ K hz (le_of_lt hy)
  unfold velocityGradient
  rw [heq.fderiv_eq]
  simp

private theorem velocityGradient_tsupport_subset
    {d : ℕ} (b : TimeVelocity d → ℝ) (k : Fin d) :
    tsupport (fun z => velocityGradient b z k) ⊆ tsupport b := by
  unfold velocityGradient
  change closure (Function.support
    (fun z => fderiv ℝ b z ((0, Pi.single k 1) : TimeVelocity d))) ⊆ tsupport b
  exact (closure_mono fun z hz => by
    rw [Function.mem_support] at hz ⊢
    intro hbz
    apply hz
    simp [hbz]).trans (tsupport_fderiv_subset ℝ)

private theorem eq_zero_of_not_mem_tsupport
    {X E : Type*} [TopologicalSpace X] [Zero E] (f : X → E) {x : X}
    (hx : x ∉ tsupport f) : f x = 0 := by
  by_contra hn
  exact hx (subset_tsupport f (Function.mem_support.mpr hn))

private theorem tendsto_integral_spacetimeMollification_mul_fixed
    {d : ℕ} (f g : TimeVelocity d → ℝ)
    (hf : MemLp f (2 : ℝ≥0∞) (volume : Measure (TimeVelocity d)))
    (hg : MemLp g (2 : ℝ≥0∞) (volume : Measure (TimeVelocity d))) :
    Tendsto
      (fun ε : ℝ => ∫ z : TimeVelocity d,
        spacetimeMollification ε f z * g z ∂volume)
      (𝓝[>] 0) (𝓝 (∫ z : TimeVelocity d, f z * g z ∂volume)) := by
  apply HypoellipticAleksandrov.Analysis.tendsto_integral_mul_of_tendsto_eLpNorm_two
      (fun ε => spacetimeMollification ε f) (fun _ => g) f g
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact SpacetimeMollifierL2.spacetimeMollification_memLp hε f hf
  · exact Eventually.of_forall fun _ => hg
  · exact hf
  · exact hg
  · simpa only [Pi.sub_def] using
      SpacetimeMollifierL2.tendsto_eLpNorm_spacetimeMollification_sub f hf
  · have hzero : (fun n : ℝ => eLpNorm
        (fun _ : TimeVelocity d => (0 : ℝ)) (2 : ℝ≥0∞)
        (volume : Measure (TimeVelocity d))) = fun _ => (0 : ℝ≥0∞) := by
      funext n
      exact eLpNorm_zero
    simpa only [sub_self, hzero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ≥0∞)) (𝓝[>] 0) (𝓝 0))

private theorem integral_univ_eq_setIntegral_of_support_subset
    {d : ℕ} {U : Set (TimeVelocity d)} (hU : MeasurableSet U)
    (f : TimeVelocity d → ℝ) (hsupp : Function.support f ⊆ U) :
    (∫ z : TimeVelocity d, f z ∂volume) = ∫ z in U, f z ∂volume := by
  rw [← integral_indicator hU]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    by_cases hz : z ∈ U
    · simp [hz]
    · have hfz : f z = 0 := by
        by_contra hn
        exact hz (hsupp (Function.mem_support.mpr hn))
      simp [hz, hfz]

private theorem bounded_weak_mul
    {d : ℕ} {U : Set (TimeVelocity d)} (hU : IsOpen U)
    (k : Fin d) (Bq Bdq : ℝ) (hBq : 0 ≤ Bq) (hBdq : 0 ≤ Bdq)
    (q dq u du : TimeVelocity d → ℝ)
    (hqMeas : AEStronglyMeasurable q (timeVelocityVolumeOn U))
    (hdqMeas : AEStronglyMeasurable dq (timeVelocityVolumeOn U))
    (hqBound : ∀ z ∈ U, |q z| ≤ Bq)
    (hdqBound : ∀ z ∈ U, |dq z| ≤ Bdq)
    (hqWeak : HasWeakVelocityPartialDerivOn U k q dq)
    (hu : ParabolicMemLpOn U 2 u) (hdu : ParabolicMemLpOn U 2 du)
    (hweak : HasWeakVelocityPartialDerivOn U k u du) :
    HasWeakVelocityPartialDerivOn U k (fun z => q z * u z)
      (fun z => q z * du z + dq z * u z) := by
  have hUmeas : MeasurableSet U := hU.measurableSet
  have hqAE : ∀ᵐ z ∂timeVelocityVolumeOn U, |q z| ≤ Bq :=
    ae_restrict_of_forall_mem U hUmeas hqBound
  have hdqAE : ∀ᵐ z ∂timeVelocityVolumeOn U, |dq z| ≤ Bdq :=
    ae_restrict_of_forall_mem U hUmeas hdqBound
  have hqTop : MemLp q ∞ (timeVelocityVolumeOn U) :=
    memLp_top_of_bound hqMeas Bq (by simpa only [Real.norm_eq_abs] using hqAE)
  have hdqTop : MemLp dq ∞ (timeVelocityVolumeOn U) :=
    memLp_top_of_bound hdqMeas Bdq (by simpa only [Real.norm_eq_abs] using hdqAE)
  have hqLoc : LocallyIntegrableOn q U volume :=
    locallyIntegrableOn_of_locallyIntegrable_restrict (hqTop.locallyIntegrable (by simp))
  have hdqLoc : LocallyIntegrableOn dq U volume :=
    locallyIntegrableOn_of_locallyIntegrable_restrict (hdqTop.locallyIntegrable (by simp))
  intro φ hφ hφCompact hφSub
  obtain ⟨δ, hδ, b, hb, hbCompact, hbSub, hbOne⟩ :=
    exists_contDiff_one_on_cthickening_tsupport_subset
      hU hφCompact.isCompact hφSub
  let Q : TimeVelocity d → ℝ := fun z => b z * q z
  let DQ : TimeVelocity d → ℝ := fun z => b z * dq z + q z * velocityGradient b z k
  have hQWeakU : HasWeakVelocityPartialDerivOn U k Q DQ := by
    simpa only [Q, DQ, mul_comm, add_comm] using
      hqWeak.mul_contDiff hb hqLoc hdqLoc
  have hQSupp : tsupport Q ⊆ U := by
    exact (tsupport_mul_subset_left (f := b) (g := q)).trans hbSub
  have hDQSuppB : tsupport DQ ⊆ tsupport b := by
    exact (tsupport_add _ _).trans (union_subset
      (tsupport_mul_subset_left (f := b) (g := dq))
      ((tsupport_mul_subset_right (f := q)
        (g := fun z => velocityGradient b z k)).trans
          (velocityGradient_tsupport_subset b k)))
  have hDQSupp : tsupport DQ ⊆ U := hDQSuppB.trans hbSub
  have hQWeak : HasWeakVelocityPartialDerivOn Set.univ k Q DQ :=
    hQWeakU.univ_of_tsupport_subset hU hQSupp hDQSupp
  have hQSupport : Function.support Q ⊆ U := (subset_tsupport Q).trans hQSupp
  have hDQSupport : Function.support DQ ⊆ U := (subset_tsupport DQ).trans hDQSupp
  have hbMeasU : AEStronglyMeasurable b (timeVelocityVolumeOn U) :=
    hb.continuous.aestronglyMeasurable
  have hdbMeasU : AEStronglyMeasurable (fun z => velocityGradient b z k)
      (timeVelocityVolumeOn U) := by
    unfold velocityGradient
    exact ((hb.continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable
  have hQMeasU : AEStronglyMeasurable Q (timeVelocityVolumeOn U) :=
    hbMeasU.mul hqMeas
  have hDQMeasU : AEStronglyMeasurable DQ (timeVelocityVolumeOn U) :=
    (hbMeasU.mul hdqMeas).add (hqMeas.mul hdbMeasU)
  have hQMeas : AEStronglyMeasurable Q
      (volume : Measure (TimeVelocity d)) :=
    aestronglyMeasurable_of_restrict_of_support_subset hUmeas hQMeasU hQSupport
  have hDQMeas : AEStronglyMeasurable DQ
      (volume : Measure (TimeVelocity d)) :=
    aestronglyMeasurable_of_restrict_of_support_subset hUmeas hDQMeasU hDQSupport
  obtain ⟨Cb, hCb⟩ := hb.continuous.bounded_above_of_compact_support hbCompact
  have hdbCont : Continuous (fun z => velocityGradient b z k) := by
    unfold velocityGradient
    exact (hb.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdbCompact : HasCompactSupport (fun z => velocityGradient b z k) := by
    exact HasCompactSupport.of_support_subset_isCompact hbCompact.isCompact
      ((subset_tsupport _).trans (velocityGradient_tsupport_subset b k))
  obtain ⟨Cdb, hCdb⟩ := hdbCont.bounded_above_of_compact_support hdbCompact
  have hQPoint : ∀ z, ‖Q z‖ ≤ |Cb| * Bq := by
    intro z
    by_cases hz : z ∈ U
    · dsimp only [Q]
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (le_trans (hCb z) (le_abs_self Cb)) (hqBound z hz)
        (abs_nonneg _) (abs_nonneg _)
    · have hQz : Q z = 0 := by
        by_contra hn
        exact hz (hQSupport (Function.mem_support.mpr hn))
      simp [hQz, mul_nonneg (abs_nonneg Cb) hBq]
  have hDQPoint : ∀ z, ‖DQ z‖ ≤ |Cb| * Bdq + Bq * |Cdb| := by
    intro z
    by_cases hz : z ∈ U
    · dsimp only [DQ]
      rw [Real.norm_eq_abs]
      calc
        |b z * dq z + q z * velocityGradient b z k| ≤
            |b z| * |dq z| + |q z| * |velocityGradient b z k| := by
              simpa only [abs_mul] using abs_add_le (b z * dq z) (q z * velocityGradient b z k)
        _ ≤ |Cb| * Bdq + Bq * |Cdb| := by
          exact add_le_add
            (mul_le_mul (le_trans (hCb z) (le_abs_self Cb)) (hdqBound z hz)
              (abs_nonneg _) (abs_nonneg _))
            (mul_le_mul (hqBound z hz) (le_trans (hCdb z) (le_abs_self Cdb))
              (abs_nonneg _) hBq)
    · have hDQz : DQ z = 0 := by
        by_contra hn
        exact hz (hDQSupport (Function.mem_support.mpr hn))
      rw [hDQz, norm_zero]
      exact add_nonneg (mul_nonneg (abs_nonneg Cb) hBdq)
        (mul_nonneg hBq (abs_nonneg Cdb))
  have hQCompact : HasCompactSupport Q := by
    exact HasCompactSupport.of_support_subset_isCompact hbCompact.isCompact
      ((subset_tsupport Q).trans
        (tsupport_mul_subset_left (f := b) (g := q)))
  have hQMem : MemLp Q (2 : ℝ≥0∞) (volume : Measure (TimeVelocity d)) :=
    hQCompact.memLp_of_bound hQMeas (|Cb| * Bq) (Eventually.of_forall hQPoint)
  have hDQCompact : HasCompactSupport DQ := by
    exact HasCompactSupport.of_support_subset_isCompact hbCompact.isCompact
      ((subset_tsupport _).trans hDQSuppB)
  have hDQMem : MemLp DQ (2 : ℝ≥0∞) (volume : Measure (TimeVelocity d)) :=
    hDQCompact.memLp_of_bound hDQMeas (|Cb| * Bdq + Bq * |Cdb|)
      (Eventually.of_forall hDQPoint)
  have hφTop : MemLp φ ∞ (volume : Measure (TimeVelocity d)) :=
    hφ.continuous.memLp_top_of_hasCompactSupport hφCompact volume
  have hgradCont : Continuous (fun z => velocityGradient φ z k) := by
    unfold velocityGradient
    exact (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hgradCompact : HasCompactSupport (fun z => velocityGradient φ z k) := by
    exact HasCompactSupport.of_support_subset_isCompact hφCompact.isCompact
      ((subset_tsupport _).trans (velocityGradient_tsupport_subset φ k))
  have hgradTop : MemLp (fun z => velocityGradient φ z k) ∞
      (volume : Measure (TimeVelocity d)) :=
    hgradCont.memLp_top_of_hasCompactSupport hgradCompact volume
  have huφR : ParabolicMemLpOn U 2 (fun z => u z * φ z) := by
    simpa only [mul_comm] using hu.mul' (hφTop.restrict U)
  have hduφR : ParabolicMemLpOn U 2 (fun z => du z * φ z) := by
    simpa only [mul_comm] using hdu.mul' (hφTop.restrict U)
  have huGradR : ParabolicMemLpOn U 2
      (fun z => u z * velocityGradient φ z k) := by
    simpa only [mul_comm] using hu.mul' (hgradTop.restrict U)
  have huφSupp : Function.support (fun z => u z * φ z) ⊆ U :=
    (Function.support_mul_subset_right u φ).trans (subset_tsupport φ |>.trans hφSub)
  have hduφSupp : Function.support (fun z => du z * φ z) ⊆ U :=
    (Function.support_mul_subset_right du φ).trans (subset_tsupport φ |>.trans hφSub)
  have huGradSupp : Function.support (fun z => u z * velocityGradient φ z k) ⊆ U :=
    (Function.support_mul_subset_right u _).trans
      ((subset_tsupport _).trans ((velocityGradient_tsupport_subset φ k).trans hφSub))
  have huφ : MemLp (fun z => u z * φ z) 2 volume :=
    huφR.memLp_of_support_subset hUmeas huφSupp
  have hduφ : MemLp (fun z => du z * φ z) 2 volume :=
    hduφR.memLp_of_support_subset hUmeas hduφSupp
  have huGrad : MemLp (fun z => u z * velocityGradient φ z k) 2 volume :=
    huGradR.memLp_of_support_subset hUmeas huGradSupp
  have hQlim := tendsto_integral_spacetimeMollification_mul_fixed Q
    (fun z => u z * velocityGradient φ z k) hQMem huGrad
  have hQdulim := tendsto_integral_spacetimeMollification_mul_fixed Q
    (fun z => du z * φ z) hQMem hduφ
  have hDQlim := tendsto_integral_spacetimeMollification_mul_fixed DQ
    (fun z => u z * φ z) hDQMem huφ
  have hsmooth (ε : ℝ) (hε : 0 < ε) :
      HasWeakVelocityPartialDerivOn U k
        (fun z => spacetimeMollification ε Q z * u z)
        (fun z => spacetimeMollification ε Q z * du z +
          u z * spacetimeMollification ε DQ z) := by
    have hQεsmooth := contDiff_spacetimeMollification hε Q
      (hQMem.locallyIntegrable (by norm_num))
    have hcomm := velocityGradient_spacetimeMollification hε k Q DQ
      (hQMem.locallyIntegrable (by norm_num))
      (hDQMem.locallyIntegrable (by norm_num)) hQWeak
    have hp := hweak.mul_contDiff hQεsmooth
      (hu.locallyIntegrableOn (by norm_num)) (hdu.locallyIntegrableOn (by norm_num))
    have hcommPoint (z : TimeVelocity d) :
        velocityGradient (spacetimeMollification ε Q) z k =
          spacetimeMollification ε DQ z := congrFun hcomm z
    simp_rw [hcommPoint] at hp
    exact hp
  have hid : ∀ ε ∈ Ioi (0 : ℝ),
      (∫ z : TimeVelocity d, spacetimeMollification ε Q z *
        (u z * velocityGradient φ z k) ∂volume) =
      -((∫ z : TimeVelocity d, spacetimeMollification ε Q z *
          (du z * φ z) ∂volume) +
        ∫ z : TimeVelocity d, spacetimeMollification ε DQ z *
          (u z * φ z) ∂volume) := by
    intro ε hε
    have hw := hsmooth ε hε φ hφ hφCompact hφSub
    have hleft := integral_univ_eq_setIntegral_of_support_subset hUmeas
      (fun z => spacetimeMollification ε Q z * (u z * velocityGradient φ z k))
      ((Function.support_mul_subset_right _ _).trans huGradSupp)
    have hright₁ := integral_univ_eq_setIntegral_of_support_subset hUmeas
      (fun z => spacetimeMollification ε Q z * (du z * φ z))
      ((Function.support_mul_subset_right _ _).trans hduφSupp)
    have hright₂ := integral_univ_eq_setIntegral_of_support_subset hUmeas
      (fun z => spacetimeMollification ε DQ z * (u z * φ z))
      ((Function.support_mul_subset_right _ _).trans huφSupp)
    rw [hleft, hright₁, hright₂]
    calc
      (∫ z in U, spacetimeMollification ε Q z *
          (u z * velocityGradient φ z k) ∂volume) =
          ∫ z in U, (spacetimeMollification ε Q z * u z) *
            velocityGradient φ z k ∂volume := by
              apply integral_congr_ae
              exact Eventually.of_forall fun z => by ring
      _ = -∫ z in U, (spacetimeMollification ε Q z * du z +
          u z * spacetimeMollification ε DQ z) * φ z ∂volume := hw
      _ = -((∫ z in U, spacetimeMollification ε Q z * (du z * φ z) ∂volume) +
          ∫ z in U, spacetimeMollification ε DQ z * (u z * φ z) ∂volume) := by
            rw [← integral_add]
            · congr 1
              apply integral_congr_ae
              exact Eventually.of_forall fun z => by ring
            · exact ((SpacetimeMollifierL2.spacetimeMollification_memLp hε Q hQMem)
                |>.integrable_mul hduφ).restrict
            · exact ((SpacetimeMollifierL2.spacetimeMollification_memLp hε DQ hDQMem)
                |>.integrable_mul huφ).restrict
  have hlimitRight := hQdulim.add hDQlim |>.neg
  have heqEventually : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∫ z : TimeVelocity d, spacetimeMollification ε Q z *
        (u z * velocityGradient φ z k) ∂volume) =
      -((∫ z : TimeVelocity d, spacetimeMollification ε Q z *
          (du z * φ z) ∂volume) +
        ∫ z : TimeVelocity d, spacetimeMollification ε DQ z *
          (u z * φ z) ∂volume) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hid ε hε
  have hlimEq :
      (∫ z : TimeVelocity d, Q z * (u z * velocityGradient φ z k) ∂volume) =
      -((∫ z : TimeVelocity d, Q z * (du z * φ z) ∂volume) +
        ∫ z : TimeVelocity d, DQ z * (u z * φ z) ∂volume) :=
    tendsto_nhds_unique hQlim
      (hlimitRight.congr' (heqEventually.mono fun _ h => h.symm))
  have hQeq (z : TimeVelocity d) (hz : z ∈ tsupport φ) : Q z = q z := by
    have hbz := hbOne (Metric.self_subset_cthickening (tsupport φ) hz)
    simp [Q, hbz]
  have hDQeq (z : TimeVelocity d) (hz : z ∈ tsupport φ) : DQ z = dq z := by
    have hbz := hbOne (Metric.self_subset_cthickening (tsupport φ) hz)
    have hdbz := velocityGradient_eq_zero_of_eq_one_on hδ hbOne k hz
    simp [DQ, hbz, hdbz]
  rw [integral_univ_eq_setIntegral_of_support_subset hUmeas _
      ((Function.support_mul_subset_right _ _).trans huGradSupp),
    integral_univ_eq_setIntegral_of_support_subset hUmeas _
      ((Function.support_mul_subset_right _ _).trans hduφSupp),
    integral_univ_eq_setIntegral_of_support_subset hUmeas _
      ((Function.support_mul_subset_right _ _).trans huφSupp)] at hlimEq
  calc
    (∫ z in U, (q z * u z) * velocityGradient φ z k ∂volume) =
        ∫ z in U, Q z * (u z * velocityGradient φ z k) ∂volume := by
          apply integral_congr_ae
          exact Eventually.of_forall fun z => by
            by_cases hdφ : velocityGradient φ z k = 0
            · simp [hdφ]
            · have hzts : z ∈ tsupport φ :=
                (velocityGradient_tsupport_subset φ k)
                  (subset_tsupport _ (Function.mem_support.mpr hdφ))
              change q z * u z * velocityGradient φ z k =
                Q z * (u z * velocityGradient φ z k)
              rw [hQeq z hzts]
              ring
    _ = -((∫ z in U, Q z * (du z * φ z) ∂volume) +
        ∫ z in U, DQ z * (u z * φ z) ∂volume) := hlimEq
    _ = -∫ z in U, (q z * du z + dq z * u z) * φ z ∂volume := by
      rw [← integral_add]
      · congr 1
        apply integral_congr_ae
        exact Eventually.of_forall fun z => by
          by_cases hzφ : φ z = 0
          · simp [hzφ]
          · have hzts : z ∈ tsupport φ := subset_tsupport φ
                (Function.mem_support.mpr hzφ)
            change Q z * (du z * φ z) + DQ z * (u z * φ z) =
              (q z * du z + dq z * u z) * φ z
            rw [hQeq z hzts, hDQeq z hzts]
            ring
      · exact (hQMem.integrable_mul hduφ).restrict
      · exact (hDQMem.integrable_mul huφ).restrict

/-- A bounded jointly measurable multiplier that is `C¹` in each fixed-time
spatial slice obeys the weak spatial Leibniz rule on a compactly contained
product cylinder, with quantitative `L²` control. -/
theorem spatialC1_mul_hasWeakVelocityPartialDerivOn_memLp_eLpNorm_le
    (d : ℕ) (t₀ t₁ t₂ t₃ : ℝ)
    (ht₀₁ : t₀ < t₁) (ht₁₂ : t₁ < t₂) (ht₂₃ : t₂ < t₃)
    (O₀ O₁ : Set (PDE.Vec d))
    (hO₀ : IsOpen O₀) (hO₁ : IsOpen O₁)
    (hO₁compact : IsCompact (closure O₁))
    (hO₁O₀ : closure O₁ ⊆ O₀)
    (k : Fin d)
    (Bq Bdq : ℝ) (hBq : 0 ≤ Bq) (hBdq : 0 ≤ Bdq)
    (q : TimeVelocity d → ℝ)
    (hqMeas : AEStronglyMeasurable q
      (timeVelocityVolumeOn (Ioo t₀ t₃ ×ˢ O₀)))
    (hqC1 : ∀ r ∈ Ioo t₀ t₃,
      ContDiffOn ℝ 1 (fun y => q (r, y)) O₀)
    (hqBound : ∀ z ∈ Ioo t₀ t₃ ×ˢ O₀, |q z| ≤ Bq)
    (hdqBound : ∀ z ∈ Ioo t₀ t₃ ×ˢ O₀,
      |spatialPartial k (fun y => q (z.1, y)) z.2| ≤ Bdq)
    (u du : TimeVelocity d → ℝ)
    (hu : ParabolicMemLpOn (Ioo t₁ t₂ ×ˢ O₁) 2 u)
    (hdu : ParabolicMemLpOn (Ioo t₁ t₂ ×ˢ O₁) 2 du)
    (hweak : HasWeakVelocityPartialDerivOn
      (Ioo t₁ t₂ ×ˢ O₁) k u du) :
    AEStronglyMeasurable
        (fun z => spatialPartial k (fun y => q (z.1, y)) z.2)
        (timeVelocityVolumeOn (Ioo t₁ t₂ ×ˢ O₁)) ∧
      ParabolicMemLpOn (Ioo t₁ t₂ ×ˢ O₁) 2
        (fun z => q z * u z) ∧
      ParabolicMemLpOn (Ioo t₁ t₂ ×ˢ O₁) 2
        (fun z => q z * du z +
          spatialPartial k (fun y => q (z.1, y)) z.2 * u z) ∧
      HasWeakVelocityPartialDerivOn (Ioo t₁ t₂ ×ˢ O₁) k
        (fun z => q z * u z)
        (fun z => q z * du z +
          spatialPartial k (fun y => q (z.1, y)) z.2 * u z) ∧
      ENNReal.toReal (eLpNorm (fun z => q z * u z) 2
          (timeVelocityVolumeOn (Ioo t₁ t₂ ×ˢ O₁))) ≤
        Bq * ENNReal.toReal (eLpNorm u 2
          (timeVelocityVolumeOn (Ioo t₁ t₂ ×ˢ O₁))) ∧
      ENNReal.toReal (eLpNorm
          (fun z => q z * du z +
            spatialPartial k (fun y => q (z.1, y)) z.2 * u z) 2
          (timeVelocityVolumeOn (Ioo t₁ t₂ ×ˢ O₁))) ≤
        Bq * ENNReal.toReal (eLpNorm du 2
          (timeVelocityVolumeOn (Ioo t₁ t₂ ×ˢ O₁))) +
        Bdq * ENNReal.toReal (eLpNorm u 2
          (timeVelocityVolumeOn (Ioo t₁ t₂ ×ˢ O₁))) := by
  let Qin : Set (TimeVelocity d) := Ioo t₁ t₂ ×ˢ O₁
  let Qout : Set (TimeVelocity d) := Ioo t₀ t₃ ×ˢ O₀
  let dq : TimeVelocity d → ℝ :=
    fun z => spatialPartial k (fun y => q (z.1, y)) z.2
  have htime : Ioo t₁ t₂ ⊆ Ioo t₀ t₃ := by
    rintro r ⟨hr₁, hr₂⟩
    exact ⟨lt_trans ht₀₁ hr₁, lt_trans hr₂ ht₂₃⟩
  have hspace : O₁ ⊆ O₀ := (subset_closure : O₁ ⊆ closure O₁).trans hO₁O₀
  have hQinOut : Qin ⊆ Qout := prod_mono htime hspace
  have hQinMeas : MeasurableSet Qin := measurableSet_Ioo.prod hO₁.measurableSet
  have hQinOpen : IsOpen Qin := isOpen_Ioo.prod hO₁
  have hqMeasIn : AEStronglyMeasurable q (timeVelocityVolumeOn Qin) :=
    hqMeas.mono_measure (Measure.restrict_mono_set volume hQinOut)
  have hqBoundIn : ∀ z ∈ Qin, |q z| ≤ Bq := fun z hz => hqBound z (hQinOut hz)
  have hdqBoundIn : ∀ z ∈ Qin, |dq z| ≤ Bdq := fun z hz => hdqBound z (hQinOut hz)
  have hraw := spatialC1_hasWeakVelocityPartialDerivOn
    (hI := htime) (hIin := measurableSet_Ioo.nullMeasurableSet)
    hO₀ hO₁ hO₁compact hO₁O₀ k Bq Bdq hBq hBdq q hqMeas hqC1
      (by simpa only [Qin] using hqBoundIn) (by simpa only [Qin, dq] using hdqBoundIn)
  have hdqMeasIn : AEStronglyMeasurable dq (timeVelocityVolumeOn Qin) := by
    apply aestronglyMeasurable_spatialSliceFDeriv_apply_on_prod htime
      hQinMeas.nullMeasurableSet hO₀ hO₁compact hO₁O₀ q hqMeas
    · intro r hr y hy
      exact ((hqC1 r hr).differentiableOn (by norm_num) y hy).differentiableAt
        (hO₀.mem_nhds hy)
  have hqWeak : HasWeakVelocityPartialDerivOn Qin k q dq := by
    simpa only [Qin, dq] using hraw
  have hqAE : ∀ᵐ z ∂timeVelocityVolumeOn Qin, |q z| ≤ Bq :=
    ae_restrict_of_forall_mem Qin hQinMeas hqBoundIn
  have hdqAE : ∀ᵐ z ∂timeVelocityVolumeOn Qin, |dq z| ≤ Bdq :=
    ae_restrict_of_forall_mem Qin hQinMeas hdqBoundIn
  obtain ⟨hqu, hquNorm⟩ := toReal_eLpNorm_mul_le hBq hqMeasIn hu hqAE
  obtain ⟨hqdu, hqduNorm⟩ := toReal_eLpNorm_mul_le hBq hqMeasIn hdu hqAE
  obtain ⟨hdqu, hdquNorm⟩ := toReal_eLpNorm_mul_le hBdq hdqMeasIn hu hdqAE
  have hsum : ParabolicMemLpOn Qin 2 (fun z => q z * du z + dq z * u z) :=
    hqdu.add hdqu
  have hsumNorm : ENNReal.toReal
      (eLpNorm (fun z => q z * du z + dq z * u z) 2
        (timeVelocityVolumeOn Qin)) ≤
      Bq * ENNReal.toReal (eLpNorm du 2 (timeVelocityVolumeOn Qin)) +
        Bdq * ENNReal.toReal (eLpNorm u 2 (timeVelocityVolumeOn Qin)) := by
    have htri : eLpNorm (fun z => q z * du z + dq z * u z) 2
        (timeVelocityVolumeOn Qin) ≤
        eLpNorm (fun z => q z * du z) 2 (timeVelocityVolumeOn Qin) +
          eLpNorm (fun z => dq z * u z) 2 (timeVelocityVolumeOn Qin) := by
      exact eLpNorm_add_le (by norm_num)
    have hreal := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨hqdu.eLpNorm_ne_top, hdqu.eLpNorm_ne_top⟩) htri
    rw [ENNReal.toReal_add hqdu.eLpNorm_ne_top hdqu.eLpNorm_ne_top] at hreal
    exact hreal.trans (add_le_add hqduNorm hdquNorm)
  have hmulWeak : HasWeakVelocityPartialDerivOn Qin k
      (fun z => q z * u z) (fun z => q z * du z + dq z * u z) :=
    bounded_weak_mul hQinOpen k Bq Bdq hBq hBdq q dq u du
      hqMeasIn hdqMeasIn hqBoundIn hdqBoundIn hqWeak hu hdu hweak
  simpa only [Qin, dq] using
    And.intro hdqMeasIn (And.intro hqu (And.intro hsum
      (And.intro hmulWeak (And.intro hquNorm hsumNorm))))

/-- A scalar that is `C¹` on an open time--velocity carrier has its literal
velocity derivative as its raw weak velocity derivative there. -/
theorem contDiffOn_one_hasWeakVelocityPartialDerivOn
    {d : ℕ} (U : Set (TimeVelocity d)) (hU : IsOpen U)
    (i : Fin d)
    (q : TimeVelocity d → ℝ) (hq : ContDiffOn ℝ 1 q U) :
    HasWeakVelocityPartialDerivOn U i q
      (fun z => velocityGradient q z i) := by
  intro φ hφ hφCompact hφSub
  let p : TimeVelocity d → ℝ := fun z => q z * φ z
  let v : TimeVelocity d := (0, Pi.single i 1)
  have hp : ContDiff ℝ 1 p := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ U
    · exact (hq.contDiffAt (hU.mem_nhds hz)).mul
        ((hφ.of_le (by norm_num)).contDiffAt)
    · have hzφ : z ∉ tsupport φ := fun h => hz (hφSub h)
      have heq : p =ᶠ[𝓝 z] fun _ => 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hzφ] with y hy
        simp [p, hy]
      exact (contDiffAt_const (x := z) (n := 1) (c := (0 : ℝ))).congr_of_eventuallyEq heq
  have hpCompact : HasCompactSupport p := hφCompact.mul_left
  have hdpCompact : HasCompactSupport (fun z => fderiv ℝ p z v) :=
    hpCompact.fderiv_apply ℝ v
  have hpInt : Integrable p := hp.continuous.integrable_of_hasCompactSupport hpCompact
  have hdpInt : Integrable (fun z => fderiv ℝ p z v) :=
    ((hp.continuous_fderiv_apply (by norm_num)).comp
      (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport hdpCompact
  have hzero : (∫ z, fderiv ℝ p z v ∂volume) = 0 := by
    have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := volume) (v := v)
      (f := fun _ : TimeVelocity d => (1 : ℝ)) (g := p)
      (by simp) (by simpa using hdpInt) (by simpa using hpInt)
      (by fun_prop) (fun x _ => hp.differentiable (by norm_num) x)
    simpa using h
  have hprod (z : TimeVelocity d) (hz : z ∈ U) :
      fderiv ℝ p z v =
        velocityGradient q z i * φ z + q z * velocityGradient φ z i := by
    rw [show p = fun y => q y * φ y from rfl]
    rw [fderiv_fun_mul ((hq.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num))
      (hφ.differentiable (by simp) z)]
    simp [v, velocityGradient, add_comm, mul_comm]
  have houtside (z : TimeVelocity d) (hz : z ∉ U) :
      fderiv ℝ p z v = 0 := by
    exact congrArg (fun L => L v)
      (fderiv_of_notMem_tsupport ℝ
        (fun hp' => hz (hφSub (tsupport_mul_subset_right hp'))))
  have hglobal : (∫ z, fderiv ℝ p z v ∂volume) =
      ∫ z in U, (velocityGradient q z i * φ z +
        q z * velocityGradient φ z i) ∂volume := by
    rw [← integral_indicator hU.measurableSet]
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by
      by_cases hz : z ∈ U
      · simp [Set.indicator_of_mem hz, hprod z hz]
      · simp [Set.indicator_of_notMem hz, houtside z hz]
  rw [hglobal] at hzero
  have hleft : IntegrableOn (fun z => q z * velocityGradient φ z i) U := by
    have hc : Continuous (fun z => q z * velocityGradient φ z i) := by
      rw [continuous_iff_continuousAt]
      intro z
      by_cases hz : z ∈ U
      · exact (hq.contDiffAt (hU.mem_nhds hz)).continuousAt.mul
          ((hφ.continuous_fderiv (by simp)).clm_apply
            (continuous_const : Continuous (fun _ =>
              ((0, Pi.single i 1) : TimeVelocity d)))).continuousAt
      · have hzφ : z ∉ tsupport φ := fun h => hz (hφSub h)
        have hd := (notMem_tsupport_iff_eventuallyEq.mp hzφ).fderiv (𝕜 := ℝ)
        exact continuousAt_const.congr_of_eventuallyEq (hd.mono fun y hy => by
          change q y * fderiv ℝ φ y ((0, Pi.single i 1) : TimeVelocity d) = 0
          rw [hy]
          simp)
    exact (hc.integrable_of_hasCompactSupport
      ((hφCompact.fderiv_apply ℝ
        ((0, Pi.single i 1) : TimeVelocity d)).mul_left)).integrableOn
  have hright : IntegrableOn (fun z => velocityGradient q z i * φ z) U := by
    have hc : Continuous (fun z => velocityGradient q z i * φ z) := by
      rw [continuous_iff_continuousAt]
      intro z
      by_cases hz : z ∈ U
      · unfold velocityGradient
        exact (((hq.contDiffAt (hU.mem_nhds hz)).continuousAt_fderiv
          (by norm_num)).clm_apply
            (continuousAt_const : ContinuousAt (fun _ =>
              ((0, Pi.single i 1) : TimeVelocity d)) z)).mul
          hφ.continuous.continuousAt
      · have hzφ : z ∉ tsupport φ := fun h => hz (hφSub h)
        have heq := notMem_tsupport_iff_eventuallyEq.mp hzφ
        exact continuousAt_const.congr_of_eventuallyEq (heq.mono fun y hy => by
          change velocityGradient q y i * φ y = 0
          simp [hy])
    exact (hc.integrable_of_hasCompactSupport hφCompact.mul_left).integrableOn
  rw [integral_add hright hleft] at hzero
  linarith

/-- A bounded `C¹` multiplier obeys the weak velocity Leibniz rule on an
arbitrary open carrier, with sharp componentwise `L²` bounds. -/
theorem velocityC1_mul_hasWeakVelocityPartialDerivOn_memLp_eLpNorm_le
    {d : ℕ} {U : Set (TimeVelocity d)} (hU : IsOpen U)
    (i : Fin d)
    (Bq Bdi : ℝ) (hBq : 0 ≤ Bq) (hBdi : 0 ≤ Bdi)
    (q : TimeVelocity d → ℝ) (hqC1 : ContDiffOn ℝ 1 q U)
    (hqBound : ∀ z ∈ U, |q z| ≤ Bq)
    (hdiBound : ∀ z ∈ U, |velocityGradient q z i| ≤ Bdi)
    (u dui : TimeVelocity d → ℝ)
    (hu : ParabolicMemLpOn U 2 u)
    (hdui : ParabolicMemLpOn U 2 dui)
    (hweak : HasWeakVelocityPartialDerivOn U i u dui) :
    AEStronglyMeasurable (fun z => velocityGradient q z i)
        (timeVelocityVolumeOn U) ∧
      ParabolicMemLpOn U 2 (fun z => q z * u z) ∧
      ParabolicMemLpOn U 2
        (fun z => q z * dui z + velocityGradient q z i * u z) ∧
      HasWeakVelocityPartialDerivOn U i
        (fun z => q z * u z)
        (fun z => q z * dui z + velocityGradient q z i * u z) ∧
      ENNReal.toReal
          (eLpNorm (fun z => q z * u z) 2 (timeVelocityVolumeOn U)) ≤
        Bq * ENNReal.toReal
          (eLpNorm u 2 (timeVelocityVolumeOn U)) ∧
      ENNReal.toReal
          (eLpNorm
            (fun z => q z * dui z + velocityGradient q z i * u z)
            2 (timeVelocityVolumeOn U)) ≤
        Bq * ENNReal.toReal
          (eLpNorm dui 2 (timeVelocityVolumeOn U)) +
        Bdi * ENNReal.toReal
          (eLpNorm u 2 (timeVelocityVolumeOn U)) := by
  have hUmeas : MeasurableSet U := hU.measurableSet
  have hqMeas : AEStronglyMeasurable q (timeVelocityVolumeOn U) :=
    hqC1.continuousOn.aestronglyMeasurable hUmeas
  have hdiMeas : AEStronglyMeasurable (fun z => velocityGradient q z i)
      (timeVelocityVolumeOn U) := by
    have hc : ContinuousOn (fun z => velocityGradient q z i) U := fun z hz => by
      unfold velocityGradient
      exact ((hqC1.contDiffAt (hU.mem_nhds hz)).continuousAt_fderiv
        (by norm_num)).clm_apply
          (continuousAt_const : ContinuousAt (fun _ =>
            ((0, Pi.single i 1) : TimeVelocity d)) z)
        |>.continuousWithinAt
    exact hc.aestronglyMeasurable hUmeas
  have hqAE : ∀ᵐ z ∂timeVelocityVolumeOn U, |q z| ≤ Bq :=
    ae_restrict_of_forall_mem U hUmeas hqBound
  have hdiAE : ∀ᵐ z ∂timeVelocityVolumeOn U,
      |velocityGradient q z i| ≤ Bdi :=
    ae_restrict_of_forall_mem U hUmeas hdiBound
  obtain ⟨hqu, hquNorm⟩ := toReal_eLpNorm_mul_le hBq hqMeas hu hqAE
  obtain ⟨hqdui, hqduiNorm⟩ := toReal_eLpNorm_mul_le hBq hqMeas hdui hqAE
  obtain ⟨hdiu, hdiuNorm⟩ := toReal_eLpNorm_mul_le hBdi hdiMeas hu hdiAE
  have hsum : ParabolicMemLpOn U 2
      (fun z => q z * dui z + velocityGradient q z i * u z) := hqdui.add hdiu
  have hsumNorm : ENNReal.toReal
      (eLpNorm (fun z => q z * dui z + velocityGradient q z i * u z) 2
        (timeVelocityVolumeOn U)) ≤
      Bq * ENNReal.toReal (eLpNorm dui 2 (timeVelocityVolumeOn U)) +
        Bdi * ENNReal.toReal (eLpNorm u 2 (timeVelocityVolumeOn U)) := by
    have htri : eLpNorm
        (fun z => q z * dui z + velocityGradient q z i * u z) 2
        (timeVelocityVolumeOn U) ≤
        eLpNorm (fun z => q z * dui z) 2 (timeVelocityVolumeOn U) +
          eLpNorm (fun z => velocityGradient q z i * u z) 2
            (timeVelocityVolumeOn U) := eLpNorm_add_le (by norm_num)
    have hreal := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨hqdui.eLpNorm_ne_top, hdiu.eLpNorm_ne_top⟩) htri
    rw [ENNReal.toReal_add hqdui.eLpNorm_ne_top hdiu.eLpNorm_ne_top] at hreal
    exact hreal.trans (add_le_add hqduiNorm hdiuNorm)
  have hqWeak := contDiffOn_one_hasWeakVelocityPartialDerivOn U hU i q hqC1
  have hmulWeak : HasWeakVelocityPartialDerivOn U i
      (fun z => q z * u z)
      (fun z => q z * dui z + velocityGradient q z i * u z) :=
    bounded_weak_mul hU i Bq Bdi hBq hBdi q (fun z => velocityGradient q z i) u dui
      hqMeas hdiMeas hqBound hdiBound hqWeak hu hdui hweak
  exact ⟨hdiMeas, hqu, hsum, hmulWeak, hquNorm, hsumNorm⟩

end HypoellipticAleksandrov.Parabolic
