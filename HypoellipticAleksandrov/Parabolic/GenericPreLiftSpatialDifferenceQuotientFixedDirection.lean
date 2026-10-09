module

public import HypoellipticAleksandrov.Analysis.BoundedMultiplierLp
public import HypoellipticAleksandrov.LinearAlgebra.LoewnerEntryBound
public import HypoellipticAleksandrov.Parabolic.GenericPreLiftSpatialDifferenceQuotientEnergyIdentity
public import HypoellipticAleksandrov.Parabolic.GenericPreLiftSpatialDifferenceQuotientSafeCarrierBridge
public import HypoellipticAleksandrov.Parabolic.IntermediateSpatialCutoffCollar
public import HypoellipticAleksandrov.Parabolic.OriginalTimePlateau
public import HypoellipticAleksandrov.Parabolic.SpatialCoordinateDerivatives
public import HypoellipticAleksandrov.Parabolic.SpatialSliceDifferenceQuotientBound
public import HypoellipticAleksandrov.Parabolic.WeakDerivativeSpatialDifferenceQuotientL2Bound
public import HypoellipticAleksandrov.Parabolic.WeakJetProduct

/-!
# Fixed-direction generic spatial difference-quotient estimate

This module supplies the non-circular fixed-direction Caccioppoli estimate used by
the generic pre-lift spatial difference-quotient estimate.  The private
infrastructure below records the signed collar geometry, product-cutoff
calculus, locally square-integrable fluxes, and coefficient quotient bounds.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory Set
open scoped Convex ENNReal MatrixOrder

private theorem fixedCore_velocityGradient_contDiff_infty
    {d : ℕ} {f : TimeVelocity d → ℝ} {i : Fin d}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z ↦ velocityGradient f z i) := by
  unfold velocityGradient
  exact (contDiff_infty_iff_fderiv.mp hf).2.clm_apply contDiff_const

private theorem fixedCore_velocityGradient_compact
    {d : ℕ} {f : TimeVelocity d → ℝ} {i : Fin d}
    (hf : HasCompactSupport f) :
    HasCompactSupport (fun z ↦ velocityGradient f z i) := by
  unfold velocityGradient
  simpa using hf.fderiv_apply (𝕜 := ℝ) ((0, Pi.single i 1) : TimeVelocity d)

private theorem fixedCore_velocityGradient_tsupport_subset
    {d : ℕ} {f : TimeVelocity d → ℝ} {i : Fin d} :
    tsupport (fun z ↦ velocityGradient f z i) ⊆ tsupport f := by
  unfold velocityGradient
  change closure (Function.support (fun z ↦
    fderiv ℝ f z (0, Pi.single i 1))) ⊆ tsupport f
  refine (closure_mono ?_).trans (tsupport_fderiv_subset ℝ)
  intro z hz
  rw [Function.mem_support] at hz ⊢
  intro hzero
  apply hz
  simp [hzero]

private theorem fixedCore_timeDerivative_tsupport_subset
    {d : ℕ} {f : TimeVelocity d → ℝ} :
    tsupport (timeDerivative f) ⊆ tsupport f := by
  unfold timeDerivative
  change closure (Function.support (fun z ↦ fderiv ℝ f z (1, 0))) ⊆ tsupport f
  refine (closure_mono ?_).trans (tsupport_fderiv_subset ℝ)
  intro z hz
  rw [Function.mem_support] at hz ⊢
  intro hzero
  apply hz
  simp [hzero]

/-- A selected weak spatial derivative on an outer open carrier uniformly
controls the corresponding quotient on any carrier whose full directed
segments remain in the outer carrier.  Applying this helper to `q` and then
to a gradient component supplies the two bounds used in assembly. -/
private theorem exists_spatialDifferenceQuotient_memLp_norm_le_on_inner
    {d : ℕ} {U V : Set (TimeVelocity d)}
    (k : Fin d)
    (hU : IsOpen U) (q Gk : TimeVelocity d → ℝ)
    (hq : ParabolicMemLpOn U 2 q) (hGk : ParabolicMemLpOn U 2 Gk)
    (hweak : HasWeakVelocityPartialDerivOn U k q Gk)
    (h : ℝ) (hh : h ≠ 0)
    (hseg : ∀ z ∈ V, [z -[ℝ] spatialShift k h z] ⊆ U) :
    ∃ hqh : ParabolicMemLpOn V 2 (spatialDifferenceQuotient k h q),
      ‖hqh.toLp (spatialDifferenceQuotient k h q)‖ ≤ ‖hGk.toLp Gk‖ := by
  exact hweak.exists_spatialDifferenceQuotient_memLp_norm_le
    U hU V k h hh q Gk hq hGk hseg

/-- Localizing a quotient weak jet by a smooth compactly supported cutoff
produces global `L²` representatives with the exact ambient weak derivative
and with support retained in the local carrier. -/
private theorem localized_spatialDifferenceQuotient_weakJet_global
    {d : ℕ} {V : Set (TimeVelocity d)} (hV : IsOpen V)
    (qh : TimeVelocity d → ℝ) (H : Fin d → TimeVelocity d → ℝ)
    (hqh : ParabolicMemLpOn V 2 qh) (hH : ∀ i, ParabolicMemLpOn V 2 (H i))
    (hweak : ∀ i, HasWeakVelocityPartialDerivOn V i qh (H i))
    (w : TimeVelocity d → ℝ) (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwCompact : HasCompactSupport w) (hwSupport : tsupport w ⊆ V) :
    let psi : TimeVelocity d → ℝ := fun z ↦ w z * qh z
    let Dpsi : Fin d → TimeVelocity d → ℝ := fun i z ↦
      velocityGradient w z i * qh z + w z * H i z
    MemLp psi 2 volume ∧ (∀ i, MemLp (Dpsi i) 2 volume) ∧
      (∀ i, HasWeakVelocityPartialDerivOn Set.univ i psi (Dpsi i)) ∧
      tsupport psi ⊆ V ∧ ∀ i, tsupport (Dpsi i) ⊆ V := by
  let psi : TimeVelocity d → ℝ := fun z ↦ w z * qh z
  let Dpsi : Fin d → TimeVelocity d → ℝ := fun i z ↦
    velocityGradient w z i * qh z + w z * H i z
  have hwTop : ParabolicMemLpOn V ∞ w :=
    (hw.continuous.memLp_of_hasCompactSupport hwCompact).restrict V
  have hdwTop (i : Fin d) : ParabolicMemLpOn V ∞
      (fun z ↦ velocityGradient w z i) :=
    ((fixedCore_velocityGradient_contDiff_infty (i := i) hw).continuous.memLp_of_hasCompactSupport
      (fixedCore_velocityGradient_compact (i := i) hwCompact)).restrict V
  have hpsiV : ParabolicMemLpOn V 2 psi := by
    simpa only [psi, mul_comm] using (hwTop.mul' hqh)
  have hDpsiV (i : Fin d) : ParabolicMemLpOn V 2 (Dpsi i) := by
    have hfirst : ParabolicMemLpOn V 2
        (fun z ↦ velocityGradient w z i * qh z) := (hdwTop i).mul' hqh
    have hsecond : ParabolicMemLpOn V 2 (fun z ↦ w z * H i z) := by
      exact hwTop.mul' (hH i)
    simpa only [Dpsi, Pi.add_def] using hfirst.add hsecond
  have hpsiWeakV (i : Fin d) : HasWeakVelocityPartialDerivOn V i psi (Dpsi i) := by
    have hp := (hweak i).mul_contDiff hw
      (hqh.locallyIntegrableOn (by norm_num))
      ((hH i).locallyIntegrableOn (by norm_num))
    convert hp using 1
    funext z
    simp only [Dpsi]
    ring
  have hpsiSupport : tsupport psi ⊆ V :=
    (tsupport_mul_subset_left (f := w) (g := qh)).trans hwSupport
  have hDpsiSupport (i : Fin d) : tsupport (Dpsi i) ⊆ V := by
    refine (tsupport_add _ _).trans (union_subset ?_ ?_)
    · exact (tsupport_mul_subset_left
        (f := fun z ↦ velocityGradient w z i) (g := qh)).trans
          (fixedCore_velocityGradient_tsupport_subset.trans hwSupport)
    · exact (tsupport_mul_subset_left (f := w) (g := H i)).trans hwSupport
  have hpsiGlobal : MemLp psi 2 volume :=
    hpsiV.memLp_of_support_subset hV.measurableSet
      ((subset_tsupport psi).trans hpsiSupport)
  have hDpsiGlobal (i : Fin d) : MemLp (Dpsi i) 2 volume :=
    (hDpsiV i).memLp_of_support_subset hV.measurableSet
      ((subset_tsupport (Dpsi i)).trans (hDpsiSupport i))
  have hpsiWeakGlobal (i : Fin d) :
      HasWeakVelocityPartialDerivOn Set.univ i psi (Dpsi i) :=
    (hpsiWeakV i).univ_of_tsupport_subset hV hpsiSupport (hDpsiSupport i)
  exact ⟨hpsiGlobal, hDpsiGlobal, hpsiWeakGlobal, hpsiSupport, hDpsiSupport⟩

/-- The global weak derivative of a localized quotient controls its signed
backward spatial difference quotient with no inverse-step loss. -/
private theorem exists_backward_spatialDifferenceQuotient_memLp_norm_le
    {d : ℕ} (k : Fin d) (h : ℝ) (hh : h ≠ 0)
    (psi Dpsi : TimeVelocity d → ℝ)
    (hpsi : ParabolicMemLpOn Set.univ 2 psi)
    (hDpsi : ParabolicMemLpOn Set.univ 2 Dpsi)
    (hweak : HasWeakVelocityPartialDerivOn Set.univ k psi Dpsi) :
    ∃ hback : ParabolicMemLpOn Set.univ 2
        (spatialDifferenceQuotient k (-h) psi),
      ‖hback.toLp (spatialDifferenceQuotient k (-h) psi)‖ ≤ ‖hDpsi.toLp Dpsi‖ := by
  have hseg : ∀ z ∈ (Set.univ : Set (TimeVelocity d)),
      [z -[ℝ] spatialShift k (-h) z] ⊆ Set.univ := by
    intro z hz
    exact subset_univ _
  exact hweak.exists_spatialDifferenceQuotient_memLp_norm_le
    Set.univ isOpen_univ Set.univ k (-h) (neg_ne_zero.mpr hh)
    psi Dpsi hpsi hDpsi hseg

/-- `L²` Cauchy--Schwarz bounds the undifferenced source paired with the
backward quotient of a localized test by the localized derivative norm. -/
private theorem abs_integral_source_mul_backwardQuotient_le
    {d : ℕ} (k : Fin d) (h : ℝ) (hh : h ≠ 0)
    (R psi Dpsi : TimeVelocity d → ℝ)
    (hR : MemLp R 2 volume) (hpsi : MemLp psi 2 volume)
    (hDpsi : MemLp Dpsi 2 volume)
    (hweak : HasWeakVelocityPartialDerivOn Set.univ k psi Dpsi) :
    |∫ z, R z * spatialDifferenceQuotient k (-h) psi z| ≤
      ‖hR.toLp R‖ * ‖hDpsi.toLp Dpsi‖ := by
  have hpsiUniv : ParabolicMemLpOn Set.univ 2 psi := by
    exact hpsi.mono_measure Measure.restrict_le_self
  have hDpsiUniv : ParabolicMemLpOn Set.univ 2 Dpsi := by
    exact hDpsi.mono_measure Measure.restrict_le_self
  obtain ⟨hback, hbackNorm⟩ :=
    exists_backward_spatialDifferenceQuotient_memLp_norm_le k h hh psi Dpsi
      hpsiUniv hDpsiUniv hweak
  have hbackGlobal : MemLp (spatialDifferenceQuotient k (-h) psi) 2 volume := by
    exact hback.memLp_of_support_subset MeasurableSet.univ (subset_univ _)
  have hholder : (2 : ℝ).HolderConjugate 2 := by
    constructor <;> norm_num
  have hR' : MemLp R (ENNReal.ofReal (2 : ℝ)) volume := by simpa using hR
  have hbackGlobal' : MemLp (spatialDifferenceQuotient k (-h) psi)
      (ENNReal.ofReal (2 : ℝ)) volume := by simpa using hbackGlobal
  have hcs := integral_mul_norm_le_Lp_mul_Lq hholder hR' hbackGlobal'
  have hRNorm : (eLpNorm R 2 volume).toReal =
      (∫ z, ‖R z‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
    have heq := congrArg ENNReal.toReal
      (hR.eLpNorm_eq_integral_rpow_norm (by norm_num) ENNReal.ofNat_ne_top)
    simp only [ENNReal.toReal_ofNat] at heq
    rw [ENNReal.toReal_ofReal (by positivity)] at heq
    convert heq using 1
    norm_num
  have hbackNormEq :
      (eLpNorm (spatialDifferenceQuotient k (-h) psi) 2 volume).toReal =
        (∫ z, ‖spatialDifferenceQuotient k (-h) psi z‖ ^ (2 : ℝ)) ^
          (1 / (2 : ℝ)) := by
    have heq := congrArg ENNReal.toReal
      (hbackGlobal.eLpNorm_eq_integral_rpow_norm
        (by norm_num) ENNReal.ofNat_ne_top)
    simp only [ENNReal.toReal_ofNat] at heq
    rw [ENNReal.toReal_ofReal (by positivity)] at heq
    convert heq using 1
    norm_num
  calc
    |∫ z, R z * spatialDifferenceQuotient k (-h) psi z| =
        ‖∫ z, R z * spatialDifferenceQuotient k (-h) psi z‖ := by
          rw [Real.norm_eq_abs]
    _ ≤ ∫ z, ‖R z‖ * ‖spatialDifferenceQuotient k (-h) psi z‖ := by
      exact (norm_integral_le_integral_norm _).trans_eq <| by
        apply integral_congr_ae
        exact ae_of_all _ fun z ↦ norm_mul _ _
    _ ≤ ‖hR.toLp R‖ * ‖hbackGlobal.toLp (spatialDifferenceQuotient k (-h) psi)‖ := by
      rw [Lp.norm_toLp, Lp.norm_toLp, hRNorm, hbackNormEq]
      exact hcs
    _ ≤ ‖hR.toLp R‖ * ‖hDpsi.toLp Dpsi‖ := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      simpa only [Lp.norm_toLp, timeVelocityVolumeOn, Measure.restrict_univ] using hbackNorm

/-- The square integral of a real-valued `L²` function is the square of the
norm of its canonical `Lp` representative. -/
private theorem fixedCore_integral_sq_eq_norm_sq_toLp
    {alpha : Type*} [MeasurableSpace alpha] {mu : Measure alpha}
    (f : alpha → ℝ) (hf : MemLp f (2 : ℝ≥0∞) mu) :
    (∫ x, f x ^ 2 ∂mu) = ‖hf.toLp f‖ ^ 2 := by
  rw [Lp.norm_toLp, hf.eLpNorm_eq_integral_rpow_norm
    (by norm_num) ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofReal (Real.rpow_nonneg
    (integral_nonneg fun _ ↦ sq_nonneg _) _), ENNReal.toReal_ofNat,
    Real.norm_eq_abs, Real.rpow_two, sq_abs]
  exact (Real.rpow_inv_natCast_pow
    (integral_nonneg fun _ ↦ sq_nonneg _) (by norm_num)).symm

/-- Multiplication by a cutoff in `[0,1]` has squared `L²` norm bounded by
the corresponding singly weighted energy. -/
private theorem exists_weightedMultiplier_memLp_norm_sq_le_integral
    {d : ℕ} {V : Set (TimeVelocity d)}
    (w H : TimeVelocity d → ℝ)
    (hH : ParabolicMemLpOn V 2 H)
    (hwMeas : AEStronglyMeasurable w (timeVelocityVolumeOn V))
    (hwNonneg : ∀ᵐ z ∂timeVelocityVolumeOn V, 0 ≤ w z)
    (hwLe : ∀ᵐ z ∂timeVelocityVolumeOn V, w z ≤ 1) :
    ∃ hwH : ParabolicMemLpOn V 2 (fun z ↦ w z * H z),
      ‖hwH.toLp (fun z ↦ w z * H z)‖ ^ 2 ≤
        ∫ z in V, w z * H z ^ 2 := by
  have hwAbs : ∀ᵐ z ∂timeVelocityVolumeOn V, |w z| ≤ (1 : ℝ) := by
    filter_upwards [hwNonneg, hwLe] with z hz0 hz1
    simpa only [abs_of_nonneg hz0] using hz1
  obtain ⟨hwH, _⟩ :=
    HypoellipticAleksandrov.Analysis.memLp_mul_eLpNorm_toReal_le_of_ae_abs_le
      (by norm_num : (0 : ℝ) ≤ 1) hwMeas hH hwAbs
  have hweightedInt : Integrable (fun z ↦ w z * H z ^ 2)
      (timeVelocityVolumeOn V) := by
    refine Integrable.mono' hH.integrable_sq (hwMeas.mul hH.integrable_sq.1) ?_
    filter_upwards [hwNonneg, hwLe] with z hz0 hz1
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hz0,
      abs_of_nonneg (sq_nonneg (H z))]
    exact mul_le_of_le_one_left (sq_nonneg (H z)) hz1
  refine ⟨hwH, ?_⟩
  rw [← fixedCore_integral_sq_eq_norm_sq_toLp _ hwH]
  apply integral_mono_ae hwH.integrable_sq hweightedInt
  filter_upwards [hwNonneg, hwLe] with z hz0 hz1
  have hwSq : w z ^ 2 ≤ w z := by nlinarith
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right hwSq (sq_nonneg (H z))

/-- The cutoff-gradient multiplier has the sharp scale `2 * Keta`, with no
difference-quotient step in the bound. -/
private theorem exists_cutoffGradientMultiplier_memLp_norm_le
    {d : ℕ} {V : Set (TimeVelocity d)}
    (hV : MeasurableSet V) (k : Fin d)
    (w qh : TimeVelocity d → ℝ) (Keta : ℝ)
    (hKeta : 0 ≤ Keta) (hqh : ParabolicMemLpOn V 2 qh)
    (hDwMeas : AEStronglyMeasurable (fun z ↦ velocityGradient w z k)
      (timeVelocityVolumeOn V))
    (hDwBound : ∀ z ∈ V, |velocityGradient w z k| ≤ 2 * Keta) :
    ∃ hterm : ParabolicMemLpOn V 2
        (fun z ↦ velocityGradient w z k * qh z),
      ‖hterm.toLp (fun z ↦ velocityGradient w z k * qh z)‖ ≤
        2 * Keta * ‖hqh.toLp qh‖ := by
  have hDwAE : ∀ᵐ z ∂timeVelocityVolumeOn V,
      |velocityGradient w z k| ≤ 2 * Keta := by
    filter_upwards [ae_restrict_mem hV] with z hz
    exact hDwBound z hz
  obtain ⟨hterm, htermNorm⟩ :=
    HypoellipticAleksandrov.Analysis.memLp_mul_eLpNorm_toReal_le_of_ae_abs_le
      (mul_nonneg (by norm_num) hKeta) hDwMeas hqh hDwAE
  refine ⟨hterm, ?_⟩
  simpa only [Lp.norm_toLp] using htermNorm

/-- The localized product-rule derivative retains the singly weighted
gradient energy in its `L²` bound. -/
private theorem exists_localizedDerivative_memLp_norm_le_weighted
    {d : ℕ} {V : Set (TimeVelocity d)} (hV : MeasurableSet V)
    (k : Fin d) (qh Hk w : TimeVelocity d → ℝ) (Keta : ℝ)
    (hKeta : 0 ≤ Keta)
    (hqh : ParabolicMemLpOn V 2 qh) (hHk : ParabolicMemLpOn V 2 Hk)
    (hwMeas : AEStronglyMeasurable w (timeVelocityVolumeOn V))
    (hDwMeas : AEStronglyMeasurable (fun z ↦ velocityGradient w z k)
      (timeVelocityVolumeOn V))
    (hwNonneg : ∀ z ∈ V, 0 ≤ w z) (hwLe : ∀ z ∈ V, w z ≤ 1)
    (hDwBound : ∀ z ∈ V, |velocityGradient w z k| ≤ 2 * Keta)
    (hSupport : tsupport (fun z ↦
      velocityGradient w z k * qh z + w z * Hk z) ⊆ V) :
    ∃ hD : MemLp (fun z ↦
        velocityGradient w z k * qh z + w z * Hk z) 2 volume,
      ‖hD.toLp (fun z ↦
          velocityGradient w z k * qh z + w z * Hk z)‖ ≤
        2 * Keta * ‖hqh.toLp qh‖ +
          Real.sqrt (∫ z in V, w z * Hk z ^ 2) := by
  have hwNonnegAE : ∀ᵐ z ∂timeVelocityVolumeOn V, 0 ≤ w z := by
    filter_upwards [ae_restrict_mem hV] with z hz
    exact hwNonneg z hz
  have hwLeAE : ∀ᵐ z ∂timeVelocityVolumeOn V, w z ≤ 1 := by
    filter_upwards [ae_restrict_mem hV] with z hz
    exact hwLe z hz
  obtain ⟨hfirst, hfirstNorm⟩ := exists_cutoffGradientMultiplier_memLp_norm_le
    hV k w qh Keta hKeta hqh hDwMeas hDwBound
  obtain ⟨hsecond, hsecondSq⟩ :=
    exists_weightedMultiplier_memLp_norm_sq_le_integral
      w Hk hHk hwMeas hwNonnegAE hwLeAE
  let D : TimeVelocity d → ℝ := fun z ↦
    velocityGradient w z k * qh z + w z * Hk z
  have hDV : ParabolicMemLpOn V 2 D := hfirst.add hsecond
  have hDglobal : MemLp D 2 volume :=
    hDV.memLp_of_support_subset hV
      ((subset_tsupport D).trans (by simpa only [D] using hSupport))
  have henergyNonneg : 0 ≤ ∫ z in V, w z * Hk z ^ 2 := by
    apply integral_nonneg_of_ae
    filter_upwards [hwNonnegAE] with z hz
    exact mul_nonneg hz (sq_nonneg _)
  have hsecondNorm :
      ‖hsecond.toLp (fun z ↦ w z * Hk z)‖ ≤
        Real.sqrt (∫ z in V, w z * Hk z ^ 2) := by
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    simpa only [Real.sq_sqrt henergyNonneg] using hsecondSq
  refine ⟨hDglobal, ?_⟩
  rw [Lp.norm_toLp]
  rw [← eLpNorm_restrict_eq_of_support_subset hDglobal.aestronglyMeasurable
    ((subset_tsupport D).trans (by simpa only [D] using hSupport))]
  have htri : eLpNorm D 2 (timeVelocityVolumeOn V) ≤
      eLpNorm (fun z ↦ velocityGradient w z k * qh z) 2
          (timeVelocityVolumeOn V) +
        eLpNorm (fun z ↦ w z * Hk z) 2 (timeVelocityVolumeOn V) :=
    by
      simpa only [D, Pi.add_def] using
        (eLpNorm_add_le (f := fun z ↦ velocityGradient w z k * qh z)
          (g := fun z ↦ w z * Hk z) (μ := timeVelocityVolumeOn V) (by norm_num : 1 ≤ (2 : ℝ≥0∞)))
  have hreal := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨hfirst.eLpNorm_ne_top, hsecond.eLpNorm_ne_top⟩) htri
  rw [ENNReal.toReal_add hfirst.eLpNorm_ne_top hsecond.eLpNorm_ne_top] at hreal
  rw [Lp.norm_toLp] at hfirstNorm hsecondNorm
  exact hreal.trans (add_le_add hfirstNorm hsecondNorm)

/-- The source pairing bound used for absorption, with the gradient factor
measured by its cutoff-weighted energy rather than its unweighted norm. -/
private theorem abs_integral_source_mul_backwardQuotient_le_localized_weighted
    {d : ℕ} {V : Set (TimeVelocity d)} (hV : MeasurableSet V)
    (k : Fin d) (h : ℝ) (hh : h ≠ 0)
    (R psi qh Hk w : TimeVelocity d → ℝ) (Keta : ℝ)
    (hKeta : 0 ≤ Keta) (hR : MemLp R 2 volume) (hpsi : MemLp psi 2 volume)
    (hqh : ParabolicMemLpOn V 2 qh) (hHk : ParabolicMemLpOn V 2 Hk)
    (hwMeas : AEStronglyMeasurable w (timeVelocityVolumeOn V))
    (hDwMeas : AEStronglyMeasurable (fun z ↦ velocityGradient w z k)
      (timeVelocityVolumeOn V))
    (hwNonneg : ∀ z ∈ V, 0 ≤ w z) (hwLe : ∀ z ∈ V, w z ≤ 1)
    (hDwBound : ∀ z ∈ V, |velocityGradient w z k| ≤ 2 * Keta)
    (hSupport : tsupport (fun z ↦
      velocityGradient w z k * qh z + w z * Hk z) ⊆ V)
    (hweak : HasWeakVelocityPartialDerivOn Set.univ k psi (fun z ↦
      velocityGradient w z k * qh z + w z * Hk z)) :
    |∫ z, R z * spatialDifferenceQuotient k (-h) psi z| ≤
      ‖hR.toLp R‖ * (2 * Keta * ‖hqh.toLp qh‖ +
        Real.sqrt (∫ z in V, w z * Hk z ^ 2)) := by
  obtain ⟨hD, hDnorm⟩ := exists_localizedDerivative_memLp_norm_le_weighted
    hV k qh Hk w Keta hKeta hqh hHk hwMeas hDwMeas hwNonneg hwLe
      hDwBound hSupport
  exact (abs_integral_source_mul_backwardQuotient_le k h hh R psi _
    hR hpsi hD hweak).trans
      (mul_le_mul_of_nonneg_left hDnorm (norm_nonneg _))

/-- A coarse scalar Young inequality with the coefficient used for absorbing
one error term into elliptic coercivity. -/
private theorem mul_le_lambda_eighth_sq_add (lam a b : ℝ) (hlam : 0 < lam) :
    a * b ≤ (lam / 8) * b ^ 2 + (2 / lam) * a ^ 2 := by
  rw [show (lam / 8) * b ^ 2 + (2 / lam) * a ^ 2 =
      ((lam ^ 2 / 8) * b ^ 2 + 2 * a ^ 2) / lam by field_simp]
  rw [le_div_iff₀ hlam]
  nlinarith [sq_nonneg (lam * b - 4 * a)]

/-- Absolute values may be inserted before the coarse scalar Young bound. -/
private theorem abs_mul_le_lambda_eighth_sq_add
    (lam a b : ℝ) (hlam : 0 < lam) :
    |a * b| ≤ (lam / 8) * b ^ 2 + (2 / lam) * a ^ 2 := by
  simpa only [abs_mul, sq_abs] using
    (mul_le_lambda_eighth_sq_add lam |a| |b| hlam)

/-- The same coarse Young bound is stable under a finite sum. -/
private theorem sum_mul_le_lambda_eighth_sq_add
    {n : ℕ} (lam : ℝ) (hlam : 0 < lam) (a b : Fin n → ℝ) :
    ∑ i, a i * b i ≤
      (lam / 8) * ∑ i, b i ^ 2 + (2 / lam) * ∑ i, a i ^ 2 := by
  calc
    ∑ i, a i * b i ≤ ∑ i, ((lam / 8) * b i ^ 2 + (2 / lam) * a i ^ 2) :=
      Finset.sum_le_sum fun i _ ↦ mul_le_lambda_eighth_sq_add lam (a i) (b i) hlam
    _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

/-- The weighted source pairing is split and absorbed into the weighted
gradient energy and quotient norm, leaving only the undifferenced source
norm with a coarse coefficient depending on `lam` and `Keta`. -/
private theorem abs_integral_source_mul_backwardQuotient_le_absorbed_weighted
    {d : ℕ} {V : Set (TimeVelocity d)} (hV : MeasurableSet V)
    (k : Fin d) (h : ℝ) (hh : h ≠ 0)
    (R psi qh Hk w : TimeVelocity d → ℝ) (lam Keta : ℝ)
    (hlam : 0 < lam) (hKeta : 0 ≤ Keta)
    (hR : MemLp R 2 volume) (hpsi : MemLp psi 2 volume)
    (hqh : ParabolicMemLpOn V 2 qh) (hHk : ParabolicMemLpOn V 2 Hk)
    (hwMeas : AEStronglyMeasurable w (timeVelocityVolumeOn V))
    (hDwMeas : AEStronglyMeasurable (fun z ↦ velocityGradient w z k)
      (timeVelocityVolumeOn V))
    (hwNonneg : ∀ z ∈ V, 0 ≤ w z) (hwLe : ∀ z ∈ V, w z ≤ 1)
    (hDwBound : ∀ z ∈ V, |velocityGradient w z k| ≤ 2 * Keta)
    (hSupport : tsupport (fun z ↦
      velocityGradient w z k * qh z + w z * Hk z) ⊆ V)
    (hweak : HasWeakVelocityPartialDerivOn Set.univ k psi (fun z ↦
      velocityGradient w z k * qh z + w z * Hk z))
    (henergyNonneg : 0 ≤ ∫ z in V, w z * Hk z ^ 2) :
    |∫ z, R z * spatialDifferenceQuotient k (-h) psi z| ≤
      (lam / 8) * (∫ z in V, w z * Hk z ^ 2) +
        (1 / 8) * ‖hqh.toLp qh‖ ^ 2 +
        (2 / lam + 8 * Keta ^ 2) * ‖hR.toLp R‖ ^ 2 := by
  have hsource := abs_integral_source_mul_backwardQuotient_le_localized_weighted
    hV k h hh R psi qh Hk w Keta hKeta hR hpsi hqh hHk hwMeas hDwMeas
      hwNonneg hwLe hDwBound hSupport hweak
  have hquotient := mul_le_lambda_eighth_sq_add (1 : ℝ)
    (2 * Keta * ‖hR.toLp R‖) ‖hqh.toLp qh‖ (by norm_num)
  have henergy := mul_le_lambda_eighth_sq_add lam ‖hR.toLp R‖
    (Real.sqrt (∫ z in V, w z * Hk z ^ 2)) hlam
  rw [Real.sq_sqrt henergyNonneg] at henergy
  calc
    |∫ z, R z * spatialDifferenceQuotient k (-h) psi z| ≤
        ‖hR.toLp R‖ * (2 * Keta * ‖hqh.toLp qh‖ +
          Real.sqrt (∫ z in V, w z * Hk z ^ 2)) := hsource
    _ = (2 * Keta * ‖hR.toLp R‖) * ‖hqh.toLp qh‖ +
        ‖hR.toLp R‖ * Real.sqrt (∫ z in V, w z * Hk z ^ 2) := by ring
    _ ≤ ((1 : ℝ) / 8) * ‖hqh.toLp qh‖ ^ 2 +
          (2 / (1 : ℝ)) * (2 * Keta * ‖hR.toLp R‖) ^ 2 +
        ((lam / 8) * (∫ z in V, w z * Hk z ^ 2) +
          (2 / lam) * ‖hR.toLp R‖ ^ 2) := by linarith
    _ = (lam / 8) * (∫ z in V, w z * Hk z ^ 2) +
        (1 / 8) * ‖hqh.toLp qh‖ ^ 2 +
        (2 / lam + 8 * Keta ^ 2) * ‖hR.toLp R‖ ^ 2 := by ring

/-- A spatial coordinate-shift collar contains every full signed spacetime
segment starting in its intermediate cylinder. -/
private theorem segment_spatialShift_subset_prod_of_carrier
    {d : ℕ} {I : Set ℝ} {O₀ O₂ : Set (PDE.Vec d)} {δ h : ℝ}
    (hcarrier :
      Dirichlet.spatialCoordinateShiftCarrier (closure O₂) δ ⊆ O₀)
    (hh : |h| ≤ δ) (k : Fin d) :
    ∀ z ∈ I ×ˢ O₂, [z -[ℝ] spatialShift k h z] ⊆ I ×ˢ O₀ := by
  rintro ⟨r, y⟩ ⟨hr, hy⟩ w hw
  rw [segment_eq_image] at hw
  rcases hw with ⟨s, hs, rfl⟩
  constructor
  · simp only [spatialShift_apply]
    change (1 - s) * r + s * r ∈ I
    rwa [show (1 - s) * r + s * r = r by ring]
  · apply hcarrier
    change (1 - s) • y + s • (y + h • PDE.basisVec k) ∈
      Dirichlet.spatialCoordinateShiftCarrier (closure O₂) δ
    rw [show (1 - s) • y + s • (y + h • PDE.basisVec k) =
        y + (s * h) • PDE.basisVec k by module]
    apply Dirichlet.mem_spatialCoordinateShiftCarrier_of_mem_of_abs_le
      (subset_closure hy)
    have hs01 : 0 ≤ s ∧ s ≤ 1 := by simpa using hs
    simpa only [abs_mul, abs_of_nonneg hs01.1] using
      (mul_le_of_le_one_left (abs_nonneg h) hs01.2).trans hh

/-- The signed collar also supplies the endpoint translation required by the
quotient-test energy identity. -/
private theorem mapsTo_spatialShift_prod_of_carrier
    {d : ℕ} {I : Set ℝ} {O₀ O₂ : Set (PDE.Vec d)} {δ h : ℝ}
    (hcarrier :
      Dirichlet.spatialCoordinateShiftCarrier (closure O₂) δ ⊆ O₀)
    (hh : |h| ≤ δ) (k : Fin d) :
    MapsTo (spatialShift k h) (I ×ˢ O₂) (I ×ˢ O₀) := by
  rintro ⟨r, y⟩ ⟨hr, hy⟩
  refine ⟨?_, hcarrier ?_⟩
  · simpa only [spatialShift_apply] using hr
  exact Dirichlet.mem_spatialCoordinateShiftCarrier_of_mem_of_abs_le
    (subset_closure hy) hh

/-- The spatial projection of the signed collar contains the coordinate
segment needed by the fixed-time mean-value estimate. -/
private theorem segment_add_smul_basisVec_subset_of_carrier
    {d : ℕ} {O₀ O₂ : Set (PDE.Vec d)} {δ h : ℝ}
    (hcarrier :
      Dirichlet.spatialCoordinateShiftCarrier (closure O₂) δ ⊆ O₀)
    (hh : |h| ≤ δ) (k : Fin d) :
    ∀ y ∈ O₂, [y -[ℝ] y + h • PDE.basisVec k] ⊆ O₀ := by
  intro y hy w hw
  rw [segment_eq_image] at hw
  rcases hw with ⟨s, hs, rfl⟩
  apply hcarrier
  change (1 - s) • y + s • (y + h • PDE.basisVec k) ∈
    Dirichlet.spatialCoordinateShiftCarrier (closure O₂) δ
  rw [show (1 - s) • y + s • (y + h • PDE.basisVec k) =
      y + (s * h) • PDE.basisVec k by module]
  apply Dirichlet.mem_spatialCoordinateShiftCarrier_of_mem_of_abs_le
    (subset_closure hy)
  have hs01 : 0 ≤ s ∧ s ≤ 1 := by simpa using hs
  simpa only [abs_mul, abs_of_nonneg hs01.1] using
    (mul_le_of_le_one_left (abs_nonneg h) hs01.2).trans hh

/-- The separated product cutoff is globally smooth. -/
private theorem productCutoff_contDiff
    {d : ℕ} (zeta : ℝ → ℝ) (eta : PDE.Vec d → ℝ)
    (hzeta : ContDiff ℝ (⊤ : ℕ∞) zeta)
    (heta : ContDiff ℝ (⊤ : ℕ∞) eta) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun z : TimeVelocity d ↦ zeta z.1 * eta z.2 ^ 2) := by
  exact (hzeta.comp (contDiff_fst (𝕜 := ℝ))).mul
    ((heta.comp (contDiff_snd (𝕜 := ℝ))).pow 2)

/-- Compact support of both separated factors gives compact support of their
spacetime product. -/
private theorem productCutoff_hasCompactSupport
    {d : ℕ} (zeta : ℝ → ℝ) (eta : PDE.Vec d → ℝ)
    (hzeta : HasCompactSupport zeta) (heta : HasCompactSupport eta) :
    HasCompactSupport
      (fun z : TimeVelocity d ↦ zeta z.1 * eta z.2 ^ 2) := by
  have hprod : IsCompact (tsupport zeta ×ˢ tsupport eta) :=
    hzeta.isCompact.prod heta.isCompact
  apply HasCompactSupport.of_support_subset_isCompact hprod
  intro z hz
  have hzeta0 : zeta z.1 ≠ 0 := by
    intro hzero
    exact hz (by simp [hzero])
  have heta0 : eta z.2 ≠ 0 := by
    intro hzero
    exact hz (by simp [hzero])
  exact ⟨subset_tsupport zeta (Function.mem_support.mpr hzeta0),
    subset_tsupport eta (Function.mem_support.mpr heta0)⟩

/-- The topological support of a separated product cutoff lies in the product
of the topological supports of its factors. -/
private theorem productCutoff_tsupport_subset
    {d : ℕ} (zeta : ℝ → ℝ) (eta : PDE.Vec d → ℝ) :
    tsupport (fun z : TimeVelocity d ↦ zeta z.1 * eta z.2 ^ 2) ⊆
      tsupport zeta ×ˢ tsupport eta := by
  rw [tsupport]
  apply closure_minimal
  · intro z hz
    have hzeta0 : zeta z.1 ≠ 0 := by
      intro hzero
      exact hz (by simp [hzero])
    have heta0 : eta z.2 ≠ 0 := by
      intro hzero
      exact hz (by simp [hzero])
    exact ⟨subset_tsupport zeta (Function.mem_support.mpr hzeta0),
      subset_tsupport eta (Function.mem_support.mpr heta0)⟩
  · exact (isClosed_tsupport zeta).prod (isClosed_tsupport eta)

/-- Exact time derivative of the separated squared spatial cutoff. -/
private theorem timeDerivative_productCutoff
    {d : ℕ} (zeta : ℝ → ℝ) (eta : PDE.Vec d → ℝ)
    (hzeta : ContDiff ℝ (⊤ : ℕ∞) zeta)
    (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (z : TimeVelocity d) :
    timeDerivative (fun x : TimeVelocity d ↦ zeta x.1 * eta x.2 ^ 2) z =
      _root_.deriv zeta z.1 * eta z.2 ^ 2 := by
  unfold timeDerivative
  have hzetaDiff : DifferentiableAt ℝ (fun x : TimeVelocity d ↦ zeta x.1) z :=
    (hzeta.comp (contDiff_fst (𝕜 := ℝ))).differentiable (by simp) z
  have hetaDiff : DifferentiableAt ℝ (fun x : TimeVelocity d ↦ eta x.2) z :=
    (heta.comp (contDiff_snd (𝕜 := ℝ))).differentiable (by simp) z
  rw [show (fun x : TimeVelocity d ↦ zeta x.1 * eta x.2 ^ 2) =
      (fun x ↦ zeta x.1) * (fun x ↦ eta x.2) ^ 2 by rfl]
  rw [fderiv_mul hzetaDiff (hetaDiff.pow 2)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  change zeta z.1 * fderiv ℝ (fun x : TimeVelocity d ↦ eta x.2 ^ 2) z (1, 0) +
      eta z.2 ^ 2 * fderiv ℝ (fun x : TimeVelocity d ↦ zeta x.1) z (1, 0) = _
  rw [fderiv_fun_pow 2 hetaDiff]
  have hetaZero : fderiv ℝ (fun x : TimeVelocity d ↦ eta x.2) z (1, 0) = 0 := by
    change fderiv ℝ (eta ∘ Prod.snd) z (1, 0) = 0
    rw [fderiv_comp z (heta.differentiable (by simp) z.2)
      (differentiableAt_snd (𝕜 := ℝ)), fderiv_snd]
    simp
  have hzetaEval : fderiv ℝ (fun x : TimeVelocity d ↦ zeta x.1) z (1, 0) =
      _root_.deriv zeta z.1 := by
    change fderiv ℝ (zeta ∘ Prod.fst) z (1, 0) = _
    rw [fderiv_comp z (hzeta.differentiable (by simp) z.1)
      (differentiableAt_fst (𝕜 := ℝ)), fderiv_fst]
    rfl
  rw [hzetaEval]
  simp only [ContinuousLinearMap.smul_apply, Nat.reduceSub, pow_one,
    nsmul_eq_mul, Nat.cast_ofNat, hetaZero, mul_zero, smul_zero, zero_add]
  ring

/-- Exact velocity gradient of the separated squared spatial cutoff. -/
private theorem velocityGradient_productCutoff
    {d : ℕ} (zeta : ℝ → ℝ) (eta : PDE.Vec d → ℝ)
    (hzeta : ContDiff ℝ (⊤ : ℕ∞) zeta)
    (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (i : Fin d) (z : TimeVelocity d) :
    velocityGradient (fun x : TimeVelocity d ↦ zeta x.1 * eta x.2 ^ 2) z i =
      zeta z.1 * (2 * eta z.2 * spatialPartial i eta z.2) := by
  unfold velocityGradient
  have hzetaDiff : DifferentiableAt ℝ (fun x : TimeVelocity d ↦ zeta x.1) z :=
    (hzeta.comp (contDiff_fst (𝕜 := ℝ))).differentiable (by simp) z
  have hetaDiff : DifferentiableAt ℝ (fun x : TimeVelocity d ↦ eta x.2) z :=
    (heta.comp (contDiff_snd (𝕜 := ℝ))).differentiable (by simp) z
  rw [show (fun x : TimeVelocity d ↦ zeta x.1 * eta x.2 ^ 2) =
      (fun x ↦ zeta x.1) * (fun x ↦ eta x.2) ^ 2 by rfl]
  rw [fderiv_mul hzetaDiff (hetaDiff.pow 2)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  change zeta z.1 * fderiv ℝ (fun x : TimeVelocity d ↦ eta x.2 ^ 2) z
      (0, Pi.single i 1) + eta z.2 ^ 2 *
      fderiv ℝ (fun x : TimeVelocity d ↦ zeta x.1) z
        (0, Pi.single i 1) = _
  rw [fderiv_fun_pow 2 hetaDiff]
  have hzetaZero : fderiv ℝ (fun x : TimeVelocity d ↦ zeta x.1) z
      (0, Pi.single i 1) = 0 := by
    change fderiv ℝ (zeta ∘ Prod.fst) z (0, Pi.single i 1) = 0
    rw [fderiv_comp z (hzeta.differentiable (by simp) z.1)
      (differentiableAt_fst (𝕜 := ℝ)), fderiv_fst]
    simp
  have hetaEval : fderiv ℝ (fun x : TimeVelocity d ↦ eta x.2) z
      (0, Pi.single i 1) = spatialPartial i eta z.2 := by
    change fderiv ℝ (eta ∘ Prod.snd) z (0, Pi.single i 1) = _
    rw [fderiv_comp z (heta.differentiable (by simp) z.2)
      (differentiableAt_snd (𝕜 := ℝ)), fderiv_snd]
    rfl
  rw [hzetaZero]
  simp only [ContinuousLinearMap.smul_apply, Nat.reduceSub, pow_one,
    nsmul_eq_mul, Nat.cast_ofNat]
  rw [hetaEval]
  simp only [smul_eq_mul]
  ring

/-- On the inner product cylinder the two plateau factors make the product
cutoff exactly one. -/
private theorem productCutoff_eq_one_on_inner
    {d : ℕ} {t₁ t₂ : ℝ} {O₁ : Set (PDE.Vec d)}
    (zeta : ℝ → ℝ) (eta : PDE.Vec d → ℝ)
    (hzeta : ∀ t ∈ Icc t₁ t₂, zeta t = 1)
    (heta : ∀ y ∈ closure O₁, eta y = 1) :
    ∀ z ∈ Ioo t₁ t₂ ×ˢ O₁,
      zeta z.1 * eta z.2 ^ 2 = 1 := by
  intro z hz
  rw [hzeta z.1 ⟨hz.1.1.le, hz.1.2.le⟩, heta z.2 (subset_closure hz.2)]
  norm_num

/-- The constructed product cutoff has the exact support, shift, derivative,
and plateau properties consumed by the fixed-step energy argument. -/
private theorem productCutoff_data
    {d : ℕ} {s₀ t₁ t₂ s₁ δ Keta Kzeta : ℝ}
    {O₀ O₁ O₂ : Set (PDE.Vec d)}
    (hO₂O₀ : closure O₂ ⊆ O₀)
    (hcarrier :
      Dirichlet.spatialCoordinateShiftCarrier (closure O₂) δ ⊆ O₀)
    (eta : PDE.QuantitativeSmoothCutoff (closure O₁) O₂ Keta)
    (zeta : ℝ → ℝ)
    (hzetaSmooth : ContDiff ℝ (⊤ : ℕ∞) zeta)
    (hzetaCompact : HasCompactSupport zeta)
    (hzetaNonneg : ∀ t, 0 ≤ zeta t)
    (hzetaLe : ∀ t, zeta t ≤ 1)
    (hzetaOne : ∀ t ∈ Icc t₁ t₂, zeta t = 1)
    (hzetaSupport : tsupport zeta ⊆ Ioo s₀ s₁)
    (hzetaDeriv : ∀ t, |_root_.deriv zeta t| ≤ Kzeta) :
    let w : TimeVelocity d → ℝ := fun z ↦ zeta z.1 * eta z.2 ^ 2
    ContDiff ℝ (⊤ : ℕ∞) w ∧
      HasCompactSupport w ∧
      tsupport w ⊆ Ioo s₀ s₁ ×ˢ O₀ ∧
      (∀ (k : Fin d) (h : ℝ), |h| ≤ δ →
        MapsTo (spatialShift k h) (tsupport w)
          (Ioo s₀ s₁ ×ˢ O₀)) ∧
      (∀ z, timeDerivative w z = _root_.deriv zeta z.1 * eta z.2 ^ 2) ∧
      (∀ i z, velocityGradient w z i =
        zeta z.1 * (2 * eta z.2 * spatialPartial i eta z.2)) ∧
      (∀ z, |timeDerivative w z| ≤ Kzeta) ∧
      (∀ i z, |velocityGradient w z i| ≤ 2 * Keta) ∧
      (∀ z, 0 ≤ w z ∧ w z ≤ 1) ∧
      (∀ i z, (velocityGradient w z i) ^ 2 ≤
        4 * Keta ^ 2 * w z) ∧
      (∀ z, w z ^ 2 ≤ w z) ∧
      (∀ z ∈ Ioo t₁ t₂ ×ˢ O₁, w z = 1) := by
  classical
  let w : TimeVelocity d → ℝ := fun z ↦ zeta z.1 * eta z.2 ^ 2
  have hsupp : tsupport w ⊆ tsupport zeta ×ˢ tsupport eta :=
    productCutoff_tsupport_subset zeta eta
  have hsuppOuter : tsupport w ⊆ Ioo s₀ s₁ ×ˢ O₀ := by
    intro z hz
    exact ⟨hzetaSupport (hsupp hz).1,
      hO₂O₀ (subset_closure (eta.tsupport_subset (hsupp hz).2))⟩
  have hshift : ∀ (k : Fin d) (h : ℝ), |h| ≤ δ →
      MapsTo (spatialShift k h) (tsupport w) (Ioo s₀ s₁ ×ˢ O₀) := by
    intro k h hh z hz
    exact mapsTo_spatialShift_prod_of_carrier hcarrier hh k
      ⟨hzetaSupport (hsupp hz).1, eta.tsupport_subset (hsupp hz).2⟩
  refine ⟨productCutoff_contDiff zeta eta hzetaSmooth eta.smooth,
    productCutoff_hasCompactSupport zeta eta hzetaCompact eta.hasCompactSupport,
    hsuppOuter, hshift, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun z ↦ timeDerivative_productCutoff zeta eta hzetaSmooth eta.smooth z
  · exact fun i z ↦ velocityGradient_productCutoff zeta eta hzetaSmooth eta.smooth i z
  · intro z
    rw [timeDerivative_productCutoff zeta eta hzetaSmooth eta.smooth z, abs_mul]
    have hetaAbs : |eta z.2| ≤ 1 := by
      rw [abs_of_nonneg (eta.nonneg z.2)]
      exact eta.le_one z.2
    have hetaSq : |eta z.2 ^ 2| ≤ 1 := by
      rw [abs_pow]
      nlinarith [abs_nonneg (eta z.2)]
    nlinarith [hzetaDeriv z.1, abs_nonneg (_root_.deriv zeta z.1)]
  · intro i z
    rw [velocityGradient_productCutoff zeta eta hzetaSmooth eta.smooth i z]
    have hzetaAbs : |zeta z.1| ≤ 1 := by
      rw [abs_of_nonneg (hzetaNonneg z.1)]
      exact hzetaLe z.1
    have hetaAbs : |eta z.2| ≤ 1 := by
      rw [abs_of_nonneg (eta.nonneg z.2)]
      exact eta.le_one z.2
    have hpartial : |spatialPartial i eta z.2| ≤ Keta := by
      simpa only [spatialPartial, PDE.classicalGradient_apply] using
        eta.abs_classicalGradient_apply_le z.2 i
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      |zeta z.1| * (2 * |eta z.2| * |spatialPartial i eta z.2|) ≤
          1 * (2 * 1 * Keta) := by
        gcongr
      _ = 2 * Keta := by ring
  · intro z
    constructor
    · exact mul_nonneg (hzetaNonneg z.1) (sq_nonneg (eta z.2))
    · have hetaSq : eta z.2 ^ 2 ≤ 1 := by
        nlinarith [eta.nonneg z.2, eta.le_one z.2]
      exact (mul_le_mul (hzetaLe z.1) hetaSq (sq_nonneg _) zero_le_one).trans_eq
        (one_mul 1)
  · intro i z
    rw [velocityGradient_productCutoff zeta eta hzetaSmooth eta.smooth i z]
    have hpartial : |spatialPartial i eta z.2| ≤ Keta := by
      simpa only [spatialPartial, PDE.classicalGradient_apply] using
        eta.abs_classicalGradient_apply_le z.2 i
    have hpartialSq : (spatialPartial i eta z.2) ^ 2 ≤ Keta ^ 2 := by
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans hpartial)).2 hpartial
    have hzetaSq : zeta z.1 ^ 2 ≤ zeta z.1 := by
      nlinarith [hzetaNonneg z.1, hzetaLe z.1]
    have hetaSq : 0 ≤ eta z.2 ^ 2 := sq_nonneg _
    have hzetaFactor :
        4 * zeta z.1 ^ 2 * eta z.2 ^ 2 ≤ 4 * zeta z.1 * eta z.2 ^ 2 := by
      have h := mul_le_mul_of_nonneg_left hzetaSq
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hetaSq)
      nlinarith
    calc
      (zeta z.1 * (2 * eta z.2 * spatialPartial i eta z.2)) ^ 2 =
          4 * zeta z.1 ^ 2 * eta z.2 ^ 2 *
            (spatialPartial i eta z.2) ^ 2 := by ring
      _ ≤ 4 * zeta z.1 * eta z.2 ^ 2 * Keta ^ 2 := by
        have hfourZetaEta : 0 ≤ 4 * zeta z.1 * eta z.2 ^ 2 :=
          mul_nonneg (mul_nonneg (by norm_num) (hzetaNonneg z.1)) hetaSq
        exact (mul_le_mul_of_nonneg_right hzetaFactor (sq_nonneg _)).trans
          (mul_le_mul_of_nonneg_left hpartialSq hfourZetaEta)
      _ = 4 * Keta ^ 2 * (zeta z.1 * eta z.2 ^ 2) := by ring
  · intro z
    have hw0 : 0 ≤ zeta z.1 * eta z.2 ^ 2 :=
      mul_nonneg (hzetaNonneg z.1) (sq_nonneg _)
    have hw1 : zeta z.1 * eta z.2 ^ 2 ≤ 1 := by
      have hetaSq : eta z.2 ^ 2 ≤ 1 := by
        nlinarith [eta.nonneg z.2, eta.le_one z.2]
      nlinarith [mul_le_mul (hzetaLe z.1) hetaSq
        (sq_nonneg (eta z.2)) zero_le_one]
    nlinarith
  · exact productCutoff_eq_one_on_inner zeta eta hzetaOne eta.eq_one_on_inner

/-- Two-sided Loewner control makes each local coefficient flux entry square
integrable on compact subsets of the outer cylinder. -/
private theorem fluxEntry_parabolicMemLpOn_compact
    {d : ℕ} {U K : Set (TimeVelocity d)} {lam Lam : ℝ}
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (A : TimeVelocity d → PDE.Mat d)
    (hEll : ∀ z ∈ U,
      lam • (1 : PDE.Mat d) ≤ A z ∧ A z ≤ Lam • (1 : PDE.Mat d))
    (hA : ∀ i j, ContDiffOn ℝ 1 (fun z : TimeVelocity d ↦ A z i j) U)
    (G : Fin d → TimeVelocity d → ℝ)
    (hG : ∀ j, ParabolicMemLpOn U 2 (G j))
    (i j : Fin d) :
    ParabolicMemLpOn K 2 (fun z ↦ A z i j * G j z) := by
  have hKmeas : MeasurableSet K := hK.measurableSet
  have haMeas : AEStronglyMeasurable (fun z : TimeVelocity d ↦ A z i j)
      (timeVelocityVolumeOn K) :=
    (hA i j).continuousOn.mono hKU |>.aestronglyMeasurable hKmeas
  have hGK : ParabolicMemLpOn K 2 (G j) := (hG j).mono hKU
  have haBound : ∀ᵐ z ∂timeVelocityVolumeOn K, |A z i j| ≤ Lam := by
    filter_upwards [ae_restrict_mem hKmeas] with z hz
    exact abs_apply_le_of_loewner hlam (hEll z (hKU hz)).1
      (hEll z (hKU hz)).2 i j
  exact (HypoellipticAleksandrov.Analysis.memLp_mul_eLpNorm_toReal_le_of_ae_abs_le
    (hlam.le.trans hlamLam) haMeas hGK haBound).1

/-- Joint `C¹` coefficient regularity and the signed collar convert the
displayed spatial derivative bound into a uniform coefficient quotient bound. -/
private theorem coefficient_spatialDifferenceQuotient_bound
    {d : ℕ} {s₀ s₁ : ℝ} {O₀ O₂ : Set (PDE.Vec d)} {δ h Ma : ℝ}
    (hO₀ : IsOpen O₀)
    (hcarrier :
      Dirichlet.spatialCoordinateShiftCarrier (closure O₂) δ ⊆ O₀)
    (hh : |h| ≤ δ)
    (A : TimeVelocity d → PDE.Mat d)
    (hA : ∀ i j, ContDiffOn ℝ 1 (fun z : TimeVelocity d ↦ A z i j)
      (Ioo s₀ s₁ ×ˢ O₀))
    (hbound : ∀ i j k z, z ∈ Ioo s₀ s₁ ×ˢ O₀ →
      |spatialPartial k (fun y : PDE.Vec d ↦ A (z.1, y) i j) z.2| ≤ Ma) :
    ∀ i j k z, z ∈ Ioo s₀ s₁ ×ˢ O₂ →
      |spatialDifferenceQuotient k h (fun x ↦ A x i j) z| ≤ Ma := by
  intro i j k z hz
  exact abs_spatialDifferenceQuotient_le_of_spatialSliceFDeriv_bound
    (f := fun x ↦ A x i j) (δ := δ)
    (fun ell g y hg hy ↦
      segment_add_smul_basisVec_subset_of_carrier hcarrier hg ell y hy)
    (fun r hr y hy ↦ by
      have hjoint : DifferentiableAt ℝ (fun z : TimeVelocity d ↦ A z i j) (r, y) :=
        ((hA i j (r, y) ⟨hr, hy⟩).differentiableWithinAt (by norm_num)).differentiableAt
          ((isOpen_Ioo.prod hO₀).mem_nhds ⟨hr, hy⟩)
      exact hjoint.comp y
        ((differentiableAt_const (c := r)).prodMk differentiableAt_id))
    (fun r hr ell y hy ↦ hbound i j ell (r, y) ⟨hr, hy⟩)
    k h z hh hz

/-- Exact forward product expansion of one row of the principal flux. -/
private theorem spatialDifferenceQuotient_principalFluxRow
    {d : ℕ} (A : TimeVelocity d → PDE.Mat d)
    (G : Fin d → TimeVelocity d → ℝ) (i k : Fin d) (h : ℝ) :
    spatialDifferenceQuotient k h (fun x ↦ ∑ j : Fin d, A x i j * G j x) =
      fun z ↦ ∑ j : Fin d, (
        spatialTranslate k h (fun x ↦ A x i j) z *
            spatialDifferenceQuotient k h (G j) z +
          spatialDifferenceQuotient k h (fun x ↦ A x i j) z * G j z) := by
  funext z
  simp only [spatialDifferenceQuotient_apply, spatialTranslate_apply]
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The absorbed source estimate only needs square integrability of the source
on the carrier on which the energy identity is integrated. -/
private theorem abs_setIntegral_source_mul_backwardQuotient_le_absorbed_weighted
    {d : ℕ} {S V : Set (TimeVelocity d)}
    (hS : MeasurableSet S) (hV : MeasurableSet V)
    (k : Fin d) (h : ℝ) (hh : h ≠ 0)
    (R psi qh Hk w : TimeVelocity d → ℝ) (lam Keta : ℝ)
    (hlam : 0 < lam) (hKeta : 0 ≤ Keta)
    (hR : ParabolicMemLpOn S 2 R) (hpsi : MemLp psi 2 volume)
    (hqh : ParabolicMemLpOn V 2 qh) (hHk : ParabolicMemLpOn V 2 Hk)
    (hwMeas : AEStronglyMeasurable w (timeVelocityVolumeOn V))
    (hDwMeas : AEStronglyMeasurable (fun z ↦ velocityGradient w z k)
      (timeVelocityVolumeOn V))
    (hwNonneg : ∀ z ∈ V, 0 ≤ w z) (hwLe : ∀ z ∈ V, w z ≤ 1)
    (hDwBound : ∀ z ∈ V, |velocityGradient w z k| ≤ 2 * Keta)
    (hSupport : tsupport (fun z ↦
      velocityGradient w z k * qh z + w z * Hk z) ⊆ V)
    (hweak : HasWeakVelocityPartialDerivOn Set.univ k psi (fun z ↦
      velocityGradient w z k * qh z + w z * Hk z))
    (henergyNonneg : 0 ≤ ∫ z in V, w z * Hk z ^ 2) :
    |∫ z in S, R z * spatialDifferenceQuotient k (-h) psi z| ≤
      (lam / 8) * (∫ z in V, w z * Hk z ^ 2) +
        (1 / 8) * ‖hqh.toLp qh‖ ^ 2 +
        (2 / lam + 8 * Keta ^ 2) * ‖hR.toLp R‖ ^ 2 := by
  let R0 : TimeVelocity d → ℝ := S.indicator R
  have hR0 : MemLp R0 2 volume := by
    exact (memLp_indicator_iff_restrict hS).2 hR
  have hmain := abs_integral_source_mul_backwardQuotient_le_absorbed_weighted
    hV k h hh R0 psi qh Hk w lam Keta hlam hKeta hR0 hpsi hqh hHk
      hwMeas hDwMeas hwNonneg hwLe hDwBound hSupport hweak henergyNonneg
  have hnorm : ‖hR0.toLp R0‖ = ‖hR.toLp R‖ := by
    simp only [Lp.norm_toLp, R0, eLpNorm_indicator_eq_eLpNorm_restrict hS]
  rw [hnorm] at hmain
  have heq : (∫ z, R0 z * spatialDifferenceQuotient k (-h) psi z) =
      ∫ z in S, R z * spatialDifferenceQuotient k (-h) psi z := by
    rw [← integral_indicator hS]
    apply integral_congr_ae
    exact ae_of_all _ fun z ↦ by
      by_cases hz : z ∈ S <;> simp [R0, hz]
  rwa [heq] at hmain

/-- A bounded time-cutoff derivative controls the absolute time contribution;
no sign of the derivative is required. -/
private theorem abs_setIntegral_timeDerivative_mul_sq_le
    {d : ℕ} {V : Set (TimeVelocity d)} (hV : MeasurableSet V)
    (Q w : TimeVelocity d → ℝ) (Kzeta : ℝ)
    (hQ : ParabolicMemLpOn V 2 Q)
    (hint : Integrable (fun z ↦ timeDerivative w z * Q z ^ 2)
      (timeVelocityVolumeOn V))
    (hbound : ∀ z ∈ V, |timeDerivative w z| ≤ Kzeta)
    (hKzeta : 0 ≤ Kzeta) :
    |∫ z in V, timeDerivative w z * Q z ^ 2| ≤
      Kzeta * ‖hQ.toLp Q‖ ^ 2 := by
  have _hKzeta := hKzeta
  rw [abs_le]
  constructor
  · calc
      -(Kzeta * ‖hQ.toLp Q‖ ^ 2) =
          ∫ z in V, -(Kzeta * Q z ^ 2) := by
            rw [integral_neg, integral_const_mul,
              fixedCore_integral_sq_eq_norm_sq_toLp Q hQ]
      _ ≤ ∫ z in V, timeDerivative w z * Q z ^ 2 := by
        apply integral_mono_ae
        · exact hQ.integrable_sq.const_mul Kzeta |>.neg
        · exact hint
        filter_upwards [ae_restrict_mem hV] with z hz
        have hzbound := hbound z hz
        rw [abs_le] at hzbound
        simpa only [neg_mul] using
          mul_le_mul_of_nonneg_right hzbound.1 (sq_nonneg (Q z))
  · calc
      ∫ z in V, timeDerivative w z * Q z ^ 2 ≤
          ∫ z in V, Kzeta * Q z ^ 2 := by
        apply integral_mono_ae hint (hQ.integrable_sq.const_mul Kzeta)
        filter_upwards [ae_restrict_mem hV] with z hz
        exact mul_le_mul_of_nonneg_right
          ((le_abs_self _).trans (hbound z hz)) (sq_nonneg (Q z))
      _ = Kzeta * ‖hQ.toLp Q‖ ^ 2 := by
        rw [integral_const_mul, fixedCore_integral_sq_eq_norm_sq_toLp Q hQ]

/-- Restriction to a plateau carrier preserves every component's `L²`
membership and bounds the sum of its squared norms by the weighted outer
energy. -/
private theorem memLpOn_inner_and_sum_norm_sq_le_weighted
    {d n : ℕ} {outer inner : Set (TimeVelocity d)}
    (hOuter : MeasurableSet outer) (hInner : MeasurableSet inner)
    (hInnerOuter : inner ⊆ outer)
    (H : Fin n → TimeVelocity d → ℝ) (w : TimeVelocity d → ℝ)
    (hH : ∀ i, ParabolicMemLpOn outer 2 (H i))
    (hwMeas : AEStronglyMeasurable w (timeVelocityVolumeOn outer))
    (hwNonneg : ∀ z ∈ outer, 0 ≤ w z) (hwLe : ∀ z ∈ outer, w z ≤ 1)
    (hwOne : ∀ z ∈ inner, w z = 1) :
    (∀ i, ParabolicMemLpOn inner 2 (H i)) ∧
      ∑ i, ‖((hH i).mono hInnerOuter).toLp (H i)‖ ^ 2 ≤
        ∫ z in outer, w z * ∑ i, H i z ^ 2 := by
  let hHi (i : Fin n) : ParabolicMemLpOn inner 2 (H i) :=
    (hH i).mono hInnerOuter
  have hsumInt : Integrable (fun z ↦ ∑ i, H i z ^ 2)
      (timeVelocityVolumeOn outer) :=
    integrable_finset_sum _ fun i _ ↦ (hH i).integrable_sq
  have hweightedInt : Integrable (fun z ↦ w z * ∑ i, H i z ^ 2)
      (timeVelocityVolumeOn outer) := by
    refine Integrable.mono' hsumInt (hwMeas.mul hsumInt.1) ?_
    filter_upwards [ae_restrict_mem hOuter] with z hz
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hwNonneg z hz),
      abs_of_nonneg (Finset.sum_nonneg fun i _ ↦ sq_nonneg (H i z))]
    exact mul_le_of_le_one_left
      (Finset.sum_nonneg fun i _ ↦ sq_nonneg (H i z)) (hwLe z hz)
  refine ⟨fun i ↦ hHi i, ?_⟩
  calc
    ∑ i, ‖(hHi i).toLp (H i)‖ ^ 2 =
        ∫ z in inner, ∑ i, H i z ^ 2 := by
      rw [integral_finset_sum]
      · simp_rw [fixedCore_integral_sq_eq_norm_sq_toLp (H _) (hHi _)]
      · exact fun i _ ↦ (hHi i).integrable_sq
    _ = ∫ z in inner, w z * ∑ i, H i z ^ 2 := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hInner] with z hz
      rw [hwOne z hz, one_mul]
    _ ≤ ∫ z in outer, w z * ∑ i, H i z ^ 2 := by
      apply integral_mono_measure
      · exact Measure.restrict_mono hInnerOuter le_rfl
      · filter_upwards [ae_restrict_mem hOuter] with z hz
        exact mul_nonneg (hwNonneg z hz)
          (Finset.sum_nonneg fun i _ ↦ sq_nonneg (H i z))
      · exact hweightedInt

/-- Scalar assembly for the Caccioppoli estimate.  Its equality and inequality
premises are outputs of the energy, coercivity, time, and source lemmas; this
private helper is not an admissible replacement for any of those PDE steps. -/
private theorem caccioppoli_combination_of_energy_bounds
    (lam Gamma Kzeta Keta E Ek flux time source qSq gSq rSq qNormSq gNormSq rNormSq : ℝ)
    (hlam : 0 < lam) (hE : 0 ≤ E) (hEkE : Ek ≤ E)
    (henergy : flux = -(1 / 2) * time + source)
    (hcoercive : (lam / 2) * E ≤ flux + Gamma * (qSq + gSq))
    (htime : |time| ≤ Kzeta * qSq)
    (hsource : |source| ≤ (lam / 8) * Ek + (1 / 8) * qSq +
      (2 / lam + 8 * Keta ^ 2) * rSq)
    (hqSq : qSq = qNormSq) (hgSq : gSq = gNormSq) (hrSq : rSq = rNormSq) :
    (lam / 4) * E ≤
      (Gamma + Kzeta / 2 + 1 / 8) * qNormSq + Gamma * gNormSq +
        (2 / lam + 8 * Keta ^ 2) * rNormSq := by
  have htimeUpper : -(1 / 2) * time ≤ (Kzeta / 2) * qSq := by
    have hnegTime : -time ≤ Kzeta * qSq := (neg_le_abs time).trans htime
    nlinarith
  have hsourceUpper : source ≤ (lam / 8) * Ek + (1 / 8) * qSq +
      (2 / lam + 8 * Keta ^ 2) * rSq :=
    (le_abs_self source).trans hsource
  rw [hqSq, hgSq] at hcoercive
  rw [hqSq] at htimeUpper
  rw [hqSq, hrSq] at hsourceUpper
  rw [henergy] at hcoercive
  nlinarith [mul_nonneg (le_of_lt hlam) hE]

private theorem caccioppoli_final_constant_bound
    (scale A beta qSq gSq rSq : ℝ)
    (hscale : 0 ≤ scale) (hA : 0 ≤ A) (hbeta : 0 ≤ beta)
    (hq : 0 ≤ qSq) (hg : 0 ≤ gSq) (hr : 0 ≤ rSq) :
    scale * (A * gSq + beta * rSq) ≤
      (scale * (A + beta + 1)) * (qSq + gSq + rSq) := by
  have htotal : 0 ≤ qSq + gSq + rSq := by positivity
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hscale
  calc
    A * gSq + beta * rSq ≤ A * (qSq + gSq + rSq) +
        beta * (qSq + gSq + rSq) := by
      gcongr <;> linarith
    _ = (A + beta) * (qSq + gSq + rSq) := by ring
    _ ≤ (A + beta + 1) * (qSq + gSq + rSq) := by
      exact mul_le_mul_of_nonneg_right (by linarith) htotal

/-- Uniform one-direction spatial difference-quotient control for the gradient
in a tested divergence-form equation. -/
theorem exists_fixedDirection_gradient_spatialDifferenceQuotient_estimate_of_testedEquation
    (d : ℕ) (s₀ t₁ t₂ s₁ : ℝ)
    (hs₀t₁ : s₀ < t₁) (ht₁t₂ : t₁ < t₂) (ht₂s₁ : t₂ < s₁)
    (O₀ O₁ : Set (PDE.Vec d))
    (hO₀ : IsOpen O₀) (hO₁ : IsOpen O₁) (hO₁ne : O₁.Nonempty)
    (hO₁compact : IsCompact (closure O₁))
    (hO₁O₀ : closure O₁ ⊆ O₀)
    (lam Lam Ma : ℝ)
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam) (hMa : 0 ≤ Ma) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ (A : TimeVelocity d → PDE.Mat d) (q : TimeVelocity d → ℝ)
        (G : Fin d → TimeVelocity d → ℝ) (R : TimeVelocity d → ℝ),
        (∀ z ∈ Set.Ioo s₀ s₁ ×ˢ O₀, (A z).IsSymm) →
        (∀ z ∈ Set.Ioo s₀ s₁ ×ˢ O₀,
          lam • (1 : PDE.Mat d) ≤ A z ∧ A z ≤ Lam • (1 : PDE.Mat d)) →
        (∀ i j, ContDiffOn ℝ 1 (fun z : TimeVelocity d => A z i j)
          (Set.Ioo s₀ s₁ ×ˢ O₀)) →
        (∀ i j k z, z ∈ Set.Ioo s₀ s₁ ×ˢ O₀ →
          |spatialPartial k
              (fun y : PDE.Vec d => A (z.1, y) i j) z.2| ≤ Ma) →
        ParabolicMemLpOn (Set.Ioo s₀ s₁ ×ˢ O₀) 2 q →
        (∀ j, ParabolicMemLpOn (Set.Ioo s₀ s₁ ×ˢ O₀) 2 (G j)) →
        ParabolicMemLpOn (Set.Ioo s₀ s₁ ×ˢ O₀) 2 R →
        (∀ j, HasWeakVelocityPartialDerivOn
          (Set.Ioo s₀ s₁ ×ˢ O₀) j q (G j)) →
        (∀ φ : TimeVelocity d → ℝ,
          ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          tsupport φ ⊆ Set.Ioo s₀ s₁ ×ˢ O₀ →
          -(∫ z in Set.Ioo s₀ s₁ ×ˢ O₀,
              q z * timeDerivative φ z) -
              (∑ i, ∑ j, ∫ z in Set.Ioo s₀ s₁ ×ˢ O₀,
                A z i j * G j z * velocityGradient φ z i) =
            ∫ z in Set.Ioo s₀ s₁ ×ˢ O₀, R z * φ z) →
        ∀ k : Fin d, ∀ h : ℝ, 0 < h → h < δ →
          (∀ j, ParabolicMemLpOn (Set.Ioo t₁ t₂ ×ˢ O₁) 2
            (spatialDifferenceQuotient k h (G j))) ∧
          (∑ j, (ENNReal.toReal (eLpNorm
            (spatialDifferenceQuotient k h (G j)) 2
            (timeVelocityVolumeOn (Set.Ioo t₁ t₂ ×ˢ O₁)))) ^ 2) ≤
            C * ((ENNReal.toReal (eLpNorm q 2
              (timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O₀)))) ^ 2 +
              (∑ j, (ENNReal.toReal (eLpNorm (G j) 2
                (timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O₀)))) ^ 2) +
              (ENNReal.toReal (eLpNorm R 2
                (timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O₀)))) ^ 2) := by
  classical
  obtain ⟨O₂, Keta, eta, δ, hO₂, hO₂compact, hO₁O₂, hO₂O₀,
      hKeta, hδ, hcarrier⟩ :=
    exists_intermediateSpatialCutoff_signedCollar O₀ O₁ hO₀ hO₁compact hO₁O₀
  obtain ⟨zeta, Kzeta, hzetaSmooth, hzetaCompact, hKzeta, hzetaNonneg,
      hzetaLe, hzetaOne, hzetaSupport, hzetaDeriv⟩ :=
    exists_smooth_timePlateau_with_deriv_bound s₀ t₁ t₂ s₁
      hs₀t₁ ht₁t₂.le ht₂s₁
  let Gamma : ℝ :=
    8 * (d : ℝ) ^ 3 / lam * Lam ^ 2 * Keta ^ 2 +
      2 * (d : ℝ) ^ 2 / lam * Ma ^ 2 +
      ((d : ℝ) ^ 2 + (d : ℝ)) * Ma * Keta
  let beta : ℝ := 2 / lam + 8 * Keta ^ 2
  let C : ℝ := (4 / lam) * (2 * Gamma + Kzeta / 2 + 1 / 8 + beta + 1)
  have hGamma : 0 ≤ Gamma := by
    dsimp [Gamma]
    positivity
  have hbeta : 0 ≤ beta := by
    dsimp [beta]
    positivity
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, δ, hC, hδ, ?_⟩
  intro A q G R hSymm hEll hA hAbound hq hG hR hWeak hEq k h hh hhd
  let S : Set (TimeVelocity d) := Ioo s₀ s₁ ×ˢ O₀
  let V : Set (TimeVelocity d) := Ioo s₀ s₁ ×ˢ O₂
  let inner : Set (TimeVelocity d) := Ioo t₁ t₂ ×ˢ O₁
  let w : TimeVelocity d → ℝ := fun z ↦ zeta z.1 * eta z.2 ^ 2
  let Q : TimeVelocity d → ℝ := spatialDifferenceQuotient k h q
  let H : Fin d → TimeVelocity d → ℝ := fun i ↦ spatialDifferenceQuotient k h (G i)
  have hSopen : IsOpen S := isOpen_Ioo.prod hO₀
  have hVopen : IsOpen V := isOpen_Ioo.prod hO₂
  have hSmeas : MeasurableSet S := hSopen.measurableSet
  have hVmeas : MeasurableSet V := hVopen.measurableSet
  have hinnerMeas : MeasurableSet inner := (isOpen_Ioo.prod hO₁).measurableSet
  have hVS : V ⊆ S := prod_mono_right (subset_closure.trans hO₂O₀)
  have hinnerV : inner ⊆ V := by
    rintro z ⟨hztime, hzspace⟩
    exact ⟨⟨hs₀t₁.trans hztime.1, hztime.2.trans ht₂s₁⟩,
      hO₁O₂ (subset_closure hzspace)⟩
  have habsh : |h| ≤ δ := by rw [abs_of_pos hh]; exact hhd.le
  have hseg : ∀ z ∈ V, [z -[ℝ] spatialShift k h z] ⊆ S := by
    exact segment_spatialShift_subset_prod_of_carrier hcarrier habsh k
  have hshiftV : MapsTo (spatialShift k h) V S :=
    mapsTo_spatialShift_prod_of_carrier hcarrier habsh k
  obtain ⟨hQ, hQnorm⟩ :=
    exists_spatialDifferenceQuotient_memLp_norm_le_on_inner k hSopen q (G k)
      hq (hG k) (hWeak k) h hh.ne' hseg
  have hH (i : Fin d) : ParabolicMemLpOn V 2 (H i) := by
    exact (hG i).spatialDifferenceQuotient_of_subset_mapsTo k h hVS hshiftV
  have hQweak (i : Fin d) : HasWeakVelocityPartialDerivOn V i Q (H i) := by
    exact (hWeak i).spatialDifferenceQuotient_of_subset_mapsTo
      (hq.locallyIntegrableOn (by norm_num))
      ((hG i).locallyIntegrableOn (by norm_num)) k h hVS hshiftV
  obtain ⟨hwSmooth, hwCompact, hwSupportS, hwShiftS, hwTime, hwGrad,
      hwTimeBound, hwGradBound, hwBounds, hwGradSq, hwSq, hwOne⟩ :=
    productCutoff_data hO₂O₀ hcarrier eta zeta hzetaSmooth hzetaCompact
      hzetaNonneg hzetaLe hzetaOne hzetaSupport hzetaDeriv
  have hwSupportV : tsupport w ⊆ V := by
    refine (productCutoff_tsupport_subset zeta eta).trans ?_
    intro z hz
    exact ⟨hzetaSupport hz.1, eta.tsupport_subset hz.2⟩
  obtain ⟨hpsi, hDpsi, hpsiWeak, hpsiSupport, hDpsiSupport⟩ :=
    localized_spatialDifferenceQuotient_weakJet_global hVopen Q H hQ hH hQweak
      w hwSmooth hwCompact hwSupportV
  have hFlux (i j : Fin d) (K : Set (TimeVelocity d))
      (hK : IsCompact K) (hKS : K ⊆ S) :
      ParabolicMemLpOn K 2 (fun z ↦ A z i j * G j z) :=
    fluxEntry_parabolicMemLpOn_compact hK hKS hlam hlamLam A hEll hA G hG i j
  obtain ⟨htimeInt, hfluxInt, hsourceInt, henergy⟩ :=
    integral_spatialDifferenceQuotient_energyIdentity_of_testedEquation d S hSopen
      A q R G hq hR hG hFlux hWeak hEq w hwSmooth hwCompact hwSupportS
      k h hh.ne' (hwShiftS k h habsh)
  have hrow (i : Fin d) := spatialDifferenceQuotient_principalFluxRow A G i k h
  have hfluxInt' (i : Fin d) : Integrable (fun z ↦
      (∑ j : Fin d,
        (spatialTranslate k h (fun x ↦ A x i j) z * H j z +
          spatialDifferenceQuotient k h (fun x ↦ A x i j) z * G j z)) *
        (velocityGradient w z i * Q z + w z * H i z))
      (timeVelocityVolumeOn S) := by
    simpa only [Q, H, hrow i, IntegrableOn, timeVelocityVolumeOn] using hfluxInt i
  have hOff : ∀ z ∈ S, z ∉ V →
      w z = 0 ∧ ∀ i, velocityGradient w z i = 0 := by
    intro z hzS hzV
    constructor
    · by_contra hn
      exact hzV (hwSupportV (subset_tsupport w hn))
    · intro i
      by_contra hn
      exact hzV ((fixedCore_velocityGradient_tsupport_subset.trans hwSupportV)
        (subset_tsupport _ hn))
  have hEllShift : ∀ z ∈ V,
      lam • (1 : PDE.Mat d) ≤ A (spatialShift k h z) ∧
        A (spatialShift k h z) ≤ Lam • (1 : PDE.Mat d) := by
    intro z hz
    exact hEll _ (hshiftV hz)
  have hAquot : ∀ z ∈ V, ∀ i j,
      |spatialDifferenceQuotient k h (fun x ↦ A x i j) z| ≤ Ma := by
    intro z hz i j
    exact coefficient_spatialDifferenceQuotient_bound hO₀ hcarrier habsh A hA
      hAbound i j k z hz
  have hdpos : 0 < d := Nat.pos_of_ne_zero (by
    intro hd0
    subst d
    exact Fin.elim0 k)
  have hcoercive :=
    setIntegral_fixedDirection_fluxPairing_coercive_absorbed_on_safeCarrier
      hSmeas hVmeas hVS A G H w Q k h lam Lam Ma Keta hdpos hlam hMa hKeta
      hwSmooth.continuous.aestronglyMeasurable (fun z hz ↦ (hwBounds z).1)
      (fun z hz ↦ (hwBounds z).2) hOff hEllShift hAquot
      (fun z hz i ↦ hwGradSq i z) hQ (fun j ↦ (hG j).mono hVS) hH
      hDpsiSupport hfluxInt'
  have hsource := abs_setIntegral_source_mul_backwardQuotient_le_absorbed_weighted
    hSmeas hVmeas k h hh.ne' R (fun z ↦ w z * Q z) Q (H k) w lam Keta
    hlam hKeta hR hpsi hQ (hH k)
    hwSmooth.continuous.aestronglyMeasurable
    (fixedCore_velocityGradient_contDiff_infty hwSmooth).continuous.aestronglyMeasurable
    (fun z hz ↦ (hwBounds z).1) (fun z hz ↦ (hwBounds z).2)
    (fun z hz ↦ hwGradBound k z) (hDpsiSupport k) (hpsiWeak k)
    (integral_nonneg_of_ae (ae_of_all _ fun z ↦
      mul_nonneg (hwBounds z).1 (sq_nonneg (H k z))))
  have htimeIntV : Integrable (fun z ↦ timeDerivative w z * Q z ^ 2)
      (timeVelocityVolumeOn V) := by
    simpa only [Q, IntegrableOn, timeVelocityVolumeOn] using htimeInt.mono_set hVS
  have htime := abs_setIntegral_timeDerivative_mul_sq_le hVmeas Q w Kzeta hQ
    htimeIntV
    (fun z hz ↦ hwTimeBound z) hKzeta
  have htimeSV : (∫ z in S, timeDerivative w z * Q z ^ 2) =
      ∫ z in V, timeDerivative w z * Q z ^ 2 := by
    rw [← integral_indicator hSmeas, ← integral_indicator hVmeas]
    apply integral_congr_ae
    exact ae_of_all _ fun z ↦ by
      by_cases hzV : z ∈ V
      · simp [hzV, hVS hzV]
      · by_cases hzS : z ∈ S
        · have hzero : timeDerivative w z = 0 := by
            by_contra hn
            exact hzV ((fixedCore_timeDerivative_tsupport_subset.trans hwSupportV)
              (subset_tsupport _ hn))
          simp [hzV, hzS, hzero]
        · simp [hzV, hzS]
  have henergy' :
      (∑ i, ∫ z in S,
        (∑ j : Fin d,
          (spatialTranslate k h (fun x ↦ A x i j) z * H j z +
            spatialDifferenceQuotient k h (fun x ↦ A x i j) z * G j z)) *
          (velocityGradient w z i * Q z + w z * H i z)) =
        -(1 / 2) * (∫ z in S, timeDerivative w z * Q z ^ 2) +
          (∫ z in S, R z * spatialDifferenceQuotient k (-h)
            (fun x ↦ w x * Q x) z) := by
    have he := henergy
    simp only [Q, H, hrow] at he ⊢
    linarith
  have hEV : (∫ z in S, w z * ∑ i, H i z ^ 2) =
      ∫ z in V, w z * ∑ i, H i z ^ 2 := by
    rw [← integral_indicator hSmeas, ← integral_indicator hVmeas]
    apply integral_congr_ae
    exact ae_of_all _ fun z ↦ by
      by_cases hzV : z ∈ V
      · simp [hzV, hVS hzV]
      · by_cases hzS : z ∈ S
        · simp [hzV, hzS, (hOff z hzS hzV).1]
        · simp [hzV, hzS]
  rw [hEV] at hcoercive
  have hqSq : (∫ z in V, Q z ^ 2) = ‖hQ.toLp Q‖ ^ 2 :=
    fixedCore_integral_sq_eq_norm_sq_toLp Q hQ
  have hgSq : (∑ j, ∫ z in V, G j z ^ 2) =
      ∑ j, ‖((hG j).mono hVS).toLp (G j)‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro j _
    exact fixedCore_integral_sq_eq_norm_sq_toLp (G j) ((hG j).mono hVS)
  have hrSq : (∫ z in S, R z ^ 2) = ‖hR.toLp R‖ ^ 2 :=
    fixedCore_integral_sq_eq_norm_sq_toLp R hR
  have htime' : |∫ z in S, timeDerivative w z * Q z ^ 2| ≤
      Kzeta * (∫ z in V, Q z ^ 2) := by
    rw [htimeSV, hqSq]
    exact htime
  have hsource' : |∫ z in S, R z * spatialDifferenceQuotient k (-h)
      (fun x ↦ w x * Q x) z| ≤
      (lam / 8) * (∫ z in V, w z * H k z ^ 2) +
        (1 / 8) * (∫ z in V, Q z ^ 2) +
        (2 / lam + 8 * Keta ^ 2) * (∫ z in S, R z ^ 2) := by
    rw [hqSq, hrSq]
    exact hsource
  have hwMeasV : AEStronglyMeasurable w (timeVelocityVolumeOn V) :=
    hwSmooth.continuous.aestronglyMeasurable
  have hEkInt : Integrable (fun z ↦ w z * H k z ^ 2)
      (timeVelocityVolumeOn V) := by
    refine Integrable.mono' (hH k).integrable_sq
      (hwMeasV.mul (hH k).integrable_sq.1) ?_
    filter_upwards [ae_restrict_mem hVmeas] with z hz
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hwBounds z).1,
      abs_of_nonneg (sq_nonneg (H k z))]
    exact mul_le_of_le_one_left (sq_nonneg _) (hwBounds z).2
  have hEInt : Integrable (fun z ↦ w z * ∑ i, H i z ^ 2)
      (timeVelocityVolumeOn V) := by
    have hsumInt : Integrable (fun z ↦ ∑ i, H i z ^ 2)
        (timeVelocityVolumeOn V) :=
      integrable_finset_sum _ fun i _ ↦ (hH i).integrable_sq
    refine Integrable.mono' hsumInt (hwMeasV.mul hsumInt.1) ?_
    filter_upwards [ae_restrict_mem hVmeas] with z hz
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hwBounds z).1,
      abs_of_nonneg (Finset.sum_nonneg fun i _ ↦ sq_nonneg (H i z))]
    exact mul_le_of_le_one_left
      (Finset.sum_nonneg fun i _ ↦ sq_nonneg (H i z)) (hwBounds z).2
  have hcomb := caccioppoli_combination_of_energy_bounds lam Gamma Kzeta Keta
    (∫ z in V, w z * ∑ i, H i z ^ 2)
    (∫ z in V, w z * H k z ^ 2)
    (∑ i, ∫ z in S,
      (∑ j : Fin d,
        (spatialTranslate k h (fun x ↦ A x i j) z * H j z +
          spatialDifferenceQuotient k h (fun x ↦ A x i j) z * G j z)) *
        (velocityGradient w z i * Q z + w z * H i z))
    (∫ z in S, timeDerivative w z * Q z ^ 2)
    (∫ z in S, R z * spatialDifferenceQuotient k (-h)
      (fun x ↦ w x * Q x) z)
    (∫ z in V, Q z ^ 2) (∑ j, ∫ z in V, G j z ^ 2) (∫ z in S, R z ^ 2)
    (‖hQ.toLp Q‖ ^ 2) (∑ j, ‖((hG j).mono hVS).toLp (G j)‖ ^ 2)
    (‖hR.toLp R‖ ^ 2) hlam
    (integral_nonneg_of_ae (ae_of_all _ fun z ↦ mul_nonneg (hwBounds z).1
      (Finset.sum_nonneg fun i _ ↦ sq_nonneg (H i z))))
    (integral_mono_ae hEkInt hEInt (by
      filter_upwards [ae_restrict_mem hVmeas] with z hz
      exact mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (fun i _ ↦ sq_nonneg (H i z)) (Finset.mem_univ k))
        (hwBounds z).1)) henergy' hcoercive htime' hsource' hqSq hgSq hrSq
  obtain ⟨hinnerH, hplateau⟩ := memLpOn_inner_and_sum_norm_sq_le_weighted
    hVmeas hinnerMeas hinnerV H w hH
    hwSmooth.continuous.aestronglyMeasurable (fun z hz ↦ (hwBounds z).1)
    (fun z hz ↦ (hwBounds z).2) hwOne
  refine ⟨hinnerH, ?_⟩
  have hGmonoSq (j : Fin d) :
      ‖((hG j).mono hVS).toLp (G j)‖ ^ 2 ≤ ‖(hG j).toLp (G j)‖ ^ 2 := by
    rw [← fixedCore_integral_sq_eq_norm_sq_toLp (G j) ((hG j).mono hVS),
      ← fixedCore_integral_sq_eq_norm_sq_toLp (G j) (hG j)]
    exact integral_mono_measure (Measure.restrict_mono_set volume hVS)
      (ae_of_all _ fun z ↦ sq_nonneg (G j z)) (hG j).integrable_sq
  have hGsumMono :
      ∑ j, ‖((hG j).mono hVS).toLp (G j)‖ ^ 2 ≤
        ∑ j, ‖(hG j).toLp (G j)‖ ^ 2 :=
    Finset.sum_le_sum fun j _ ↦ hGmonoSq j
  have hGkSum : ‖(hG k).toLp (G k)‖ ^ 2 ≤
      ∑ j, ‖(hG j).toLp (G j)‖ ^ 2 :=
    Finset.single_le_sum (fun j _ ↦ sq_nonneg ‖(hG j).toLp (G j)‖)
      (Finset.mem_univ k)
  have hscaled : ∑ j, ‖(hinnerH j).toLp (H j)‖ ^ 2 ≤
      (4 / lam) * ((2 * Gamma + Kzeta / 2 + 1 / 8) *
        (∑ j, ‖(hG j).toLp (G j)‖ ^ 2) + beta * ‖hR.toLp R‖ ^ 2) := by
    calc
      _ ≤ ∫ z in V, w z * ∑ i, H i z ^ 2 := hplateau
      _ ≤ (4 / lam) * ((Gamma + Kzeta / 2 + 1 / 8) * ‖hQ.toLp Q‖ ^ 2 +
          Gamma * (∑ j, ‖((hG j).mono hVS).toLp (G j)‖ ^ 2) +
          beta * ‖hR.toLp R‖ ^ 2) := by
        calc
          _ = (4 / lam) * ((lam / 4) *
              ∫ z in V, w z * ∑ i, H i z ^ 2) := by
                field_simp [ne_of_gt hlam]
          _ ≤ _ := mul_le_mul_of_nonneg_left (by simpa only [beta] using hcomb)
            (by positivity)
      _ ≤ _ := by
        have hQsq := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hQnorm
        have hA : 0 ≤ Gamma + Kzeta / 2 + 1 / 8 := by positivity
        have hscale : 0 ≤ 4 / lam := by positivity
        apply mul_le_mul_of_nonneg_left _ hscale
        calc
          (Gamma + Kzeta / 2 + 1 / 8) * ‖hQ.toLp Q‖ ^ 2 +
                Gamma * (∑ j, ‖((hG j).mono hVS).toLp (G j)‖ ^ 2) +
                beta * ‖hR.toLp R‖ ^ 2
              ≤ (Gamma + Kzeta / 2 + 1 / 8) * ‖(hG k).toLp (G k)‖ ^ 2 +
                Gamma * (∑ j, ‖(hG j).toLp (G j)‖ ^ 2) +
                beta * ‖hR.toLp R‖ ^ 2 := by
            exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hQsq hA)
              (mul_le_mul_of_nonneg_left hGsumMono hGamma)) le_rfl
          _ ≤ (Gamma + Kzeta / 2 + 1 / 8) *
                (∑ j, ‖(hG j).toLp (G j)‖ ^ 2) +
                Gamma * (∑ j, ‖(hG j).toLp (G j)‖ ^ 2) +
                beta * ‖hR.toLp R‖ ^ 2 := by
            exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hGkSum hA)
              le_rfl) le_rfl
          _ = (2 * Gamma + Kzeta / 2 + 1 / 8) *
                (∑ j, ‖(hG j).toLp (G j)‖ ^ 2) +
                beta * ‖hR.toLp R‖ ^ 2 := by ring
  have hfinal := caccioppoli_final_constant_bound (4 / lam)
    (2 * Gamma + Kzeta / 2 + 1 / 8) beta
    ((ENNReal.toReal (eLpNorm q 2 (timeVelocityVolumeOn S))) ^ 2)
    (∑ j, (ENNReal.toReal (eLpNorm (G j) 2 (timeVelocityVolumeOn S))) ^ 2)
    ((ENNReal.toReal (eLpNorm R 2 (timeVelocityVolumeOn S))) ^ 2)
    (by positivity) (by positivity) hbeta (sq_nonneg _)
    (Finset.sum_nonneg fun j _ ↦ sq_nonneg _) (sq_nonneg _)
  have hscaled' : ∑ j, (ENNReal.toReal (eLpNorm
      (spatialDifferenceQuotient k h (G j)) 2
      (timeVelocityVolumeOn inner))) ^ 2 ≤
      (4 / lam) * ((2 * Gamma + Kzeta / 2 + 1 / 8) *
        (∑ j, (ENNReal.toReal (eLpNorm (G j) 2
          (timeVelocityVolumeOn S))) ^ 2) + beta *
        (ENNReal.toReal (eLpNorm R 2 (timeVelocityVolumeOn S))) ^ 2) := by
    simpa only [H, Lp.norm_toLp] using hscaled
  simpa only [C, S, inner] using hscaled'.trans hfinal


end HypoellipticAleksandrov.Parabolic
