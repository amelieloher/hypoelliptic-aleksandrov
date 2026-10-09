module

public import HypoellipticAleksandrov.Parabolic.ParabolicMemLpSpatialDifferenceQuotient
public import HypoellipticAleksandrov.Parabolic.SpatialDifferenceQuotientWeakDerivatives
public import HypoellipticAleksandrov.Parabolic.SpatialDifferenceQuotientTest
public import HypoellipticAleksandrov.Parabolic.SpatialDifferenceQuotientL2Transpose
public import HypoellipticAleksandrov.Parabolic.SpatialTranslationWeakDerivatives
public import HypoellipticAleksandrov.Parabolic.SpacetimeMollifierL2
public import HypoellipticAleksandrov.Parabolic.SpacetimeMollifierWeightedTimeEnergy
public import HypoellipticAleksandrov.Parabolic.TimeVelocitySmoothCompactPlateau
public import HypoellipticAleksandrov.Parabolic.WeakDerivativesCompactGlobalization
public import HypoellipticAleksandrov.Parabolic.WeakDerivativeSpacetimeMollification
public import HypoellipticAleksandrov.Parabolic.WeakJetProduct

/-!
# Quotient-test energy identity

This module begins the direct spacetime-mollification proof of the localized
spatial difference-quotient energy identity.  The private infrastructure below
constructs a precompact shift-safe collar and globalizes the localized value
and its selected weak spatial derivatives.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory Set
open scoped Convolution ENNReal Pointwise Topology
open HypoellipticAleksandrov.Parabolic.SpacetimeMollifier
open SpacetimeMollifierWeightedTimeEnergy

private theorem velocityGradient_contDiff_infty
    {d : ℕ} {f : TimeVelocity d → ℝ} {i : Fin d}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z ↦ velocityGradient f z i) := by
  unfold velocityGradient
  exact (contDiff_infty_iff_fderiv.mp hf).2.clm_apply contDiff_const

private theorem velocityGradient_compact
    {d : ℕ} {f : TimeVelocity d → ℝ} {i : Fin d}
    (hf : HasCompactSupport f) :
    HasCompactSupport (fun z ↦ velocityGradient f z i) := by
  unfold velocityGradient
  simpa using hf.fderiv_apply (𝕜 := ℝ) ((0, Pi.single i 1) : TimeVelocity d)

private theorem velocityGradient_tsupport_subset
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

private theorem timeDerivative_tsupport_subset
    {d : ℕ} {f : TimeVelocity d → ℝ} :
    tsupport (timeDerivative f) ⊆ tsupport f := by
  unfold timeDerivative
  change closure (Function.support (fun z ↦
    fderiv ℝ f z (1, 0))) ⊆ tsupport f
  refine (closure_mono ?_).trans (tsupport_fderiv_subset ℝ)
  intro z hz
  rw [Function.mem_support] at hz ⊢
  intro hzero
  apply hz
  simp [hzero]

/-- Time differentiation commutes exactly with a spatial difference quotient. -/
private theorem timeDerivative_spatialDifferenceQuotient
    {d : ℕ} (k : Fin d) (h : ℝ) (f : TimeVelocity d → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    timeDerivative (spatialDifferenceQuotient k h f) =
      spatialDifferenceQuotient k h (timeDerivative f) := by
  funext z
  have htrans : DifferentiableAt ℝ (spatialTranslate k h f) z :=
    (ContDiff.spatialTranslate hf).differentiable (by simp) z
  have hfd : DifferentiableAt ℝ f z := hf.differentiable (by simp) z
  have ht := timeDerivative_spatialTranslate k h f z
  unfold timeDerivative at ht
  unfold timeDerivative spatialDifferenceQuotient
  rw [show (fun z ↦ (spatialTranslate k h f z - f z) / h) =
      fun z ↦ h⁻¹ * (spatialTranslate k h f z - f z) by
        funext y
        ring]
  rw [fderiv_const_mul (a := fun y ↦ spatialTranslate k h f y - f y)
    (htrans.sub hfd)]
  rw [show fderiv ℝ (fun y ↦ spatialTranslate k h f y - f y) z =
      fderiv ℝ (spatialTranslate k h f) z - fderiv ℝ f z from
    (htrans.hasFDerivAt.sub hfd.hasFDerivAt).fderiv]
  simp [ht, div_eq_mul_inv, mul_comm]

/-- A selected velocity derivative commutes exactly with a spatial difference
quotient of a smooth function. -/
private theorem velocityGradient_spatialDifferenceQuotient
    {d : ℕ} (k : Fin d) (h : ℝ) (f : TimeVelocity d → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin d) (z : TimeVelocity d) :
    velocityGradient (spatialDifferenceQuotient k h f) z i =
      spatialDifferenceQuotient k h (fun y ↦ velocityGradient f y i) z := by
  have htrans : DifferentiableAt ℝ (spatialTranslate k h f) z :=
    (ContDiff.spatialTranslate hf).differentiable (by simp) z
  have hfd : DifferentiableAt ℝ f z := hf.differentiable (by simp) z
  have hv := congrFun (velocityGradient_spatialTranslate k h f z) i
  unfold velocityGradient at hv
  unfold velocityGradient spatialDifferenceQuotient
  rw [show (fun y ↦ (spatialTranslate k h f y - f y) / h) =
      fun y ↦ h⁻¹ * (spatialTranslate k h f y - f y) by
        funext y
        ring]
  rw [fderiv_const_mul (a := fun y ↦ spatialTranslate k h f y - f y)
    (htrans.sub hfd)]
  rw [show fderiv ℝ (fun y ↦ spatialTranslate k h f y - f y) z =
      fderiv ℝ (spatialTranslate k h f) z - fderiv ℝ f z from
    (htrans.hasFDerivAt.sub hfd.hasFDerivAt).fderiv]
  simp [hv, div_eq_mul_inv, mul_comm]

/-- A selected velocity derivative of a backward quotient transposes from a
smooth compact test to the forward quotient of an `L²` factor. -/
private theorem setIntegral_mul_velocityGradient_spatialDifferenceQuotient_neg
    {d : ℕ} {S C V : Set (TimeVelocity d)}
    (hSmeas : MeasurableSet S) (hCcompact : IsCompact C)
    (hCS : C ⊆ S) (hVC : V ⊆ C)
    (H : TimeVelocity d → ℝ) (hH : ParabolicMemLpOn C 2 H)
    (k : Fin d) (h : ℝ) (f : TimeVelocity d → ℝ)
    (hfSmooth : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfCompact : HasCompactSupport f) (hfSupport : tsupport f ⊆ V)
    (hfShift : Set.MapsTo (spatialShift k h) V C) (i : Fin d) :
    (∫ z in S, H z * velocityGradient
        (spatialDifferenceQuotient k (-h) f) z i) =
      -∫ z in V, spatialDifferenceQuotient k h H z * velocityGradient f z i := by
  let g : TimeVelocity d → ℝ := fun z ↦ velocityGradient f z i
  have hgSmooth : ContDiff ℝ (⊤ : ℕ∞) g :=
    velocityGradient_contDiff_infty hfSmooth
  have hgCompact : HasCompactSupport g :=
    velocityGradient_compact hfCompact
  have hgSupport : tsupport g ⊆ V :=
    velocityGradient_tsupport_subset.trans hfSupport
  have hquotSupport : tsupport (spatialDifferenceQuotient k (-h) g) ⊆ C :=
    tsupport_spatialDifferenceQuotient_subset_of_mapsTo_spatialShift_neg
      k (-h) g hgSupport hVC (by simpa using hfShift)
  have hrestrictLeft :
      (∫ z in S, H z * spatialDifferenceQuotient k (-h) g z) =
        ∫ z in C, H z * spatialDifferenceQuotient k (-h) g z := by
    exact setIntegral_eq_of_subset_of_forall_diff_eq_zero hSmeas hCS
      (fun z hz ↦ by
        have hzero : spatialDifferenceQuotient k (-h) g z = 0 :=
          image_eq_zero_of_notMem_tsupport (fun hzt ↦ hz.2 (hquotSupport hzt))
        rw [hzero]
        simp)
  have htranspose :=
    setIntegral_spatialDifferenceQuotient_mul_eq_neg_mul_spatialDifferenceQuotient_neg
      C k h H g hH hgSmooth.continuous hgCompact
      (hgSupport.trans hVC) (fun z hz ↦ hfShift (hgSupport hz))
  have hrestrictRight :
      (∫ z in C, spatialDifferenceQuotient k h H z * g z) =
        ∫ z in V, spatialDifferenceQuotient k h H z * g z := by
    exact setIntegral_eq_of_subset_of_forall_diff_eq_zero hCcompact.measurableSet hVC
      (fun z hz ↦ by
        have hzero : g z = 0 :=
          image_eq_zero_of_notMem_tsupport (fun hzt ↦ hz.2 (hgSupport hzt))
        rw [hzero]
        simp)
  simp_rw [velocityGradient_spatialDifferenceQuotient k (-h) f hfSmooth i]
  rw [hrestrictLeft]
  calc
    (∫ z in C, H z * spatialDifferenceQuotient k (-h) g z) =
        -(∫ z in C, spatialDifferenceQuotient k h H z * g z) := by
      linarith
    _ = -∫ z in V, spatialDifferenceQuotient k h H z * velocityGradient f z i := by
      rw [hrestrictRight]

/-- Transposition of the time derivative of a backward quotient from a smooth
compact test to the forward quotient of the rough factor, with the latter
pairing restricted to its shift-safe carrier. -/
private theorem setIntegral_mul_timeDerivative_spatialDifferenceQuotient_neg
    {d : ℕ} {S V : Set (TimeVelocity d)}
    (hSmeas : MeasurableSet S) (hVS : V ⊆ S)
    (q : TimeVelocity d → ℝ) (hq : ParabolicMemLpOn S 2 q)
    (k : Fin d) (h : ℝ) (f : TimeVelocity d → ℝ)
    (hfSmooth : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfCompact : HasCompactSupport f) (hfSupport : tsupport f ⊆ V)
    (hfShift : Set.MapsTo (spatialShift k h) V S) :
    (∫ z in S, q z * timeDerivative
        (spatialDifferenceQuotient k (-h) f) z) =
      -∫ z in V, spatialDifferenceQuotient k h q z * timeDerivative f z := by
  have hdtSmooth : ContDiff ℝ (⊤ : ℕ∞) (timeDerivative f) := by
    unfold timeDerivative
    exact (contDiff_infty_iff_fderiv.mp hfSmooth).2.clm_apply contDiff_const
  have hdtCompact : HasCompactSupport (timeDerivative f) := by
    unfold timeDerivative
    simpa using hfCompact.fderiv_apply (𝕜 := ℝ) ((1, 0) : TimeVelocity d)
  have hdtSupport : tsupport (timeDerivative f) ⊆ V :=
    timeDerivative_tsupport_subset.trans hfSupport
  have htranspose :=
    setIntegral_spatialDifferenceQuotient_mul_eq_neg_mul_spatialDifferenceQuotient_neg
      S k h q (timeDerivative f) hq hdtSmooth.continuous hdtCompact
      (hdtSupport.trans hVS) (fun z hz ↦ hfShift (hdtSupport hz))
  have hrestrict :
      (∫ z in S, spatialDifferenceQuotient k h q z * timeDerivative f z) =
        ∫ z in V, spatialDifferenceQuotient k h q z * timeDerivative f z := by
    exact setIntegral_eq_of_subset_of_forall_diff_eq_zero hSmeas hVS
      (fun z hz ↦ by
        have hzero : timeDerivative f z = 0 :=
          image_eq_zero_of_notMem_tsupport (fun hzt ↦ hz.2 (hdtSupport hzt))
        simp [hzero])
  rw [timeDerivative_spatialDifferenceQuotient k (-h) f hfSmooth]
  calc
    (∫ z in S, q z * spatialDifferenceQuotient k (-h) (timeDerivative f) z) =
        -(∫ z in S, spatialDifferenceQuotient k h q z * timeDerivative f z) := by
      linarith
    _ = -∫ z in V, spatialDifferenceQuotient k h q z * timeDerivative f z := by
      rw [hrestrict]

private theorem tsupport_spacetimeMollification_subset_cthickening
    {d : ℕ} {f : TimeVelocity d → ℝ}
    {ε : ℝ} (hε : 0 < ε) :
    tsupport (spacetimeMollification ε f) ⊆ Metric.cthickening ε (tsupport f) := by
  have hsupp : Function.support (spacetimeMollification ε f) ⊆
      Metric.thickening ε (tsupport f) := by
    intro z hz
    have hzsum := support_convolution_subset
      (ContinuousLinearMap.lsmul ℝ ℝ) hz
    rcases hzsum with ⟨x, hx, y, hy, rfl⟩
    apply Metric.mem_thickening_iff.mpr
    refine ⟨y, subset_tsupport f hy, ?_⟩
    rw [dist_eq_norm]
    simpa [spacetimeMollifier_support hε] using hx
  exact (closure_mono hsupp).trans
    (Metric.closure_thickening_subset_cthickening ε (tsupport f))

/-- A local `L²` representative can be globalized without changing the
weighted time-energy pairing near the support of the smooth weight. -/
private theorem tendsto_localized_timeEnergy_spacetimeMollification
    {d : ℕ} {V : Set (TimeVelocity d)}
    (hVopen : IsOpen V)
    (qh w : TimeVelocity d → ℝ) (hqh : ParabolicMemLpOn V 2 qh)
    (hwSmooth : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwCompact : HasCompactSupport w) (hwSupport : tsupport w ⊆ V) :
    Filter.Tendsto (fun ε : ℝ ↦ ∫ z in V, qh z *
        timeDerivative (spacetimeMollification ε (fun y ↦ w y * qh y)) z)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((1 / 2 : ℝ) * ∫ z in V,
        timeDerivative w z * qh z ^ 2)) := by
  obtain ⟨δ, hδ, χ, hχSmooth, hχCompact, hχSupport, hχOne⟩ :=
    exists_contDiff_one_on_cthickening_tsupport_subset
      hVopen hwCompact.isCompact hwSupport
  let Q : TimeVelocity d → ℝ := fun z ↦ χ z * qh z
  have hχTop : ParabolicMemLpOn V ∞ χ :=
    (hχSmooth.continuous.memLp_of_hasCompactSupport hχCompact).restrict V
  have hQV : ParabolicMemLpOn V 2 Q := by
    simpa only [Q, mul_comm] using hqh.fun_mul hχTop
  have hQSupport : Function.support Q ⊆ V := by
    intro z hz
    have hzχ : χ z ≠ 0 := by
      intro hzero
      apply hz
      simp [Q, hzero]
    exact hχSupport (subset_tsupport χ hzχ)
  have hQ : MemLp Q 2 volume :=
    hQV.memLp_of_support_subset hVopen.measurableSet hQSupport
  have hχOneK : Set.EqOn χ 1 (tsupport w) := fun z hz ↦
    hχOne (Metric.self_subset_cthickening (tsupport w) hz)
  have hwQ : (fun z ↦ w z * Q z) = fun z ↦ w z * qh z := by
    funext z
    by_cases hz : z ∈ tsupport w
    · simp [Q, hχOneK hz]
    · have hwz : w z = 0 := image_eq_zero_of_notMem_tsupport hz
      simp [hwz]
  have hwtQsq : (fun z ↦ timeDerivative w z * Q z ^ 2) =
      fun z ↦ timeDerivative w z * qh z ^ 2 := by
    funext z
    by_cases hz : z ∈ tsupport w
    · simp [Q, hχOneK hz]
    · have hwtz : timeDerivative w z = 0 :=
        image_eq_zero_of_notMem_tsupport
          (fun hzt ↦ hz (timeDerivative_tsupport_subset hzt))
      simp [hwtz]
  have hglobal :=
    tendsto_integral_mul_timeDerivative_spacetimeMollification_mul
      Q w hQ hwSmooth hwCompact
  have heq : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),
      (∫ z : TimeVelocity d, Q z *
          timeDerivative (spacetimeMollification ε (fun y ↦ w y * Q y)) z) =
        ∫ z in V, qh z *
          timeDerivative (spacetimeMollification ε (fun y ↦ w y * qh y)) z := by
    filter_upwards [(eventually_lt_nhds (show (0 : ℝ) < δ from hδ)).filter_mono
        inf_le_left,
      self_mem_nhdsWithin] with ε hεδ hεpos
    rw [hwQ]
    let D : TimeVelocity d → ℝ := fun z ↦ timeDerivative
      (spacetimeMollification ε (fun y ↦ w y * qh y)) z
    have hχ_at_D (z : TimeVelocity d) (hzD : D z ≠ 0) : χ z = 1 := by
      have hzmoll := timeDerivative_tsupport_subset (subset_tsupport D hzD)
      have hzthick := tsupport_spacetimeMollification_subset_cthickening hεpos hzmoll
      have hthickSub : Metric.cthickening ε
          (tsupport (fun y ↦ w y * qh y)) ⊆
          Metric.cthickening ε (tsupport w) := by
        exact Metric.cthickening_subset_of_subset ε tsupport_mul_subset_left
      exact hχOne (Metric.cthickening_mono hεδ.le (tsupport w)
        (hthickSub hzthick))
    calc
      (∫ z : TimeVelocity d, Q z * D z) = ∫ z in V, Q z * D z := by
        have ht := setIntegral_eq_of_subset_of_forall_diff_eq_zero
          (μ := (volume : Measure (TimeVelocity d))) MeasurableSet.univ
          (subset_univ V) (f := fun z ↦ Q z * D z) (fun z hz ↦ by
            by_cases hzD : D z = 0
            · simp [hzD]
            · have hzχ := hχ_at_D z hzD
              have hzV : z ∈ V := hχSupport (subset_tsupport χ (by simp [hzχ]))
              exact (hz.2 hzV).elim)
        simpa only [Measure.restrict_univ] using ht
      _ = ∫ z in V, qh z * D z := by
        apply integral_congr_ae
        filter_upwards [] with z
        by_cases hzD : D z = 0
        · simp [hzD]
        · simp [Q, hχ_at_D z hzD]
  have hlimitEq :
      ((1 / 2 : ℝ) * ∫ z : TimeVelocity d,
          timeDerivative w z * Q z ^ 2) =
        (1 / 2 : ℝ) * ∫ z in V, timeDerivative w z * qh z ^ 2 := by
    rw [hwtQsq]
    congr 1
    have ht := setIntegral_eq_of_subset_of_forall_diff_eq_zero
      (μ := (volume : Measure (TimeVelocity d))) MeasurableSet.univ
      (subset_univ V) (f := fun z ↦ timeDerivative w z * qh z ^ 2) (fun z hz ↦ by
        have hwtz : timeDerivative w z = 0 :=
          image_eq_zero_of_notMem_tsupport
            (fun hzt ↦ hz.2 (hwSupport (timeDerivative_tsupport_subset hzt)))
        rw [hwtz]
        simp)
    simpa only [Measure.restrict_univ] using ht
  rw [← hlimitEq]
  exact hglobal.congr' heq

/-- The localized quotient test and all its selected spatial derivatives have
global `L²` representatives and ambient weak-derivative relations. -/
private theorem exists_global_localizedQuotient_weakGradient
    {d : ℕ} {S : Set (TimeVelocity d)} (hS : IsOpen S)
    (q : TimeVelocity d → ℝ) (G : Fin d → TimeVelocity d → ℝ)
    (hq : ParabolicMemLpOn S 2 q)
    (hG : ∀ j, ParabolicMemLpOn S 2 (G j))
    (hWeak : ∀ j, HasWeakVelocityPartialDerivOn S j q (G j))
    (w : TimeVelocity d → ℝ)
    (hwSmooth : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwCompact : HasCompactSupport w) (hwSupport : tsupport w ⊆ S)
    (k : Fin d) (h : ℝ)
    (hwShift : Set.MapsTo (spatialShift k h) (tsupport w) S) :
    ∃ V C : Set (TimeVelocity d), IsOpen V ∧ IsCompact (closure V) ∧
      tsupport w ⊆ V ∧ V ⊆ S ∧
      IsCompact C ∧ V ⊆ C ∧ C ⊆ S ∧
      Set.MapsTo (spatialShift k h) V C ∧
      ParabolicMemLpOn V 2 (spatialDifferenceQuotient k h q) ∧
      (∀ i, ParabolicMemLpOn V 2 (spatialDifferenceQuotient k h (G i))) ∧
      (∀ i, HasWeakVelocityPartialDerivOn V i
        (spatialDifferenceQuotient k h q)
        (spatialDifferenceQuotient k h (G i))) ∧
      MemLp (fun z ↦ w z * spatialDifferenceQuotient k h q z) 2 volume ∧
      (∀ i, MemLp (fun z ↦
        velocityGradient w z i * spatialDifferenceQuotient k h q z +
          w z * spatialDifferenceQuotient k h (G i) z) 2 volume) ∧
      (∀ i, HasWeakVelocityPartialDerivOn Set.univ i
        (fun z ↦ w z * spatialDifferenceQuotient k h q z)
        (fun z ↦ velocityGradient w z i * spatialDifferenceQuotient k h q z +
          w z * spatialDifferenceQuotient k h (G i) z)) ∧
      ∀ i, tsupport (fun z ↦
        velocityGradient w z i * spatialDifferenceQuotient k h q z +
          w z * spatialDifferenceQuotient k h (G i) z) ⊆ V := by
  let K : Set (TimeVelocity d) := tsupport w
  let U : Set (TimeVelocity d) :=
    S ∩ spatialShift k h ⁻¹' S
  have hshiftContinuous : Continuous (spatialShift k h) := by
    convert (Homeomorph.addRight
      ((0, h • PDE.basisVec k) : TimeVelocity d)).continuous using 1
    funext z
    apply Prod.ext
    · simp [spatialShift]
    · rfl
  have hU : IsOpen U := hS.inter (hS.preimage hshiftContinuous)
  have hKU : K ⊆ U := by
    intro z hz
    exact ⟨hwSupport hz, hwShift hz⟩
  obtain ⟨δ, hδ, hcollar⟩ := hwCompact.isCompact.exists_cthickening_subset_open hU hKU
  let V : Set (TimeVelocity d) := Metric.thickening δ K
  have hVopen : IsOpen V := Metric.isOpen_thickening
  have hVclosure : IsCompact (closure V) := by
    apply IsCompact.of_isClosed_subset hwCompact.isCompact.cthickening isClosed_closure
    exact Metric.closure_thickening_subset_cthickening δ K
  have hKV : K ⊆ V := Metric.self_subset_thickening hδ K
  have hVU : V ⊆ U :=
    (Metric.thickening_subset_cthickening δ K).trans hcollar
  have hclosureVU : closure V ⊆ U :=
    (Metric.closure_thickening_subset_cthickening δ K).trans hcollar
  have hVS : V ⊆ S := fun z hz ↦ (hVU hz).1
  have hVshift : Set.MapsTo (spatialShift k h) V S := fun z hz ↦ (hVU hz).2
  let C : Set (TimeVelocity d) :=
    closure V ∪ spatialShift k h '' closure V
  have hCcompact : IsCompact C := by
    exact hVclosure.union (hVclosure.image hshiftContinuous)
  have hVC : V ⊆ C := by
    intro z hz
    exact Or.inl (subset_closure hz)
  have hCS : C ⊆ S := by
    rintro z (hz | ⟨y, hy, rfl⟩)
    · exact (hclosureVU hz).1
    · exact (hclosureVU hy).2
  have hVshiftC : Set.MapsTo (spatialShift k h) V C := by
    intro z hz
    exact Or.inr ⟨z, subset_closure hz, rfl⟩
  let qh : TimeVelocity d → ℝ := spatialDifferenceQuotient k h q
  let Gh : Fin d → TimeVelocity d → ℝ := fun i ↦
    spatialDifferenceQuotient k h (G i)
  let ψ : TimeVelocity d → ℝ := fun z ↦ w z * qh z
  let Dψ : Fin d → TimeVelocity d → ℝ := fun i z ↦
    velocityGradient w z i * qh z + w z * Gh i z
  have hqh : ParabolicMemLpOn V 2 qh :=
    hq.spatialDifferenceQuotient_of_subset_mapsTo k h hVS hVshift
  have hGh (i : Fin d) : ParabolicMemLpOn V 2 (Gh i) :=
    (hG i).spatialDifferenceQuotient_of_subset_mapsTo k h hVS hVshift
  have hqhWeak (i : Fin d) : HasWeakVelocityPartialDerivOn V i qh (Gh i) := by
    exact (hWeak i).spatialDifferenceQuotient_of_subset_mapsTo
      (hq.locallyIntegrableOn (by norm_num))
      ((hG i).locallyIntegrableOn (by norm_num)) k h hVS hVshift
  have hwTop : ParabolicMemLpOn V ∞ w :=
    (hwSmooth.continuous.memLp_of_hasCompactSupport hwCompact).restrict V
  have hdwTop (i : Fin d) : ParabolicMemLpOn V ∞
      (fun z ↦ velocityGradient w z i) :=
    ((velocityGradient_contDiff_infty (i := i) hwSmooth).continuous.memLp_of_hasCompactSupport
      (velocityGradient_compact (i := i) hwCompact)).restrict V
  have hψV : ParabolicMemLpOn V 2 ψ := by
    simpa only [ψ, mul_comm] using hqh.fun_mul hwTop
  have hDψV (i : Fin d) : ParabolicMemLpOn V 2 (Dψ i) := by
    have hfirst : ParabolicMemLpOn V 2 (fun z ↦ velocityGradient w z i * qh z) :=
      by simpa only [mul_comm] using hqh.fun_mul (hdwTop i)
    have hsecond : ParabolicMemLpOn V 2 (fun z ↦ w z * Gh i z) := by
      simpa only [mul_comm] using (hGh i).mul' hwTop
    exact hfirst.add hsecond
  have hψWeakV (i : Fin d) : HasWeakVelocityPartialDerivOn V i ψ (Dψ i) := by
    have hp := (hqhWeak i).mul_contDiff hwSmooth
      (hqh.locallyIntegrableOn (by norm_num))
      ((hGh i).locallyIntegrableOn (by norm_num))
    convert hp using 1
    · funext z
      simp only [Dψ]
      ring
  have hψSupport : tsupport ψ ⊆ V :=
    (tsupport_mul_subset_left (f := w) (g := qh)).trans hKV
  have hDψSupport (i : Fin d) : tsupport (Dψ i) ⊆ V := by
    refine (tsupport_add _ _).trans (union_subset ?_ ?_)
    · exact (tsupport_mul_subset_left (f := fun z ↦ velocityGradient w z i)
        (g := qh)).trans (velocityGradient_tsupport_subset.trans hKV)
    · exact (tsupport_mul_subset_left (f := w) (g := Gh i)).trans hKV
  have hψGlobal : MemLp ψ 2 volume :=
    hψV.memLp_of_support_subset hVopen.measurableSet
      ((subset_tsupport ψ).trans hψSupport)
  have hDψGlobal (i : Fin d) : MemLp (Dψ i) 2 volume :=
    (hDψV i).memLp_of_support_subset hVopen.measurableSet
      ((subset_tsupport (Dψ i)).trans (hDψSupport i))
  have hψWeakGlobal (i : Fin d) : HasWeakVelocityPartialDerivOn Set.univ i ψ (Dψ i) :=
    (hψWeakV i).univ_of_tsupport_subset hVopen hψSupport (hDψSupport i)
  exact ⟨V, C, hVopen, hVclosure, hKV, hVS, hCcompact, hVC, hCS, hVshiftC,
    hqh, hGh, hqhWeak,
    hψGlobal, hDψGlobal, hψWeakGlobal, hDψSupport⟩

/-- Positive-radius mollification of the localized quotient gives smooth
compact tests, their exact selected gradients, and a backward-quotient test
whose support remains in the original open carrier. -/
private theorem exists_mollifiedLocalizedQuotient_testPackage
    {d : ℕ} {S V : Set (TimeVelocity d)}
    (hVopen : IsOpen V) (hVcompact : IsCompact (closure V))
    (hVS : V ⊆ S) (k : Fin d) (h : ℝ)
    (hVshift : Set.MapsTo (spatialShift k h) V S)
    (ψ : TimeVelocity d → ℝ) (Dψ : Fin d → TimeVelocity d → ℝ)
    (hψ : MemLp ψ 2 volume) (hDψ : ∀ i, MemLp (Dψ i) 2 volume)
    (hψWeak : ∀ i, HasWeakVelocityPartialDerivOn Set.univ i ψ (Dψ i))
    (hψSupport : tsupport ψ ⊆ V) :
    ∃ r : ℝ, 0 < r ∧
      (∀ ε : ℝ, 0 < ε → ε < r →
        ContDiff ℝ (⊤ : ℕ∞) (spacetimeMollification ε ψ) ∧
        HasCompactSupport (spacetimeMollification ε ψ) ∧
        tsupport (spacetimeMollification ε ψ) ⊆ V ∧
        (∀ i z, velocityGradient (spacetimeMollification ε ψ) z i =
          spacetimeMollification ε (Dψ i) z) ∧
        ContDiff ℝ (⊤ : ℕ∞)
          (spatialDifferenceQuotient k (-h) (spacetimeMollification ε ψ)) ∧
        HasCompactSupport
          (spatialDifferenceQuotient k (-h) (spacetimeMollification ε ψ)) ∧
        tsupport (spatialDifferenceQuotient k (-h)
          (spacetimeMollification ε ψ)) ⊆ S) ∧
      Filter.Tendsto (fun ε : ℝ ↦ eLpNorm (spacetimeMollification ε ψ - ψ) 2 volume)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
      ∀ i, Filter.Tendsto (fun ε : ℝ ↦
        eLpNorm (spacetimeMollification ε (Dψ i) - Dψ i) 2 volume)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hψCompact : HasCompactSupport ψ :=
    hVcompact.of_isClosed_subset (isClosed_tsupport ψ) (hψSupport.trans subset_closure)
  obtain ⟨r, hr, hcollar⟩ := hψCompact.isCompact.exists_cthickening_subset_open
    hVopen hψSupport
  refine ⟨r, hr, ?_,
    SpacetimeMollifierL2.tendsto_eLpNorm_spacetimeMollification_sub ψ hψ,
    fun i ↦ SpacetimeMollifierL2.tendsto_eLpNorm_spacetimeMollification_sub
      (Dψ i) (hDψ i)⟩
  intro ε hε hεr
  have hsmooth := contDiff_spacetimeMollification hε ψ
    (hψ.locallyIntegrable (by norm_num))
  have hcompact : HasCompactSupport (spacetimeMollification ε ψ) := by
    exact (spacetimeMollifier_hasCompactSupport hε).convolution
      (ContinuousLinearMap.lsmul ℝ ℝ) hψCompact
  have hsupp : tsupport (spacetimeMollification ε ψ) ⊆ V :=
    (tsupport_spacetimeMollification_subset_cthickening hε).trans
      ((Metric.cthickening_mono hεr.le (tsupport ψ)).trans hcollar)
  have hgrad (i : Fin d) := velocityGradient_spacetimeMollification hε i ψ (Dψ i)
    (hψ.locallyIntegrable (by norm_num))
    ((hDψ i).locallyIntegrable (by norm_num)) (hψWeak i)
  have htestSmooth : ContDiff ℝ (⊤ : ℕ∞)
      (spatialDifferenceQuotient k (-h) (spacetimeMollification ε ψ)) :=
    ContDiff.spatialDifferenceQuotient hsmooth
  have htestCompact : HasCompactSupport
      (spatialDifferenceQuotient k (-h) (spacetimeMollification ε ψ)) :=
    HasCompactSupport.spatialDifferenceQuotient hcompact
  have htestSupport : tsupport (spatialDifferenceQuotient k (-h)
      (spacetimeMollification ε ψ)) ⊆ S := by
    exact tsupport_spatialDifferenceQuotient_subset_of_mapsTo_spatialShift_neg
      k (-h) (spacetimeMollification ε ψ) hsupp hVS (by simpa using hVshift)
  exact ⟨hsmooth, hcompact, hsupp, fun i z ↦ congrFun (hgrad i) z,
    htestSmooth, htestCompact, htestSupport⟩

/-- A fixed nonzero spatial quotient is a bounded operator on ambient `L²`,
so it preserves strong `L²` convergence. -/
private theorem tendsto_eLpNorm_spatialDifferenceQuotient_sub
    {d : ℕ} {l : Filter ℝ} (k : Fin d) (h : ℝ) (hh : h ≠ 0)
    (f : ℝ → TimeVelocity d → ℝ) (f₀ : TimeVelocity d → ℝ)
    (hf : ∀ᶠ ε in l, MemLp (f ε) 2 volume) (hf₀ : MemLp f₀ 2 volume)
    (hlim : Filter.Tendsto (fun ε ↦ eLpNorm (f ε - f₀) 2 volume)
      l (nhds 0)) :
    Filter.Tendsto (fun ε ↦ eLpNorm
      (spatialDifferenceQuotient k h (f ε) -
        spatialDifferenceQuotient k h f₀) 2 volume) l (nhds 0) := by
  let g : ℝ → TimeVelocity d → ℝ := fun ε ↦ f ε - f₀
  have hg : ∀ᶠ ε in l, MemLp (g ε) 2 volume := by
    filter_upwards [hf] with ε hε
    exact hε.sub hf₀
  have hshiftNorm : ∀ᶠ ε in l,
      eLpNorm (g ε ∘ spatialShift k h) 2 volume = eLpNorm (g ε) 2 volume := by
    filter_upwards [hg] with ε hε
    exact eLpNorm_comp_measurePreserving hε.aestronglyMeasurable
      (spatialShift_measurePreserving k h)
  have hbound : ∀ᶠ ε in l, eLpNorm
      (spatialDifferenceQuotient k h (f ε) -
        spatialDifferenceQuotient k h f₀) 2 volume ≤
        ‖(1 / h : ℝ)‖ₑ * (eLpNorm (g ε) 2 volume + eLpNorm (g ε) 2 volume) := by
    filter_upwards [hg, hshiftNorm] with ε hε hshift
    have hshiftMeas : AEStronglyMeasurable (g ε ∘ spatialShift k h) volume :=
      (hε.comp_measurePreserving (spatialShift_measurePreserving k h)).aestronglyMeasurable
    have hsubMeas : AEStronglyMeasurable
        ((g ε ∘ spatialShift k h) - g ε) volume :=
      hshiftMeas.sub hε.aestronglyMeasurable
    rw [show spatialDifferenceQuotient k h (f ε) -
        spatialDifferenceQuotient k h f₀ =
          (1 / h : ℝ) • ((g ε ∘ spatialShift k h) - g ε) by
      funext z
      simp only [g, spatialDifferenceQuotient_apply, spatialTranslate_apply,
        Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply]
      field_simp [hh]
      ring]
    rw [eLpNorm_const_smul]
    gcongr
    exact (eLpNorm_sub_le (by norm_num)).trans_eq
      (by rw [hshift])
  have hright : Filter.Tendsto (fun ε ↦
      ‖(1 / h : ℝ)‖ₑ * (eLpNorm (g ε) 2 volume + eLpNorm (g ε) 2 volume))
      l (nhds 0) := by
    simpa only [zero_add, mul_zero] using
      ENNReal.Tendsto.const_mul (hlim.add hlim)
        (Or.inr (enorm_ne_top : ‖(1 / h : ℝ)‖ₑ ≠ ∞))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hright
    (Filter.Eventually.of_forall fun _ ↦ bot_le) hbound

/-- The source stays undifferenced when the mollified localized quotient is
passed to the fixed backward quotient. -/
private theorem tendsto_sourcePairing_mollifiedBackwardQuotient
    {d : ℕ} (S : Set (TimeVelocity d)) (R ψ : TimeVelocity d → ℝ)
    (hR : ParabolicMemLpOn S 2 R) (hψ : MemLp ψ 2 volume)
    (k : Fin d) (h : ℝ) (hh : h ≠ 0) :
    Filter.Tendsto (fun ε : ℝ ↦ ∫ z in S, R z *
      spatialDifferenceQuotient k (-h) (spacetimeMollification ε ψ) z)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ z in S, R z * spatialDifferenceQuotient k (-h) ψ z)) := by
  have hmoll : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),
      MemLp (spacetimeMollification ε ψ) 2 volume := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact SpacetimeMollifierL2.spacetimeMollification_memLp hε ψ hψ
  have hquotLim := tendsto_eLpNorm_spatialDifferenceQuotient_sub k (-h)
    (neg_ne_zero.mpr hh) (fun ε ↦ spacetimeMollification ε ψ) ψ hmoll hψ
    (SpacetimeMollifierL2.tendsto_eLpNorm_spacetimeMollification_sub ψ hψ)
  have hquotMem (u : TimeVelocity d → ℝ) (hu : MemLp u 2 volume) :
      MemLp (spatialDifferenceQuotient k (-h) u) 2 volume := by
    rw [show spatialDifferenceQuotient k (-h) u =
        (1 / (-h) : ℝ) • ((u ∘ spatialShift k (-h)) - u) by
      funext z
      simp only [spatialDifferenceQuotient_apply, spatialTranslate_apply,
        Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply]
      ring]
    exact ((hu.comp_measurePreserving
      (spatialShift_measurePreserving k (-h))).sub hu).const_smul _
  have hquotLimS : Filter.Tendsto (fun ε ↦ eLpNorm
      (spatialDifferenceQuotient k (-h) (spacetimeMollification ε ψ) -
        spatialDifferenceQuotient k (-h) ψ) 2
      ((volume : Measure (TimeVelocity d)).restrict S))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hquotLim
      (Filter.Eventually.of_forall fun _ ↦ bot_le)
      (Filter.Eventually.of_forall fun ε ↦
        eLpNorm_mono_measure _ Measure.restrict_le_self)
  apply HypoellipticAleksandrov.Analysis.tendsto_integral_mul_of_tendsto_eLpNorm_two
    (fun _ ↦ R) (fun ε ↦ spatialDifferenceQuotient k (-h)
      (spacetimeMollification ε ψ)) R (spatialDifferenceQuotient k (-h) ψ)
  · exact Filter.Eventually.of_forall fun _ ↦ hR
  · filter_upwards [hmoll] with ε hε
    exact (hquotMem _ hε).mono_measure Measure.restrict_le_self
  · exact hR
  · exact (hquotMem _ hψ).mono_measure Measure.restrict_le_self
  · have hzero : (fun ε : ℝ ↦ eLpNorm
        (fun _ : TimeVelocity d ↦ (0 : ℝ)) 2
        ((volume : Measure (TimeVelocity d)).restrict S)) =
        fun _ ↦ (0 : ℝ≥0∞) := by
      funext ε
      exact eLpNorm_zero
    simpa only [sub_self, Pi.zero_apply, hzero] using
      (tendsto_const_nhds : Filter.Tendsto
        (fun _ : ℝ ↦ (0 : ℝ≥0∞)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
  · simpa only [Pi.sub_def] using hquotLimS

/-- Entrywise principal-flux transposition on a compact carrier is stable
under strong `L²` approximation of the compactly supported test gradient.
The quotient falls on the flux only in the forward-quotient pairing. -/
private theorem tendsto_fluxPairing_backwardQuotient_eq_forwardQuotient
    {d : ℕ} {l : Filter ℝ} (U V : Set (TimeVelocity d))
    (hUmeas : MeasurableSet U) (hVU : V ⊆ U)
    (H : TimeVelocity d → ℝ) (hH : ParabolicMemLpOn U 2 H)
    (k : Fin d) (h : ℝ)
    (hshift : Set.MapsTo (spatialShift k h) V U)
    (f : ℝ → TimeVelocity d → ℝ) (f₀ : TimeVelocity d → ℝ)
    (hf : ∀ᶠ ε in l, MemLp (f ε) 2 volume)
    (hfcont : ∀ᶠ ε in l, Continuous (f ε))
    (hfcompact : ∀ᶠ ε in l, HasCompactSupport (f ε))
    (hfsupport : ∀ᶠ ε in l, tsupport (f ε) ⊆ V)
    (hf₀ : MemLp f₀ 2 volume)
    (hlim : Filter.Tendsto (fun ε ↦ eLpNorm (f ε - f₀) 2 volume)
      l (nhds 0)) :
    (Filter.Tendsto (fun ε ↦ ∫ z in U, H z *
        spatialDifferenceQuotient k (-h) (f ε) z)
      l (nhds (-∫ z in V, spatialDifferenceQuotient k h H z * f₀ z))) ∧
      (∀ᶠ ε in l, (∫ z in U, H z *
          spatialDifferenceQuotient k (-h) (f ε) z) =
        -∫ z in V, spatialDifferenceQuotient k h H z * f ε z) := by
  have hqH : ParabolicMemLpOn V 2 (spatialDifferenceQuotient k h H) :=
    hH.spatialDifferenceQuotient_of_subset_mapsTo k h hVU hshift
  have hpair : Filter.Tendsto (fun ε ↦
      ∫ z in V, spatialDifferenceQuotient k h H z * f ε z)
      l (nhds (∫ z in V, spatialDifferenceQuotient k h H z * f₀ z)) := by
    apply HypoellipticAleksandrov.Analysis.tendsto_integral_mul_of_tendsto_eLpNorm_two
      (fun _ ↦ spatialDifferenceQuotient k h H) f
      (spatialDifferenceQuotient k h H) f₀
    · exact Filter.Eventually.of_forall fun _ ↦ hqH
    · filter_upwards [hf] with ε hε
      exact hε.mono_measure Measure.restrict_le_self
    · exact hqH
    · exact hf₀.mono_measure Measure.restrict_le_self
    · have hzero : (fun ε : ℝ ↦ eLpNorm
          (fun _ : TimeVelocity d ↦ (0 : ℝ)) 2
          ((volume : Measure (TimeVelocity d)).restrict V)) =
          fun _ ↦ (0 : ℝ≥0∞) := by
        funext ε
        exact eLpNorm_zero
      simpa only [sub_self, Pi.zero_apply, hzero] using
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ ↦ (0 : ℝ≥0∞)) l (nhds 0))
    · exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
        (Filter.Eventually.of_forall fun _ ↦ bot_le)
        (Filter.Eventually.of_forall fun ε ↦
          eLpNorm_mono_measure _ Measure.restrict_le_self)
  have htranspose : ∀ᶠ ε in l, (∫ z in U, H z *
      spatialDifferenceQuotient k (-h) (f ε) z) =
      -∫ z in V, spatialDifferenceQuotient k h H z * f ε z := by
    filter_upwards [hfcont, hfcompact, hfsupport] with ε hcont hcompact hsupp
    have ht := setIntegral_spatialDifferenceQuotient_mul_eq_neg_mul_spatialDifferenceQuotient_neg
      U k h H (f ε) hH hcont hcompact (hsupp.trans hVU)
      (fun z hz ↦ hshift (hsupp hz))
    calc
      (∫ z in U, H z * spatialDifferenceQuotient k (-h) (f ε) z) =
          -∫ z in U, spatialDifferenceQuotient k h H z * f ε z := by
        linarith
      _ = -∫ z in V, spatialDifferenceQuotient k h H z * f ε z := by
        congr 1
        exact setIntegral_eq_of_subset_of_forall_diff_eq_zero hUmeas hVU
          (fun z hz ↦ by
            have hzero : f ε z = 0 := image_eq_zero_of_notMem_tsupport
              (fun hzt ↦ hz.2 (hsupp hzt))
            simp only [hzero, mul_zero])
  refine ⟨?_, htranspose⟩
  exact (hpair.neg).congr' (htranspose.mono fun _ heq ↦ heq.symm)

/-- The preceding carrier lemma applied to the entrywise principal flux
`Hᵢⱼ = Aᵢⱼ Gⱼ`, obtaining its local `L²` representative directly from
the compact-carrier flux hypothesis. -/
private theorem tendsto_principalFluxEntry_backwardQuotient_eq_forwardQuotient
    {d : ℕ} {l : Filter ℝ} (S K V : Set (TimeVelocity d))
    (hKcompact : IsCompact K) (hKS : K ⊆ S) (hKV : V ⊆ K)
    (A : TimeVelocity d → PDE.Mat d) (G : Fin d → TimeVelocity d → ℝ)
    (hFlux : ∀ i j, ∀ C : Set (TimeVelocity d), IsCompact C → C ⊆ S →
      ParabolicMemLpOn C 2 (fun z ↦ A z i j * G j z))
    (i j k : Fin d) (h : ℝ) (hshift : Set.MapsTo (spatialShift k h) V K)
    (f : ℝ → TimeVelocity d → ℝ) (f₀ : TimeVelocity d → ℝ)
    (hf : ∀ᶠ ε in l, MemLp (f ε) 2 volume)
    (hfcont : ∀ᶠ ε in l, Continuous (f ε))
    (hfcompact : ∀ᶠ ε in l, HasCompactSupport (f ε))
    (hfsupport : ∀ᶠ ε in l, tsupport (f ε) ⊆ V)
    (hf₀ : MemLp f₀ 2 volume)
    (hlim : Filter.Tendsto (fun ε ↦ eLpNorm (f ε - f₀) 2 volume)
      l (nhds 0)) :
    (Filter.Tendsto (fun ε ↦ ∫ z in K, (A z i j * G j z) *
        spatialDifferenceQuotient k (-h) (f ε) z)
      l (nhds (-∫ z in V, spatialDifferenceQuotient k h
        (fun x ↦ A x i j * G j x) z * f₀ z))) ∧
      (∀ᶠ ε in l, (∫ z in K, (A z i j * G j z) *
          spatialDifferenceQuotient k (-h) (f ε) z) =
        -∫ z in V, spatialDifferenceQuotient k h
          (fun x ↦ A x i j * G j x) z * f ε z) := by
  exact tendsto_fluxPairing_backwardQuotient_eq_forwardQuotient K V
    hKcompact.measurableSet hKV (fun z ↦ A z i j * G j z)
    (hFlux i j K hKcompact hKS) k h hshift f f₀ hf hfcont hfcompact
    hfsupport hf₀ hlim

/-- Rearranging the supplied divergence identity for the mollified
backward-quotient test gives the signs produced by testing with its negative. -/
private theorem testedEquation_neg_mollifiedBackwardQuotient
    {d : ℕ} {S : Set (TimeVelocity d)}
    (A : TimeVelocity d → PDE.Mat d) (q R : TimeVelocity d → ℝ)
    (G : Fin d → TimeVelocity d → ℝ)
    (hEq : ∀ φ : TimeVelocity d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ S →
      -(∫ z in S, q z * timeDerivative φ z) -
          ∑ i, ∑ j, ∫ z in S,
            A z i j * G j z * velocityGradient φ z i =
        ∫ z in S, R z * φ z)
    (k : Fin d) (h ε : ℝ) (ψ : TimeVelocity d → ℝ)
    (hεSmooth : ContDiff ℝ (⊤ : ℕ∞)
      (spacetimeMollification ε ψ))
    (hεCompact : HasCompactSupport (spacetimeMollification ε ψ))
    (hTestSupport : tsupport (spatialDifferenceQuotient k (-h)
      (spacetimeMollification ε ψ)) ⊆ S) :
    (∫ z in S, q z * timeDerivative
        (spatialDifferenceQuotient k (-h) (spacetimeMollification ε ψ)) z) +
      ∑ i, ∑ j, ∫ z in S, A z i j * G j z *
        velocityGradient
          (spatialDifferenceQuotient k (-h) (spacetimeMollification ε ψ)) z i =
      -(∫ z in S, R z * spatialDifferenceQuotient k (-h)
        (spacetimeMollification ε ψ) z) := by
  have hTestSmooth : ContDiff ℝ (⊤ : ℕ∞)
      (spatialDifferenceQuotient k (-h) (spacetimeMollification ε ψ)) :=
    ContDiff.spatialDifferenceQuotient hεSmooth
  have hTestCompact : HasCompactSupport
      (spatialDifferenceQuotient k (-h) (spacetimeMollification ε ψ)) :=
    HasCompactSupport.spatialDifferenceQuotient hεCompact
  have heq := hEq
    (spatialDifferenceQuotient k (-h) (spacetimeMollification ε ψ))
    hTestSmooth hTestCompact hTestSupport
  linarith

/-- A spatial difference quotient commutes exactly with a finite sum, without
any regularity or nonzero-step assumption. -/
private theorem spatialDifferenceQuotient_finset_sum
    {d : ℕ} {ι : Type*} (s : Finset ι) (k : Fin d) (h : ℝ)
    (H : ι → TimeVelocity d → ℝ) :
    spatialDifferenceQuotient k h (fun x ↦ ∑ j ∈ s, H j x) =
      fun z ↦ ∑ j ∈ s, spatialDifferenceQuotient k h (H j) z := by
  funext z
  simp only [spatialDifferenceQuotient_apply, spatialTranslate_apply]
  rw [← Finset.sum_sub_distrib, Finset.sum_div]

/-- The weighted time-energy density is integrable on the original carrier.
Only local `L²` control of the quotient near the compact weight support is
used. -/
private theorem integrableOn_timeDerivative_mul_spatialDifferenceQuotient_sq
    {d : ℕ} {S V : Set (TimeVelocity d)} (hVS : V ⊆ S)
    (q : TimeVelocity d → ℝ) (hq : ParabolicMemLpOn V 2 q)
    (w : TimeVelocity d → ℝ)
    (hwSmooth : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwCompact : HasCompactSupport w) (hwSupport : tsupport w ⊆ V) :
    IntegrableOn (fun z ↦ timeDerivative w z * q z ^ 2) S := by
  have hdtTop : ParabolicMemLpOn V ∞ (timeDerivative w) :=
    ((contDiff_infty_iff_fderiv.mp hwSmooth).2.clm_apply contDiff_const).continuous
      |>.memLp_of_hasCompactSupport
        (by
          change HasCompactSupport (fun z ↦ fderiv ℝ w z (1, 0))
          simpa using hwCompact.fderiv_apply (𝕜 := ℝ) ((1, 0) : TimeVelocity d))
      |>.restrict V
  have hV : IntegrableOn (fun z ↦ timeDerivative w z * q z ^ 2) V := by
    have hp := (hq.mul' (r := 2) hdtTop).integrable_mul hq
    apply hp.congr
    filter_upwards with z
    simp only [Pi.mul_apply]
    ring
  have hsupp : Function.support (fun z ↦ timeDerivative w z * q z ^ 2) ⊆ V := by
    intro z hz
    have hdtz : timeDerivative w z ≠ 0 := by
      intro hzero
      exact hz (by simp [hzero])
    exact hwSupport (timeDerivative_tsupport_subset (subset_tsupport _ hdtz))
  have hglobal := (integrableOn_iff_integrable_of_support_subset hsupp).mp hV
  exact (integrableOn_iff_integrable_of_support_subset (hsupp.trans hVS)).mpr hglobal

/-- Pairing an `L²` source on a carrier with a fixed backward quotient of a
global `L²` function is integrable on that carrier. -/
private theorem integrableOn_source_mul_spatialDifferenceQuotient
    {d : ℕ} (S : Set (TimeVelocity d))
    (R ψ : TimeVelocity d → ℝ) (hR : ParabolicMemLpOn S 2 R)
    (hψ : MemLp ψ 2 volume) (k : Fin d) (h : ℝ) :
    IntegrableOn (fun z ↦ R z * spatialDifferenceQuotient k (-h) ψ z) S := by
  have hquot : MemLp (spatialDifferenceQuotient k (-h) ψ) 2 volume := by
    rw [show spatialDifferenceQuotient k (-h) ψ =
        (1 / (-h) : ℝ) • ((ψ ∘ spatialShift k (-h)) - ψ) by
      funext z
      simp only [spatialDifferenceQuotient_apply, spatialTranslate_apply,
        Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply]
      ring]
    exact ((hψ.comp_measurePreserving
      (spatialShift_measurePreserving k (-h))).sub hψ).const_smul _
  exact hR.integrable_mul (hquot.mono_measure Measure.restrict_le_self)

/-- The aggregate forward flux quotient paired with a compactly supported
global `L²` test gradient is integrable on the original carrier. -/
private theorem integrableOn_sum_principalFluxQuotient_mul
    {d : ℕ} {S C V : Set (TimeVelocity d)}
    (hCcompact : IsCompact C) (hCS : C ⊆ S) (hVC : V ⊆ C)
    (A : TimeVelocity d → PDE.Mat d) (G : Fin d → TimeVelocity d → ℝ)
    (hFlux : ∀ i j, ∀ K : Set (TimeVelocity d), IsCompact K → K ⊆ S →
      ParabolicMemLpOn K 2 (fun z ↦ A z i j * G j z))
    (i k : Fin d) (h : ℝ)
    (hshift : Set.MapsTo (spatialShift k h) V C)
    (Dψ : TimeVelocity d → ℝ) (hDψ : MemLp Dψ 2 volume)
    (hDψSupport : tsupport Dψ ⊆ V) :
    IntegrableOn (fun z ↦ spatialDifferenceQuotient k h
        (fun x ↦ ∑ j, A x i j * G j x) z * Dψ z) S := by
  have hentries (j : Fin d) : ParabolicMemLpOn V 2
      (spatialDifferenceQuotient k h (fun z ↦ A z i j * G j z)) :=
    (hFlux i j C hCcompact hCS).spatialDifferenceQuotient_of_subset_mapsTo
      k h hVC hshift
  have hsum : ParabolicMemLpOn V 2 (fun z ↦ ∑ j,
      spatialDifferenceQuotient k h (fun x ↦ A x i j * G j x) z) :=
    memLp_finset_sum _ fun j _ ↦ hentries j
  have hV : IntegrableOn (fun z ↦ spatialDifferenceQuotient k h
      (fun x ↦ ∑ j, A x i j * G j x) z * Dψ z) V := by
    rw [spatialDifferenceQuotient_finset_sum Finset.univ k h
      (fun j x ↦ A x i j * G j x)]
    exact hsum.integrable_mul (hDψ.mono_measure Measure.restrict_le_self)
  have hsupp : Function.support (fun z ↦ spatialDifferenceQuotient k h
      (fun x ↦ ∑ j, A x i j * G j x) z * Dψ z) ⊆ V := by
    intro z hz
    have hDz : Dψ z ≠ 0 := by
      intro hzero
      exact hz (by simp [hzero])
    exact hDψSupport (subset_tsupport Dψ hDz)
  exact ((integrableOn_iff_integrable_of_support_subset hsupp).mp hV).restrict

/-- The quotient-test energy identity obtained from a tested divergence-form
equation by smooth compact approximation. -/
theorem integral_spatialDifferenceQuotient_energyIdentity_of_testedEquation
    (d : ℕ) (S : Set (TimeVelocity d)) (hS : IsOpen S)
    (A : TimeVelocity d → PDE.Mat d) (q R : TimeVelocity d → ℝ)
    (G : Fin d → TimeVelocity d → ℝ)
    (hq : ParabolicMemLpOn S 2 q) (hR : ParabolicMemLpOn S 2 R)
    (hG : ∀ j, ParabolicMemLpOn S 2 (G j))
    (hFlux : ∀ i j, ∀ K : Set (TimeVelocity d), IsCompact K → K ⊆ S →
      ParabolicMemLpOn K 2 (fun z ↦ A z i j * G j z))
    (hWeak : ∀ j, HasWeakVelocityPartialDerivOn S j q (G j))
    (hEq : ∀ φ : TimeVelocity d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ S →
      -(∫ z in S, q z * timeDerivative φ z) -
          ∑ i, ∑ j, ∫ z in S,
            A z i j * G j z * velocityGradient φ z i =
        ∫ z in S, R z * φ z)
    (w : TimeVelocity d → ℝ)
    (hwSmooth : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwCompact : HasCompactSupport w) (hwSupport : tsupport w ⊆ S)
    (k : Fin d) (h : ℝ) (hh : h ≠ 0)
    (hwShift : Set.MapsTo (spatialShift k h) (tsupport w) S) :
    IntegrableOn
        (fun z ↦ timeDerivative w z *
          (spatialDifferenceQuotient k h q z) ^ 2) S ∧
      (∀ i, IntegrableOn
        (fun z ↦ spatialDifferenceQuotient k h
            (fun x ↦ ∑ j, A x i j * G j x) z *
          (velocityGradient w z i * spatialDifferenceQuotient k h q z +
            w z * spatialDifferenceQuotient k h (G i) z)) S) ∧
      IntegrableOn
        (fun z ↦ R z * spatialDifferenceQuotient k (-h)
          (fun x ↦ w x * spatialDifferenceQuotient k h q x) z) S ∧
      (-1 / 2 : ℝ) *
          (∫ z in S, timeDerivative w z *
            (spatialDifferenceQuotient k h q z) ^ 2) -
        ∑ i, ∫ z in S, spatialDifferenceQuotient k h
            (fun x ↦ ∑ j, A x i j * G j x) z *
          (velocityGradient w z i * spatialDifferenceQuotient k h q z +
            w z * spatialDifferenceQuotient k h (G i) z) =
        -(∫ z in S, R z * spatialDifferenceQuotient k (-h)
          (fun x ↦ w x * spatialDifferenceQuotient k h q x) z) := by
  obtain ⟨V, C, hVopen, hVcompact, hwV, hVS, hCcompact, hVC, hCS,
      hVshift, hqh, hGh, hqhWeak, hψ, hDψ, hψWeak, hDψSupport⟩ :=
    exists_global_localizedQuotient_weakGradient hS q G hq hG hWeak w
      hwSmooth hwCompact hwSupport k h hwShift
  let qh : TimeVelocity d → ℝ := spatialDifferenceQuotient k h q
  let ψ : TimeVelocity d → ℝ := fun z ↦ w z * qh z
  let Dψ : Fin d → TimeVelocity d → ℝ := fun i z ↦
    velocityGradient w z i * qh z +
      w z * spatialDifferenceQuotient k h (G i) z
  obtain ⟨r, hr, htest, hψlim, hDψlim⟩ :=
    exists_mollifiedLocalizedQuotient_testPackage hVopen hVcompact hVS k h
      (fun z hz ↦ hCS (hVshift hz)) ψ Dψ hψ hDψ hψWeak
      (tsupport_mul_subset_left.trans hwV)
  have htimeInt : IntegrableOn (fun z ↦ timeDerivative w z * qh z ^ 2) S :=
    integrableOn_timeDerivative_mul_spatialDifferenceQuotient_sq hVS qh hqh w
      hwSmooth hwCompact hwV
  have hsourceInt : IntegrableOn (fun z ↦ R z *
      spatialDifferenceQuotient k (-h) ψ z) S :=
    integrableOn_source_mul_spatialDifferenceQuotient S R ψ hR hψ k h
  have hfluxInt (i : Fin d) : IntegrableOn (fun z ↦
      spatialDifferenceQuotient k h (fun x ↦ ∑ j, A x i j * G j x) z *
        Dψ i z) S :=
    integrableOn_sum_principalFluxQuotient_mul hCcompact hCS hVC A G hFlux
      i k h hVshift (Dψ i) (hDψ i) (hDψSupport i)
  refine ⟨htimeInt, hfluxInt, hsourceInt, ?_⟩
  let l : Filter ℝ := nhdsWithin 0 (Set.Ioi 0)
  let f : ℝ → TimeVelocity d → ℝ := fun ε ↦ spacetimeMollification ε ψ
  have hevent : ∀ᶠ ε in l, 0 < ε ∧ ε < r := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hr).filter_mono inf_le_left] with ε hε hεr
    exact ⟨hε, hεr⟩
  have hfMem : ∀ᶠ ε in l, MemLp (f ε) 2 volume := by
    filter_upwards [hevent] with ε hε
    exact SpacetimeMollifierL2.spacetimeMollification_memLp hε.1 ψ hψ
  have htimeLim : Filter.Tendsto (fun ε ↦ ∫ z in V, qh z *
      timeDerivative (f ε) z) l
      (nhds ((1 / 2 : ℝ) * ∫ z in V, timeDerivative w z * qh z ^ 2)) := by
    exact tendsto_localized_timeEnergy_spacetimeMollification hVopen qh w hqh
      hwSmooth hwCompact hwV
  have hsourceLim : Filter.Tendsto (fun ε ↦ ∫ z in S, R z *
      spatialDifferenceQuotient k (-h) (f ε) z) l
      (nhds (∫ z in S, R z * spatialDifferenceQuotient k (-h) ψ z)) := by
    exact tendsto_sourcePairing_mollifiedBackwardQuotient S R ψ hR hψ k h hh
  have hfluxLim (i j : Fin d) : Filter.Tendsto (fun ε ↦
      ∫ z in V, spatialDifferenceQuotient k h
        (fun x ↦ A x i j * G j x) z * spacetimeMollification ε (Dψ i) z) l
      (nhds (∫ z in V, spatialDifferenceQuotient k h
        (fun x ↦ A x i j * G j x) z * Dψ i z)) := by
    have hentry : ParabolicMemLpOn V 2
        (spatialDifferenceQuotient k h (fun z ↦ A z i j * G j z)) :=
      (hFlux i j C hCcompact hCS).spatialDifferenceQuotient_of_subset_mapsTo
        k h hVC hVshift
    apply HypoellipticAleksandrov.Analysis.tendsto_integral_mul_of_tendsto_eLpNorm_two
      (fun _ ↦ spatialDifferenceQuotient k h (fun z ↦ A z i j * G j z))
      (fun ε ↦ spacetimeMollification ε (Dψ i))
      (spatialDifferenceQuotient k h (fun z ↦ A z i j * G j z)) (Dψ i)
    · exact Filter.Eventually.of_forall fun _ ↦ hentry
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact (SpacetimeMollifierL2.spacetimeMollification_memLp hε (Dψ i)
        (hDψ i)).mono_measure Measure.restrict_le_self
    · exact hentry
    · exact (hDψ i).mono_measure Measure.restrict_le_self
    · convert (tendsto_const_nhds : Filter.Tendsto
        (fun _ : ℝ ↦ (0 : ℝ≥0∞)) l (nhds 0)) using 1
      simp
    · exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        (hDψlim i) (Filter.Eventually.of_forall fun _ ↦ bot_le)
        (Filter.Eventually.of_forall fun ε ↦
          eLpNorm_mono_measure _ Measure.restrict_le_self)
  have heqEventually : ∀ᶠ ε in l,
      -(∫ z in V, qh z * timeDerivative (f ε) z) -
          ∑ i, ∑ j, ∫ z in V, spatialDifferenceQuotient k h
            (fun x ↦ A x i j * G j x) z *
              spacetimeMollification ε (Dψ i) z =
        -(∫ z in S, R z * spatialDifferenceQuotient k (-h) (f ε) z) := by
    filter_upwards [hevent] with ε hε
    have hp := htest ε hε.1 hε.2
    have he := testedEquation_neg_mollifiedBackwardQuotient A q R G hEq k h ε ψ
      hp.1 hp.2.1 hp.2.2.2.2.2.2
    have ht := setIntegral_mul_timeDerivative_spatialDifferenceQuotient_neg
      hS.measurableSet hVS q hq k h (f ε) hp.1 hp.2.1 hp.2.2.1
      (fun z hz ↦ hCS (hVshift hz))
    have hf (i j : Fin d) :=
      setIntegral_mul_velocityGradient_spatialDifferenceQuotient_neg
        hS.measurableSet hCcompact hCS hVC (fun z ↦ A z i j * G j z)
        (hFlux i j C hCcompact hCS) k h (f ε) hp.1 hp.2.1 hp.2.2.1
        hVshift i
    dsimp only [f] at he ht hf ⊢
    rw [ht] at he
    have hfsum : (∑ i, ∑ j, ∫ z in S, A z i j * G j z *
        velocityGradient (spatialDifferenceQuotient k (-h)
          (spacetimeMollification ε ψ)) z i) =
        ∑ i, ∑ j, -(∫ z in V, spatialDifferenceQuotient k h
          (fun x ↦ A x i j * G j x) z *
            velocityGradient (spacetimeMollification ε ψ) z i) := by
      exact Finset.sum_congr rfl (fun i _ ↦ Finset.sum_congr rfl
        (fun j _ ↦ hf i j))
    rw [hfsum] at he
    have hgradsum : (∑ i, ∑ j, -(∫ z in V,
        spatialDifferenceQuotient k h (fun x ↦ A x i j * G j x) z *
          velocityGradient (spacetimeMollification ε ψ) z i)) =
        ∑ i, ∑ j, -(∫ z in V,
          spatialDifferenceQuotient k h (fun x ↦ A x i j * G j x) z *
            spacetimeMollification ε (Dψ i) z) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      congr 2
      funext z
      rw [hp.2.2.2.1 i z]
    rw [hgradsum] at he
    simp only [Finset.sum_neg_distrib] at he
    dsimp only [qh] at ⊢
    linarith
  have hleftLim : Filter.Tendsto (fun ε ↦
      -(∫ z in V, qh z * timeDerivative (f ε) z) -
        ∑ i, ∑ j, ∫ z in V, spatialDifferenceQuotient k h
          (fun x ↦ A x i j * G j x) z *
            spacetimeMollification ε (Dψ i) z) l
      (nhds (-((1 / 2 : ℝ) * ∫ z in V, timeDerivative w z * qh z ^ 2) -
        ∑ i, ∑ j, ∫ z in V, spatialDifferenceQuotient k h
          (fun x ↦ A x i j * G j x) z * Dψ i z)) := by
    exact htimeLim.neg.sub (tendsto_finset_sum _ fun i _ ↦
      tendsto_finset_sum _ fun j _ ↦
        hfluxLim i j)
  have hrightLim := hsourceLim.neg
  have heqEventually' : (λ ε ↦
      -(∫ z in S, R z * spatialDifferenceQuotient k (-h) (f ε) z)) =ᶠ[l]
      fun ε ↦ -(∫ z in V, qh z * timeDerivative (f ε) z) -
        ∑ i, ∑ j, ∫ z in V, spatialDifferenceQuotient k h
          (fun x ↦ A x i j * G j x) z *
            spacetimeMollification ε (Dψ i) z := by
    filter_upwards [heqEventually] with ε he
    exact he.symm
  have hlimEq := tendsto_nhds_unique hleftLim
    (hrightLim.congr' heqEventually')
  rw [show (∫ z in V, timeDerivative w z * qh z ^ 2) =
      ∫ z in S, timeDerivative w z * qh z ^ 2 by
        exact (setIntegral_eq_of_subset_of_forall_diff_eq_zero hS.measurableSet hVS
          (fun z hz ↦ by
            have hzero : timeDerivative w z = 0 :=
              image_eq_zero_of_notMem_tsupport
                (fun hzt ↦ hz.2 (hwV (timeDerivative_tsupport_subset hzt)))
            simp [hzero])).symm
    ] at hlimEq
  have hfluxEq (i : Fin d) :
      (∫ z in S, spatialDifferenceQuotient k h
          (fun x ↦ ∑ j, A x i j * G j x) z * Dψ i z) =
        ∑ j, ∫ z in V, spatialDifferenceQuotient k h
          (fun x ↦ A x i j * G j x) z * Dψ i z := by
    have hentryInt (j : Fin d) : IntegrableOn (fun z ↦
        spatialDifferenceQuotient k h (fun x ↦ A x i j * G j x) z *
          Dψ i z) V := by
      exact ((hFlux i j C hCcompact hCS).spatialDifferenceQuotient_of_subset_mapsTo
        k h hVC hVshift).integrable_mul
          ((hDψ i).mono_measure Measure.restrict_le_self)
    calc
      (∫ z in S, spatialDifferenceQuotient k h
          (fun x ↦ ∑ j, A x i j * G j x) z * Dψ i z) =
          ∫ z in V, spatialDifferenceQuotient k h
            (fun x ↦ ∑ j, A x i j * G j x) z * Dψ i z := by
        exact setIntegral_eq_of_subset_of_forall_diff_eq_zero hS.measurableSet hVS
          (fun z hz ↦ by
            have hzero : Dψ i z = 0 := image_eq_zero_of_notMem_tsupport
              (fun hzt ↦ hz.2 (hDψSupport i hzt))
            simp [hzero])
      _ = ∫ z in V, (∑ j, spatialDifferenceQuotient k h
            (fun x ↦ A x i j * G j x) z) * Dψ i z := by
        rw [spatialDifferenceQuotient_finset_sum Finset.univ k h
          (fun j x ↦ A x i j * G j x)]
      _ = ∑ j, ∫ z in V, spatialDifferenceQuotient k h
          (fun x ↦ A x i j * G j x) z * Dψ i z := by
        rw [show (fun z ↦ (∑ j, spatialDifferenceQuotient k h
            (fun x ↦ A x i j * G j x) z) * Dψ i z) =
          fun z ↦ ∑ j, spatialDifferenceQuotient k h
              (fun x ↦ A x i j * G j x) z * Dψ i z by
          funext z
          rw [Finset.sum_mul]]
        exact integral_finset_sum _ (fun j _ ↦ hentryInt j)
  rw [show (∑ i, ∫ z in S, spatialDifferenceQuotient k h
      (fun x ↦ ∑ j, A x i j * G j x) z * Dψ i z) =
      ∑ i, ∑ j, ∫ z in V, spatialDifferenceQuotient k h
        (fun x ↦ A x i j * G j x) z * Dψ i z by
    exact Finset.sum_congr rfl (fun i _ ↦ hfluxEq i)]
  simp_rw [qh, Dψ] at hlimEq ⊢
  linarith

end HypoellipticAleksandrov.Parabolic
