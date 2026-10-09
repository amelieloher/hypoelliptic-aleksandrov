module

public import HypoellipticAleksandrov.Parabolic.WeakDerivatives
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.Geometry.Manifold.SmoothApprox
public import Mathlib.Topology.UrysohnsLemma

/-!
# Interior-supported smooth functions are dense in time--velocity `L²`

On every open subset of time--velocity space, globally smooth compactly supported
real functions whose topological support remains in that subset are dense for the
restricted-volume `L²` norm.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal RealInnerProductSpace Topology

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

private theorem continuousCompact_contDiff_eLpNorm_sub_le_with_support_timeVelocity
    {d : ℕ} {μ : Measure (TimeVelocity d)} [IsFiniteMeasureOnCompacts μ]
    {f : TimeVelocity d → ℝ} (hfCompact : HasCompactSupport f)
    (hfCont : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : TimeVelocity d → ℝ,
      HasCompactSupport g ∧ ContDiff ℝ (⊤ : ℕ∞) g ∧
      Function.support g ⊆ Function.support f ∧
      eLpNorm (f - g) (2 : ℝ≥0∞) μ ≤ ENNReal.ofReal ε := by
  by_cases hf : f =ᵐ[μ] 0
  · refine ⟨0, HasCompactSupport.zero, contDiff_const, by simp, ?_⟩
    simp [eLpNorm_congr_ae hf]
  have htsupport : μ (tsupport f) ≠ ∞ := hfCompact.measure_lt_top.ne
  have hmeasure_pos : 0 < (μ <| tsupport f).toReal := by
    rw [← Measure.measure_support_eq_zero_iff _] at hf
    exact ENNReal.toReal_pos
      (pos_mono (subset_tsupport f) (pos_of_ne_zero hf)).ne' htsupport
  set ε' := ε * (μ <| tsupport f).toReal ^ (-(1 / (2 : ℝ≥0∞).toReal)) with hε'_def
  have hε' : 0 < ε' := by
    dsimp [ε']
    positivity
  have hscale : ENNReal.ofReal ε' * μ (tsupport f) ^ (1 / (2 : ℝ≥0∞).toReal) ≤
      ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_toReal htsupport, ENNReal.ofReal_rpow_of_pos hmeasure_pos,
      ← ENNReal.ofReal_mul hε'.le, ENNReal.ofReal_le_ofReal_iff hε.le, hε'_def, mul_assoc,
      ← Real.rpow_add hmeasure_pos, neg_add_cancel, Real.rpow_zero, mul_one]
  obtain ⟨g, hgSmooth, hgDist, hgSupport⟩ :=
    hfCont.exists_contDiff_approx (⊤ : ℕ∞) (ε := fun _ ↦ ε') (by fun_prop)
      (by intro; exact hε')
  refine ⟨g, hfCompact.mono hgSupport, hgSmooth, hgSupport, ?_⟩
  refine (eLpNorm_sub_le_of_dist_bdd μ ENNReal.coe_ne_top
    hfCompact.measurableSet.nullMeasurableSet hε'.le
    (hfCont.aestronglyMeasurable.sub hgSmooth.continuous.aestronglyMeasurable) ?_
    (subset_tsupport f) (hgSupport.trans (subset_tsupport f))).trans hscale
  intro x
  rw [dist_comm]
  exact (hgDist x).le

private theorem cutoff_error_ae_timeVelocity
    {d : ℕ} {U K : Set (TimeVelocity d)} (hU : IsOpen U)
    (g : TimeVelocity d → ℝ) (χ : C(TimeVelocity d, ℝ))
    (hχone : Set.EqOn χ 1 K) :
    g - (fun x ↦ χ x * g x) =ᵐ[timeVelocityVolumeOn U]
      ((U ∩ tsupport g) \ K).indicator (g - (fun x ↦ χ x * g x)) := by
  change g - (fun x ↦ χ x * g x) =ᵐ[volume.restrict U]
    ((U ∩ tsupport g) \ K).indicator (g - (fun x ↦ χ x * g x))
  rw [Filter.EventuallyEq, ae_restrict_iff' hU.measurableSet]
  filter_upwards with x hxU
  by_cases hx : x ∈ (U ∩ tsupport g) \ K
  · simp [hx]
  · rw [Set.indicator_of_notMem hx]
    by_cases hxK : x ∈ K
    · have hχ : χ x = 1 := hχone hxK
      simp only [Pi.sub_apply, hχ, one_mul, sub_self]
    · have hxnot : x ∉ tsupport g := by
        intro hxtsupport
        exact hx ⟨⟨hxU, hxtsupport⟩, hxK⟩
      simp only [Pi.sub_apply]
      rw [image_eq_zero_of_notMem_tsupport hxnot]
      simp only [mul_zero, sub_zero]

private theorem cutoff_error_indicator_bound_timeVelocity
    {d : ℕ} {U K : Set (TimeVelocity d)}
    (g : TimeVelocity d → ℝ) (χ : C(TimeVelocity d, ℝ))
    (hg : Continuous g)
    {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) (hC0 : 0 ≤ C)
    (hχrange : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (hset : MeasurableSet ((U ∩ tsupport g) \ K)) :
    eLpNorm (((U ∩ tsupport g) \ K).indicator
      (g - (fun x ↦ χ x * g x))) (2 : ℝ≥0∞) (timeVelocityVolumeOn U) ≤
      ENNReal.ofReal C * (timeVelocityVolumeOn U) ((U ∩ tsupport g) \ K) ^
        (1 / (2 : ℝ≥0∞).toReal) := by
  apply eLpNorm_indicator_sub_le_of_dist_bdd (timeVelocityVolumeOn U) ENNReal.coe_ne_top
    hset.nullMeasurableSet hC0
    ((hg.aestronglyMeasurable.sub
      (χ.continuous.mul hg).aestronglyMeasurable).indicator hset)
  intro x hx
  have hχ0 : 0 ≤ χ x := (hχrange x).1
  have hχ1 : χ x ≤ 1 := (hχrange x).2
  have hsub0 : 0 ≤ 1 - χ x := by linarith
  have hsub1 : |1 - χ x| ≤ 1 := by
    rw [abs_of_nonneg hsub0]
    linarith
  calc
    dist (g x) (χ x * g x) = |1 - χ x| * ‖g x‖ := by
      rw [dist_eq_norm]
      rw [show g x - χ x * g x = (1 - χ x) * g x by ring, norm_mul,
        Real.norm_eq_abs]
    _ ≤ |1 - χ x| * C := mul_le_mul_of_nonneg_left (hC x) (abs_nonneg _)
    _ ≤ C := by nlinarith [mul_nonneg hC0 (abs_nonneg (1 - χ x))]

private theorem cutoff_error_lt_of_core_timeVelocity
    {d : ℕ} {U K : Set (TimeVelocity d)}
    (g : TimeVelocity d → ℝ) (χ : C(TimeVelocity d, ℝ))
    {C r ε : ℝ} (hC0 : 0 ≤ C) (hCpos : 0 < C) (hr : 0 < r) (hε : 0 < ε)
    (hmeasure : (timeVelocityVolumeOn U) ((U ∩ tsupport g) \ K) < ENNReal.ofReal (r ^ 2))
    (herror : g - (fun x ↦ χ x * g x) =ᵐ[timeVelocityVolumeOn U]
      ((U ∩ tsupport g) \ K).indicator (g - (fun x ↦ χ x * g x)))
    (hindicator : eLpNorm (((U ∩ tsupport g) \ K).indicator
      (g - (fun x ↦ χ x * g x))) (2 : ℝ≥0∞) (timeVelocityVolumeOn U) ≤
      ENNReal.ofReal C * (timeVelocityVolumeOn U) ((U ∩ tsupport g) \ K) ^
        (1 / (2 : ℝ≥0∞).toReal))
    (hr_def : r = ε / (C + 1)) :
    eLpNorm (g - (fun x ↦ χ x * g x)) (2 : ℝ≥0∞) (timeVelocityVolumeOn U) <
      ENNReal.ofReal ε := by
  calc
    eLpNorm (g - (fun x ↦ χ x * g x)) (2 : ℝ≥0∞) (timeVelocityVolumeOn U) =
        eLpNorm (((U ∩ tsupport g) \ K).indicator
          (g - (fun x ↦ χ x * g x))) (2 : ℝ≥0∞) (timeVelocityVolumeOn U) :=
      eLpNorm_congr_ae herror
    _ ≤ ENNReal.ofReal C * (timeVelocityVolumeOn U) ((U ∩ tsupport g) \ K) ^
        (1 / (2 : ℝ≥0∞).toReal) := hindicator
    _ < ENNReal.ofReal C * (ENNReal.ofReal (r ^ 2)) ^
        (1 / (2 : ℝ≥0∞).toReal) := by
      exact ENNReal.mul_lt_mul_right (ENNReal.ofReal_ne_zero_iff.mpr hCpos)
        ENNReal.ofReal_ne_top (ENNReal.rpow_lt_rpow hmeasure (by norm_num))
    _ = ENNReal.ofReal (C * r) := by
      have hrpow : (r ^ 2) ^ (1 / (2 : ℝ)) = r := by
        rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs, abs_of_pos hr]
      rw [show 1 / (2 : ℝ≥0∞).toReal = (1 / (2 : ℝ)) by norm_num,
        ENNReal.ofReal_rpow_of_nonneg (sq_nonneg r) (by norm_num), hrpow,
        ← ENNReal.ofReal_mul hC0]
    _ < ENNReal.ofReal ε := by
      rw [ENNReal.ofReal_lt_ofReal_iff hε]
      rw [hr_def]
      calc
        C * (ε / (C + 1)) = (C / (C + 1)) * ε := by ring
        _ < 1 * ε := mul_lt_mul_of_pos_right
          ((div_lt_one (by linarith : 0 < C + 1)).mpr (by linarith)) hε
        _ = ε := one_mul _

private theorem compactCore_cutoff_eLpNorm_sub_lt_timeVelocity
    {d : ℕ} {U : Set (TimeVelocity d)} (hU : IsOpen U)
    {g : TimeVelocity d → ℝ} (hgSmooth : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgCompact : HasCompactSupport g) {ε : ℝ} (hε : 0 < ε) :
    ∃ h : TimeVelocity d → ℝ,
      Continuous h ∧ HasCompactSupport h ∧ tsupport h ⊆ U ∧
      eLpNorm (g - h) (2 : ℝ≥0∞) (timeVelocityVolumeOn U) < ENNReal.ofReal ε := by
  let μ : Measure (TimeVelocity d) := timeVelocityVolumeOn U
  have hmeas : MeasurableSet (U ∩ tsupport g) :=
    hU.measurableSet.inter (isClosed_tsupport g).measurableSet
  have hfinite : μ (U ∩ tsupport g) ≠ ∞ := by
    exact (measure_mono Set.inter_subset_right).trans_lt
      hgCompact.isCompact.measure_lt_top |>.ne
  rcases hgSmooth.continuous.bounded_above_of_compact_support hgCompact with ⟨C, hC⟩
  have hC0 : 0 ≤ C := (norm_nonneg (g 0)).trans (hC 0)
  by_cases hCzero : C = 0
  · have hgzero : g = 0 := by
      funext x
      apply norm_eq_zero.mp
      exact le_antisymm (by simpa [hCzero] using hC x) (norm_nonneg _)
    have hzero : eLpNorm (g - 0) (2 : ℝ≥0∞) (timeVelocityVolumeOn U) < ENNReal.ofReal ε := by
      simpa [hgzero] using ENNReal.ofReal_pos.2 hε
    exact ⟨0, continuous_zero, HasCompactSupport.zero, by simp, hzero⟩
  have hCpos : 0 < C := lt_of_le_of_ne hC0 (Ne.symm hCzero)
  let r : ℝ := ε / (C + 1)
  have hr : 0 < r := by
    dsimp [r]
    positivity
  rcases hmeas.exists_isCompact_diff_lt hfinite
    (ENNReal.ofReal_pos.2 (sq_pos_of_pos hr)).ne' with ⟨K, hKA, hKCompact, hKmeasure⟩
  rcases exists_continuousMap_one_of_isCompact_subset_isOpen hKCompact hU
    (hKA.trans Set.inter_subset_left) with ⟨χ, hχone, hχcompact, hχsupport, hχrange⟩
  have herror := cutoff_error_ae_timeVelocity hU g χ hχone
  have hindicator := cutoff_error_indicator_bound_timeVelocity
    g χ hgSmooth.continuous hC hC0 hχrange
    (hmeas.diff hKCompact.isClosed.measurableSet)
  have hcutoff : eLpNorm (g - (fun x ↦ χ x * g x)) (2 : ℝ≥0∞) (timeVelocityVolumeOn U) <
      ENNReal.ofReal ε := by
    simpa only [μ] using
      cutoff_error_lt_of_core_timeVelocity g χ hC0 hCpos hr hε hKmeasure herror hindicator rfl
  let h : TimeVelocity d → ℝ := fun x ↦ χ x * g x
  have hhcont : Continuous h := χ.continuous.mul hgSmooth.continuous
  have hhcompact : HasCompactSupport h :=
    hχcompact.of_isClosed_subset (isClosed_tsupport _) tsupport_mul_subset_left
  have hhsupport : tsupport h ⊆ U := tsupport_mul_subset_left.trans hχsupport
  exact ⟨h, hhcont, hhcompact, hhsupport, hcutoff⟩

private theorem lp_dist_toLp_toLp_le_timeVelocity
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} {ε : ℝ}
    (hf : MemLp f (2 : ℝ≥0∞) μ) (hg : MemLp g (2 : ℝ≥0∞) μ)
    (hε : 0 ≤ ε)
    (hfg : eLpNorm (f - g) (2 : ℝ≥0∞) μ ≤ ENNReal.ofReal ε) :
    dist (hf.toLp f) (hg.toLp g) ≤ ε := by
  rw [Lp.dist_def, eLpNorm_congr_ae (hf.coeFn_toLp.sub hg.coeFn_toLp)]
  calc
    (eLpNorm (f - g) (2 : ℝ≥0∞) μ).toReal ≤ (ENNReal.ofReal ε).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hfg
    _ = ε := ENNReal.toReal_ofReal hε

private theorem exists_smoothCompactlySupported_toLp_timeVelocity_dist_lt
    {d : ℕ} {U : Set (TimeVelocity d)} (hU : IsOpen U)
    (u : Lp ℝ (2 : ℝ≥0∞) (timeVelocityVolumeOn U))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (φ : TimeVelocity d → ℝ)
        (hφ : ParabolicMemLpOn U (2 : ℝ≥0∞) φ),
      ContDiff ℝ (⊤ : ℕ∞) φ ∧
      HasCompactSupport φ ∧
      tsupport φ ⊆ U ∧
      dist u (hφ.toLp φ) < ε := by
  let μ : Measure (TimeVelocity d) := timeVelocityVolumeOn U
  have hquarter : 0 < ε / 4 := by positivity
  obtain ⟨g, hgCompact, hgSmooth, hug⟩ :=
    (Lp.memLp u).exist_eLpNorm_sub_le ENNReal.coe_ne_top (by norm_num) hquarter
  obtain ⟨h, hhCont, hhCompact, hhSupport, hgh⟩ :=
    compactCore_cutoff_eLpNorm_sub_lt_timeVelocity hU hgSmooth hgCompact hquarter
  obtain ⟨q, hqCompact, hqSmooth, hqSupport, hhq⟩ :=
    continuousCompact_contDiff_eLpNorm_sub_le_with_support_timeVelocity
      (μ := timeVelocityVolumeOn U) hhCompact hhCont hquarter
  have hqTsupport : tsupport q ⊆ U := by
    rw [tsupport]
    exact (closure_mono hqSupport).trans
      (show closure (Function.support h) ⊆ U from hhSupport)
  let mg : MemLp g (2 : ℝ≥0∞) μ :=
    (hgSmooth.continuous.memLp_of_hasCompactSupport hgCompact).restrict U
  let mh : MemLp h (2 : ℝ≥0∞) μ :=
    (hhCont.memLp_of_hasCompactSupport hhCompact).restrict U
  let mq : MemLp q (2 : ℝ≥0∞) μ :=
    (hqSmooth.continuous.memLp_of_hasCompactSupport hqCompact).restrict U
  have hu_toLp : (Lp.memLp u).toLp (u : TimeVelocity d → ℝ) = u := by
    apply Lp.ext
    exact (Lp.memLp u).coeFn_toLp
  have hug' : dist u (mg.toLp g) ≤ ε / 4 := by
    rw [← hu_toLp]
    simpa only [μ] using
      lp_dist_toLp_toLp_le_timeVelocity (Lp.memLp u) mg hquarter.le hug
  have hgh' : dist (mg.toLp g) (mh.toLp h) ≤ ε / 4 := by
    simpa only [μ] using
      lp_dist_toLp_toLp_le_timeVelocity mg mh hquarter.le (le_of_lt hgh)
  have hhq' : dist (mh.toLp h) (mq.toLp q) ≤ ε / 4 := by
    simpa only [μ] using
      lp_dist_toLp_toLp_le_timeVelocity mh mq hquarter.le hhq
  refine ⟨q, mq, hqSmooth, hqCompact, hqTsupport, ?_⟩
  calc
    dist u (mq.toLp q) ≤ dist u (mg.toLp g) + dist (mg.toLp g) (mq.toLp q) :=
      dist_triangle _ _ _
    _ ≤ dist u (mg.toLp g) +
        (dist (mg.toLp g) (mh.toLp h) + dist (mh.toLp h) (mq.toLp q)) := by
      gcongr
      exact dist_triangle _ _ _
    _ ≤ ε / 4 + (ε / 4 + ε / 4) := by gcongr
    _ < ε := by linarith

/-- Globally smooth compactly supported functions whose topological support lies
in an open time--velocity carrier are dense in its restricted real `L²`. -/
theorem dense_smoothCompactlySupported_toLp_timeVelocity
    {d : ℕ} {U : Set (TimeVelocity d)} (hU : IsOpen U) :
    Dense {q : Lp ℝ (2 : ℝ≥0∞) (timeVelocityVolumeOn U) |
      ∃ (φ : TimeVelocity d → ℝ)
          (hφ : ParabolicMemLpOn U (2 : ℝ≥0∞) φ),
        ContDiff ℝ (⊤ : ℕ∞) φ ∧
        HasCompactSupport φ ∧
        tsupport φ ⊆ U ∧
        q = hφ.toLp φ} := by
  intro u
  refine (mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall).2 ?_
  intro ε hε
  rcases exists_smoothCompactlySupported_toLp_timeVelocity_dist_lt hU u hε with
    ⟨φ, hφ, hφSmooth, hφCompact, hφSupport, hdist⟩
  refine ⟨hφ.toLp φ, ?_, ?_⟩
  · exact ⟨φ, hφ, hφSmooth, hφCompact, hφSupport, rfl⟩
  · rw [Metric.mem_closedBall, dist_comm]
    exact hdist.le

end HypoellipticAleksandrov.Parabolic
