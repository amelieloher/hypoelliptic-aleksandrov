module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialSobolev
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.Geometry.Manifold.SmoothApprox

/-!
# Interior-supported smooth tests are dense in spatial `L²`

On every open native-vector domain, actual bundled smooth compactly supported
test functions are dense for the restricted-volume `L²` norm.  The proof first
uses global smooth compact approximation, localizes by a compact core and a
Urysohn cutoff, and smooths once more without enlarging topological support.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal RealInnerProductSpace Topology

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

variable {d : ℕ} {Ω : Set (PDE.Vec d)}

private theorem continuousCompact_contDiff_eLpNorm_sub_le_with_support
    {d : ℕ} {μ : Measure (PDE.Vec d)} [IsFiniteMeasureOnCompacts μ]
    {f : PDE.Vec d → ℝ} (hfCompact : HasCompactSupport f)
    (hfCont : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : PDE.Vec d → ℝ,
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

private theorem cutoff_error_ae
    {d : ℕ} {Ω K : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (g : PDE.Vec d → ℝ) (χ : C(PDE.Vec d, ℝ))
    (hχone : Set.EqOn χ 1 K) :
    g - (fun x ↦ χ x * g x) =ᵐ[PDE.volumeOn Ω]
      ((Ω ∩ tsupport g) \ K).indicator (g - (fun x ↦ χ x * g x)) := by
  change g - (fun x ↦ χ x * g x) =ᵐ[volume.restrict Ω]
    ((Ω ∩ tsupport g) \ K).indicator (g - (fun x ↦ χ x * g x))
  rw [Filter.EventuallyEq, ae_restrict_iff' hΩ.measurableSet]
  filter_upwards with x hxΩ
  by_cases hx : x ∈ (Ω ∩ tsupport g) \ K
  · simp [hx]
  · rw [Set.indicator_of_notMem hx]
    by_cases hxK : x ∈ K
    · have hχ : χ x = 1 := hχone hxK
      simp only [Pi.sub_apply, hχ, one_mul, sub_self]
    · have hxnot : x ∉ tsupport g := by
        intro hxtsupport
        exact hx ⟨⟨hxΩ, hxtsupport⟩, hxK⟩
      simp only [Pi.sub_apply]
      rw [image_eq_zero_of_notMem_tsupport hxnot]
      simp only [mul_zero, sub_zero]

private theorem cutoff_error_indicator_bound
    {d : ℕ} {Ω K : Set (PDE.Vec d)}
    (g : PDE.Vec d → ℝ) (χ : C(PDE.Vec d, ℝ))
    (hg : AEStronglyMeasurable g (PDE.volumeOn Ω))
    {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) (hC0 : 0 ≤ C)
    (hχrange : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (hset : MeasurableSet ((Ω ∩ tsupport g) \ K)) :
    eLpNorm (((Ω ∩ tsupport g) \ K).indicator
      (g - (fun x ↦ χ x * g x))) (2 : ℝ≥0∞) (PDE.volumeOn Ω) ≤
      ENNReal.ofReal C * (PDE.volumeOn Ω) ((Ω ∩ tsupport g) \ K) ^
        (1 / (2 : ℝ≥0∞).toReal) := by
  apply eLpNorm_indicator_sub_le_of_dist_bdd (PDE.volumeOn Ω) ENNReal.coe_ne_top
    hset.nullMeasurableSet hC0
    ((hg.sub (χ.continuous.aestronglyMeasurable.mul hg)).indicator hset)
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

private theorem cutoff_error_lt_of_core
    {d : ℕ} {Ω K : Set (PDE.Vec d)}
    (g : PDE.Vec d → ℝ) (χ : C(PDE.Vec d, ℝ))
    {C r ε : ℝ} (hC0 : 0 ≤ C) (hCpos : 0 < C) (hr : 0 < r) (hε : 0 < ε)
    (hmeasure : (PDE.volumeOn Ω) ((Ω ∩ tsupport g) \ K) < ENNReal.ofReal (r ^ 2))
    (herror : g - (fun x ↦ χ x * g x) =ᵐ[PDE.volumeOn Ω]
      ((Ω ∩ tsupport g) \ K).indicator (g - (fun x ↦ χ x * g x)))
    (hindicator : eLpNorm (((Ω ∩ tsupport g) \ K).indicator
      (g - (fun x ↦ χ x * g x))) (2 : ℝ≥0∞) (PDE.volumeOn Ω) ≤
      ENNReal.ofReal C * (PDE.volumeOn Ω) ((Ω ∩ tsupport g) \ K) ^
        (1 / (2 : ℝ≥0∞).toReal))
    (hr_def : r = ε / (C + 1)) :
    eLpNorm (g - (fun x ↦ χ x * g x)) (2 : ℝ≥0∞) (PDE.volumeOn Ω) <
      ENNReal.ofReal ε := by
  calc
    eLpNorm (g - (fun x ↦ χ x * g x)) (2 : ℝ≥0∞) (PDE.volumeOn Ω) =
        eLpNorm (((Ω ∩ tsupport g) \ K).indicator
          (g - (fun x ↦ χ x * g x))) (2 : ℝ≥0∞) (PDE.volumeOn Ω) :=
      eLpNorm_congr_ae herror
    _ ≤ ENNReal.ofReal C * (PDE.volumeOn Ω) ((Ω ∩ tsupport g) \ K) ^
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

private theorem cutoff_continuous
    {d : ℕ} (g : PDE.Vec d → ℝ) (χ : C(PDE.Vec d, ℝ)) (hgCont : Continuous g) :
    Continuous (fun x ↦ χ x * g x) :=
  χ.continuous.mul hgCont

private theorem cutoff_hasCompactSupport
    {d : ℕ} (g : PDE.Vec d → ℝ) (χ : C(PDE.Vec d, ℝ))
    (hχcompact : IsCompact (tsupport χ)) :
    HasCompactSupport (fun x ↦ χ x * g x) := by
  exact hχcompact.of_isClosed_subset (isClosed_tsupport _)
    tsupport_mul_subset_left

private theorem cutoff_tsupport_subset
    {d : ℕ} {Ω : Set (PDE.Vec d)} (g : PDE.Vec d → ℝ) (χ : C(PDE.Vec d, ℝ))
    (hχsupport : tsupport χ ⊆ Ω) :
    tsupport (fun x ↦ χ x * g x) ⊆ Ω :=
  tsupport_mul_subset_left.trans hχsupport

private theorem cutoff_bundle
    {d : ℕ} {Ω : Set (PDE.Vec d)} (g : PDE.Vec d → ℝ) (χ : C(PDE.Vec d, ℝ))
    (hgCont : Continuous g) (hχcompact : IsCompact (tsupport χ))
    (hχsupport : tsupport χ ⊆ Ω) {ε : ℝ}
    (hcutoff : eLpNorm (g - (fun x ↦ χ x * g x)) (2 : ℝ≥0∞) (PDE.volumeOn Ω) <
      ENNReal.ofReal ε) :
    ∃ h : PDE.Vec d → ℝ,
      Continuous h ∧ HasCompactSupport h ∧ tsupport h ⊆ Ω ∧
      eLpNorm (g - h) (2 : ℝ≥0∞) (PDE.volumeOn Ω) < ENNReal.ofReal ε := by
  let h : PDE.Vec d → ℝ := fun x ↦ χ x * g x
  have hhcont : Continuous h := cutoff_continuous g χ hgCont
  have hhcompact : HasCompactSupport h := cutoff_hasCompactSupport g χ hχcompact
  have hhsupport : tsupport h ⊆ Ω := cutoff_tsupport_subset g χ hχsupport
  exact Exists.intro h ⟨hhcont, hhcompact, hhsupport, hcutoff⟩

private theorem compactCore_cutoff_eLpNorm_sub_lt
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    {g : PDE.Vec d → ℝ} (hgSmooth : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgCompact : HasCompactSupport g) {ε : ℝ} (hε : 0 < ε) :
    ∃ h : PDE.Vec d → ℝ,
      Continuous h ∧ HasCompactSupport h ∧ tsupport h ⊆ Ω ∧
      eLpNorm (g - h) (2 : ℝ≥0∞) (PDE.volumeOn Ω) < ENNReal.ofReal ε := by
  let μ : Measure (PDE.Vec d) := PDE.volumeOn Ω
  have hmeas : MeasurableSet (Ω ∩ tsupport g) :=
    hΩ.measurableSet.inter (isClosed_tsupport g).measurableSet
  have hfinite : μ (Ω ∩ tsupport g) ≠ ∞ := by
    exact (measure_mono Set.inter_subset_right).trans_lt
      hgCompact.isCompact.measure_lt_top |>.ne
  rcases hgSmooth.continuous.bounded_above_of_compact_support hgCompact with ⟨C, hC⟩
  have hC0 : 0 ≤ C := (norm_nonneg (g 0)).trans (hC 0)
  by_cases hCzero : C = 0
  · have hgzero : g = 0 := by
      funext x
      apply norm_eq_zero.mp
      exact le_antisymm (by simpa [hCzero] using hC x) (norm_nonneg _)
    have hzero : eLpNorm (g - 0) (2 : ℝ≥0∞) (PDE.volumeOn Ω) < ENNReal.ofReal ε := by
      simpa [hgzero] using ENNReal.ofReal_pos.2 hε
    exact ⟨0, continuous_zero, HasCompactSupport.zero, by simp, hzero⟩
  have hCpos : 0 < C := lt_of_le_of_ne hC0 (Ne.symm hCzero)
  let r : ℝ := ε / (C + 1)
  have hr : 0 < r := by
    dsimp [r]
    positivity
  rcases hmeas.exists_isCompact_diff_lt hfinite
    (ENNReal.ofReal_pos.2 (sq_pos_of_pos hr)).ne' with ⟨K, hKA, hKCompact, hKmeasure⟩
  rcases exists_continuousMap_one_of_isCompact_subset_isOpen hKCompact hΩ
    (hKA.trans Set.inter_subset_left) with ⟨χ, hχone, hχcompact, hχsupport, hχrange⟩
  have herror := cutoff_error_ae hΩ g χ hχone
  have hindicator := cutoff_error_indicator_bound g χ hgSmooth.continuous.aestronglyMeasurable
    hC hC0 hχrange
    (hmeas.diff hKCompact.isClosed.measurableSet)
  have hcutoff : eLpNorm (g - (fun x ↦ χ x * g x)) (2 : ℝ≥0∞) (PDE.volumeOn Ω) <
      ENNReal.ofReal ε := by
    simpa only [μ] using
      cutoff_error_lt_of_core g χ hC0 hCpos hr hε hKmeasure herror hindicator rfl
  exact cutoff_bundle g χ hgSmooth.continuous hχcompact hχsupport hcutoff

private theorem lp_dist_toLp_toLp_le
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

private theorem exists_weakTestFunction_toScalarLp_dist_lt
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (u : PDE.ScalarLp Ω (2 : ℝ≥0∞)) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : PDE.WeakTestFunction Ω,
      dist u (φ.toScalarLp (2 : ℝ≥0∞)) < ε := by
  let μ : Measure (PDE.Vec d) := PDE.volumeOn Ω
  have hquarter : 0 < ε / 4 := by positivity
  obtain ⟨g, hgCompact, hgSmooth, hug⟩ :=
    (Lp.memLp u).exist_eLpNorm_sub_le ENNReal.coe_ne_top (by norm_num) hquarter
  obtain ⟨h, hhCont, hhCompact, hhSupport, hgh⟩ :=
    compactCore_cutoff_eLpNorm_sub_lt hΩ hgSmooth hgCompact hquarter
  obtain ⟨q, hqCompact, hqSmooth, hqSupport, hhq⟩ :=
    continuousCompact_contDiff_eLpNorm_sub_le_with_support
      (μ := PDE.volumeOn Ω) hhCompact hhCont hquarter
  have hqTsupport : tsupport q ⊆ Ω := by
    rw [tsupport]
    exact (closure_mono hqSupport).trans (show closure (Function.support h) ⊆ Ω from hhSupport)
  let φ : PDE.WeakTestFunction Ω :=
    { toFun := q
      contDiff := hqSmooth
      hasCompactSupport := hqCompact
      tsupport_subset := hqTsupport }
  let mg : MemLp g (2 : ℝ≥0∞) μ :=
    (hgSmooth.continuous.memLp_of_hasCompactSupport hgCompact).restrict Ω
  let mh : MemLp h (2 : ℝ≥0∞) μ :=
    (hhCont.memLp_of_hasCompactSupport hhCompact).restrict Ω
  let mq : MemLp q (2 : ℝ≥0∞) μ :=
    (hqSmooth.continuous.memLp_of_hasCompactSupport hqCompact).restrict Ω
  have hu_toLp : (Lp.memLp u).toLp (u : PDE.Vec d → ℝ) = u := by
    apply Lp.ext
    exact (Lp.memLp u).coeFn_toLp
  have hug' : dist u (mg.toLp g) ≤ ε / 4 := by
    rw [← hu_toLp]
    simpa only [μ] using lp_dist_toLp_toLp_le (Lp.memLp u) mg hquarter.le hug
  have hgh' : dist (mg.toLp g) (mh.toLp h) ≤ ε / 4 := by
    simpa only [μ] using lp_dist_toLp_toLp_le mg mh hquarter.le (le_of_lt hgh)
  have hhq' : dist (mh.toLp h) (mq.toLp q) ≤ ε / 4 := by
    simpa only [μ] using lp_dist_toLp_toLp_le mh mq hquarter.le hhq
  have hqφ : mq.toLp q = φ.toScalarLp (2 : ℝ≥0∞) := by
    apply Lp.ext
    filter_upwards [mq.coeFn_toLp, φ.coeFn_toScalarLp (2 : ℝ≥0∞)] with x hxq hxφ
    exact hxq.trans hxφ.symm
  refine ⟨φ, ?_⟩
  rw [← hqφ]
  calc
    dist u (mq.toLp q) ≤ dist u (mg.toLp g) + dist (mg.toLp g) (mq.toLp q) :=
      dist_triangle _ _ _
    _ ≤ dist u (mg.toLp g) +
        (dist (mg.toLp g) (mh.toLp h) + dist (mh.toLp h) (mq.toLp q)) := by
      gcongr
      exact dist_triangle _ _ _
    _ ≤ ε / 4 + (ε / 4 + ε / 4) := by gcongr
    _ < ε := by linarith

/-- Actual smooth compactly supported tests are dense in restricted-volume
`L²` on every open native-vector domain. -/
theorem weakTestFunction_toScalarLp_dense
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) :
    Dense (Set.range fun φ : PDE.WeakTestFunction Ω =>
      φ.toScalarLp (2 : ℝ≥0∞)) := by
  intro u
  refine (mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall).2 ?_
  intro ε hε
  rcases exists_weakTestFunction_toScalarLp_dist_lt hΩ u hε with ⟨φ, hφ⟩
  exact ⟨φ.toScalarLp (2 : ℝ≥0∞), ⟨φ, rfl⟩, by
    rw [Metric.mem_closedBall, dist_comm]
    exact hφ.le⟩

private theorem smoothTest_valueCLM_eq_toScalarLp
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (φ : PDE.WeakTestFunction Ω) :
    valueCLM hΩ
      (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ) =
        φ.toScalarLp (2 : ℝ≥0∞) := by
  change (PDE.smoothCompactlySupportedW1pGraph
    (p := (2 : ℝ≥0∞)) hΩ φ).1.1 = φ.toScalarLp (2 : ℝ≥0∞)
  apply Lp.ext
  filter_upwards [
    PDE.W1pFunction.coeFn_toW1pGraph_fst
      (PDE.W1pFunction.ofContDiff hΩ
        (φ.contDiff.of_le (by simp)) φ.hasCompactSupport (2 : ℝ≥0∞)),
    φ.coeFn_toScalarLp (2 : ℝ≥0∞)] with x hxGraph hxTest
  exact hxGraph.trans hxTest.symm

/-- The spatial `H¹₀` value map has dense range in restricted-volume `L²`. -/
theorem valueCLM_denseRange
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) :
    DenseRange (valueCLM hΩ) := by
  change Dense (Set.range (valueCLM hΩ))
  refine (weakTestFunction_toScalarLp_dense hΩ).mono ?_
  rintro y ⟨φ, rfl⟩
  exact ⟨smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ,
    smoothTest_valueCLM_eq_toScalarLp hΩ φ⟩

end HypoellipticAleksandrov.Parabolic.Dirichlet
