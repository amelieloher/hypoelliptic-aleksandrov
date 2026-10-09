module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimePositivePartContinuity

/-!
# Positive-part dual-pairing convergence

This module packages the finite-measure \(L^2\) convergence argument for the
positive-part map and its induced dual pairings.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open Filter Function MeasureTheory Set Topology
open scoped ENNReal RealInnerProductSpace

/-- The (L^2)-Cauchy--Schwarz bound in integral square-norm form. -/
theorem integral_mul_norm_le_sqrt_mul_sqrt
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {μ : Measure ℝ} (f : ℝ → E) (g : ℝ → F)
    (hf : MemLp f (2 : ℝ≥0∞) μ) (hg : MemLp g (2 : ℝ≥0∞) μ) :
    ∫ t, ‖f t‖ * ‖g t‖ ∂μ ≤
      √(∫ t, ‖f t‖ ^ 2 ∂μ) * √(∫ t, ‖g t‖ ^ 2 ∂μ) := by
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    Real.HolderConjugate.two_two
    (μ := μ) (f := fun t => ‖f t‖) (g := fun t => ‖g t‖)
    (Eventually.of_forall fun _ => norm_nonneg _)
    (Eventually.of_forall fun _ => norm_nonneg _)
    (by simpa only [ENNReal.ofReal_ofNat] using hf.norm)
    (by simpa only [ENNReal.ofReal_ofNat] using hg.norm)
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  simpa only [Real.rpow_two] using hholder

private noncomputable def dualPairingErrorIntegral
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (μ : Measure ℝ)
    (u : ℝ → H10HilbertGraph hΩ) (g : ℝ → H10HilbertGraphDual hΩ) : ℝ :=
  ∫ t, |(g t) (u t)| ∂μ

private noncomputable def dualPairingFirstBound
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (μ : Measure ℝ)
    (u : ℝ → H10HilbertGraph hΩ) (g : ℝ → H10HilbertGraphDual hΩ) : ℝ :=
  √(∫ t, ‖g t‖ ^ 2 ∂μ) * √(∫ t, ‖u t‖ ^ 2 ∂μ)

private noncomputable def dualPairingDifferenceIntegral
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (μ : Measure ℝ)
    (u uh : ℝ → H10HilbertGraph hΩ) (g gh : ℝ → H10HilbertGraphDual hΩ) : ℝ :=
  ∫ t, |(gh t) (uh t) - (g t) (u t)| ∂μ

private theorem dualPairing_first_integral_le
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (μ : Measure ℝ)
    (u : ℝ → H10HilbertGraph hΩ) (g : ℝ → H10HilbertGraphDual hΩ)
    (hu : MemLp u 2 μ) (hg : MemLp g 2 μ) :
    (∫ t, ‖g t‖ * ‖u t‖ ∂μ) ≤ dualPairingFirstBound hΩ μ u g := by
  exact integral_mul_norm_le_sqrt_mul_sqrt g u hg hu

private theorem dualPairing_pointwise_le
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (u uh : ℝ → H10HilbertGraph hΩ) (g gh : ℝ → H10HilbertGraphDual hΩ)
    (t : ℝ) :
    |(gh t) (uh t) - (g t) (u t)| ≤
      ‖gh t - g t‖ * ‖uh t‖ + ‖g t‖ * ‖uh t - u t‖ := by
  change ‖(gh t) (uh t) - (g t) (u t)‖ ≤ _
  calc
    _ = ‖(gh t - g t) (uh t) + (g t) (uh t - u t)‖ := by
      congr 1
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.map_sub]
      ring
    _ ≤ ‖(gh t - g t) (uh t)‖ + ‖(g t) (uh t - u t)‖ := norm_add_le _ _
    _ ≤ _ := add_le_add (ContinuousLinearMap.le_opNorm _ _)
      (ContinuousLinearMap.le_opNorm _ _)

private theorem integrable_dualPairing
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (μ : Measure ℝ)
    (u : ℝ → H10HilbertGraph hΩ) (g : ℝ → H10HilbertGraphDual hΩ)
    (hu : MemLp u 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun t => (g t) (u t)) μ := by
  let pairing : H10HilbertGraphDual hΩ →L[ℝ] H10HilbertGraph hΩ →L[ℝ] ℝ :=
    ContinuousLinearMap.flip (ContinuousLinearMap.apply ℝ ℝ)
  simpa only [pairing, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.apply_apply] using
    memLp_one_iff_integrable.mp (pairing.memLp_of_bilin 1 hg hu)

private noncomputable def dualPairingApproximationError
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (μ : Measure ℝ)
    (u : ℝ → H10HilbertGraph hΩ) (g : ℝ → H10HilbertGraphDual hΩ)
    (uh : ℝ → ℝ → H10HilbertGraph hΩ) (gh : ℝ → ℝ → H10HilbertGraphDual hΩ) :
    ℝ → ℝ :=
  fun h => ∫ t, |(gh h t) (uh h t) - (g t) (u t)| ∂μ

private noncomputable def sqNormApproximationError
    {E : Type*} [NormedAddCommGroup E] (μ : Measure ℝ)
    (f : ℝ → E) (fh : ℝ → ℝ → E) : ℝ → ℝ :=
  fun h => ∫ t, ‖fh h t - f t‖ ^ 2 ∂μ

private theorem integral_sqNorm_eq_toLp_norm_sq
    {E : Type*} [NormedAddCommGroup E] (μ : Measure ℝ)
    (z : ℝ → E) (hz : MemLp z 2 μ) :
    ∫ t, ‖z t‖ ^ 2 ∂μ = ‖hz.toLp z‖ ^ 2 := by
  rw [Lp.norm_def, eLpNorm_congr_ae hz.coeFn_toLp,
    hz.eLpNorm_eq_integral_rpow_norm (by norm_num) (by simp)]
  simp
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg
    (integral_nonneg fun _ => sq_nonneg _) _)]
  exact (Real.rpow_inv_natCast_pow
    (integral_nonneg fun _ => sq_nonneg _) (by norm_num)).symm

private theorem eventually_sqrt_sqNorm_le_of_tendsto
    {E : Type*} [NormedAddCommGroup E] (μ : Measure ℝ)
    (u : ℝ → E) (uh : ℝ → ℝ → E)
    (hu : MemLp u 2 μ) (huh : ∀ᶠ h : ℝ in 𝓝[>] 0, MemLp (uh h) 2 μ)
    (hU : Tendsto (sqNormApproximationError μ u uh) (𝓝[>] 0) (𝓝 0)) :
    ∃ C : ℝ, ∀ᶠ h : ℝ in 𝓝[>] 0,
      √(∫ t, ‖uh h t‖ ^ 2 ∂μ) ≤ C + √(∫ t, ‖u t‖ ^ 2 ∂μ) := by
  rcases hU.sqrt.isBoundedUnder_le.eventually_le with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  filter_upwards [huh, hC] with h hmh hbound
  have hd := hmh.sub hu
  let hy := hu
  let hxy := hd
  have hEq : hmh.toLp (uh h) = hxy.toLp (uh h - u) + hy.toLp u := by
    rw [show hxy.toLp (uh h - u) = hmh.toLp (uh h) - hy.toLp u by
      exact MemLp.toLp_sub hmh hu]
    abel
  have hsDiff : (∫ t, ‖uh h t - u t‖ ^ 2 ∂μ) = ‖hxy.toLp (uh h - u)‖ ^ 2 := by
    simpa only [Pi.sub_apply] using
      integral_sqNorm_eq_toLp_norm_sq μ (uh h - u) hxy
  have hboundNorm : ‖hxy.toLp (uh h - u)‖ ≤ C := by
    calc
      ‖hxy.toLp (uh h - u)‖ = √(‖hxy.toLp (uh h - u)‖ ^ 2) := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
      _ = √(∫ t, ‖uh h t - u t‖ ^ 2 ∂μ) := congrArg Real.sqrt hsDiff.symm
      _ ≤ C := hbound
  rw [integral_sqNorm_eq_toLp_norm_sq μ (uh h) hmh,
    integral_sqNorm_eq_toLp_norm_sq μ u hy, hEq]
  simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] using
    (norm_add_le (hxy.toLp (uh h - u)) (hy.toLp u)).trans
      (add_le_add hboundNorm le_rfl)


private theorem tendsto_dualPairing_of_sqNorm
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (μ : Measure ℝ)
    (u : ℝ → H10HilbertGraph hΩ) (g : ℝ → H10HilbertGraphDual hΩ)
    (uh : ℝ → ℝ → H10HilbertGraph hΩ) (gh : ℝ → ℝ → H10HilbertGraphDual hΩ)
    (hu : MemLp u 2 μ) (hg : MemLp g 2 μ)
    (huh : ∀ᶠ h : ℝ in 𝓝[>] 0, MemLp (uh h) 2 μ)
    (hgh : ∀ᶠ h : ℝ in 𝓝[>] 0, MemLp (gh h) 2 μ)
    (hU : Tendsto (sqNormApproximationError μ u uh) (𝓝[>] 0) (𝓝 0))
    (hG : Tendsto (sqNormApproximationError μ g gh) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (dualPairingApproximationError hΩ μ u g uh gh) (𝓝[>] 0) (𝓝 0) := by
  have hUs := hU.sqrt
  have hGs := hG.sqrt
  obtain ⟨C, huhBound⟩ := eventually_sqrt_sqNorm_le_of_tendsto μ u uh hu huh hU
  have hfirst : Tendsto (fun h => √(∫ t, ‖gh h t - g t‖ ^ 2 ∂μ) *
      √(∫ t, ‖uh h t‖ ^ 2 ∂μ)) (𝓝[>] 0) (𝓝 0) := by
    have hGs0 : Tendsto (fun h => √(∫ t, ‖gh h t - g t‖ ^ 2 ∂μ))
        (𝓝[>] 0) (𝓝 0) := by
      simpa only [Real.sqrt_zero, sqNormApproximationError, Pi.sub_def] using hGs
    apply hGs0.zero_mul_isBoundedUnder_le
    exact isBoundedUnder_of_eventually_le (huhBound.mono fun h hh => by
      simpa only [Function.comp_apply, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)] using hh)
  have hsecond : Tendsto (fun h => √(∫ t, ‖g t‖ ^ 2 ∂μ) *
      √(∫ t, ‖uh h t - u t‖ ^ 2 ∂μ)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.sqrt_zero, mul_zero, sqNormApproximationError, Pi.sub_def]
      using tendsto_const_nhds.mul hUs
  apply squeeze_zero'
  · filter_upwards with h
    exact integral_nonneg fun _ => abs_nonneg _
  · filter_upwards [huh, hgh] with h hmh hmg
    have hdU : MemLp (uh h - u) 2 μ := hmh.sub hu
    have hdG : MemLp (gh h - g) 2 μ := hmg.sub hg
    have hp1 := integrable_dualPairing hΩ μ (uh h) (gh h) hmh hmg
    have hp0 := integrable_dualPairing hΩ μ u g hu hg
    calc
      _ ≤ ∫ t, ‖gh h t - g t‖ * ‖uh h t‖ +
          ‖g t‖ * ‖uh h t - u t‖ ∂μ := by
        apply integral_mono
        · simpa only [Real.norm_eq_abs, Pi.sub_def] using (hp1.sub hp0).norm
        · exact (hdG.norm.integrable_mul hmh.norm).add
            (hg.norm.integrable_mul hdU.norm)
        · exact dualPairing_pointwise_le hΩ u (uh h) g (gh h)
      _ = (∫ t, ‖gh h t - g t‖ * ‖uh h t‖ ∂μ) +
          ∫ t, ‖g t‖ * ‖uh h t - u t‖ ∂μ := integral_add
            (hdG.norm.integrable_mul hmh.norm) (hg.norm.integrable_mul hdU.norm)
      _ ≤ _ := add_le_add
        (dualPairing_first_integral_le hΩ μ (uh h) (gh h - g) hmh hdG)
        (dualPairing_first_integral_le hΩ μ (uh h - u) g hdU hg)
  · simpa only [add_zero, dualPairingFirstBound, Pi.sub_def] using hfirst.add hsecond


private theorem localPositivePart_memLp
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (μ : Measure ℝ)
    (f : MeasureTheory.Lp (H10HilbertGraph hΩ) (2 : ℝ≥0∞) μ) :
    MemLp (fun t => h10PositivePart hΩ (f t)) (2 : ℝ≥0∞) μ := by
  apply MemLp.of_le (Lp.memLp f)
  · exact (continuous_h10PositivePart hΩ).comp_aestronglyMeasurable
      (Lp.memLp f).aestronglyMeasurable
  · filter_upwards with t
    exact norm_h10PositivePart_le hΩ (f t)

/-- Pointwise positive part preserves (L^2)-membership. -/
theorem memLp_positivePart
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (μ : Measure ℝ)
    (f : ℝ → H10HilbertGraph hΩ) (hf : MemLp f 2 μ) :
    MemLp (fun t => h10PositivePart hΩ (f t)) 2 μ := by
  apply MemLp.of_le hf
  · exact (continuous_h10PositivePart hΩ).comp_aestronglyMeasurable
      hf.aestronglyMeasurable
  · filter_upwards with t
    exact norm_h10PositivePart_le hΩ _

private noncomputable def localPositivePart
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (μ : Measure ℝ) :
    MeasureTheory.Lp (H10HilbertGraph hΩ) (2 : ℝ≥0∞) μ →
      MeasureTheory.Lp (H10HilbertGraph hΩ) (2 : ℝ≥0∞) μ :=
  fun f => (localPositivePart_memLp hΩ μ f).toLp
    (fun t => h10PositivePart hΩ (f t))

private theorem coeFn_localPositivePart
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (μ : Measure ℝ)
    (f : MeasureTheory.Lp (H10HilbertGraph hΩ) (2 : ℝ≥0∞) μ) :
    localPositivePart hΩ μ f =ᵐ[μ] fun t => h10PositivePart hΩ (f t) :=
  (localPositivePart_memLp hΩ μ f).coeFn_toLp

private theorem continuous_localPositivePart
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (μ : Measure ℝ)
    [IsFiniteMeasure μ] : Continuous (localPositivePart hΩ μ) := by
  rw [continuous_iff_seqContinuous]
  intro fn f hfn
  let F : ℕ → ℝ → H10HilbertGraph hΩ := fun n t => fn n t
  let G : ℕ → ℝ → H10HilbertGraph hΩ := fun n t => h10PositivePart hΩ (fn n t)
  let G₀ : ℝ → H10HilbertGraph hΩ := fun t => h10PositivePart hΩ (f t)
  have hFmem : ∀ n, MemLp (F n) (2 : ℝ≥0∞) μ := fun n => Lp.memLp (fn n)
  have hfmem : MemLp (fun t => f t) (2 : ℝ≥0∞) μ := Lp.memLp f
  have hFLp : Tendsto (fun n => eLpNorm (F n - fun t => f t) 2 μ)
      atTop (𝓝 0) := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' (fn) f).1 hfn
  have hFui : UnifIntegrable F (2 : ℝ≥0∞) μ :=
    unifIntegrable_of_tendsto_Lp (by norm_num) (by norm_num) hFmem hfmem hFLp
  have hGmem : ∀ n, MemLp (G n) (2 : ℝ≥0∞) μ := by
    intro n
    exact (memLp_congr_ae (coeFn_localPositivePart hΩ μ (fn n))).mp
      (Lp.memLp (localPositivePart hΩ μ (fn n)))
  have hGui : UnifIntegrable G (2 : ℝ≥0∞) μ := by
    apply hFui.ae_mono (fun n => (hGmem n).aestronglyMeasurable)
    intro n
    filter_upwards with t
    exact enorm_le_iff_norm_le.mpr (norm_h10PositivePart_le hΩ (fn n t))
  have hG₀mem : MemLp G₀ (2 : ℝ≥0∞) μ :=
    (memLp_congr_ae (coeFn_localPositivePart hΩ μ f)).mp
      (Lp.memLp (localPositivePart hΩ μ f))
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms, -, hae⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (hfn.comp hns)).exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  have hpoint : ∀ᵐ t ∂μ, Tendsto (fun n => G (ns (ms n)) t) atTop (𝓝 (G₀ t)) := by
    filter_upwards [hae] with t ht
    exact (continuous_h10PositivePart hΩ).continuousAt.tendsto.comp ht
  have hnorm : Tendsto (fun n => eLpNorm (G (ns (ms n)) - G₀) 2 μ)
      atTop (𝓝 0) := by
    apply tendsto_Lp_finite_of_tendsto_ae (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
    · exact fun n => (hGmem (ns (ms n))).aestronglyMeasurable
    · exact hG₀mem
    · exact hGui.comp (fun n => ns (ms n))
    · exact hpoint
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  refine hnorm.congr' ?_
  filter_upwards with n
  apply eLpNorm_congr_ae
  filter_upwards [coeFn_localPositivePart hΩ μ (fn (ns (ms n))),
    coeFn_localPositivePart hΩ μ f] with t hleft hright
  simp only [Pi.sub_apply, G, G₀]
  change _ = localPositivePart hΩ μ (fn (ns (ms n))) t - localPositivePart hΩ μ f t
  rw [hleft, hright]

private theorem tendsto_localToLp_of_sqNorm
    {E : Type*} [NormedAddCommGroup E]
    (μ : Measure ℝ) (f : ℝ → E) (fh : ℝ → ℝ → E)
    (hf : MemLp f (2 : ℝ≥0∞) μ)
    (hfh : ∀ᶠ h : ℝ in 𝓝[>] 0, MemLp (fh h) (2 : ℝ≥0∞) μ)
    (hconv : Tendsto (fun h : ℝ => ∫ t, ‖fh h t - f t‖ ^ 2 ∂μ)
      (𝓝[>] 0) (𝓝 0)) :
    ∃ FLp : ℝ → MeasureTheory.Lp E (2 : ℝ≥0∞) μ,
      Tendsto FLp (𝓝[>] 0) (𝓝 (hf.toLp f)) ∧
      ∀ᶠ h : ℝ in 𝓝[>] 0, FLp h =ᵐ[μ] fh h := by
  letI := Classical.propDecidable
  let FLp : ℝ → MeasureTheory.Lp E (2 : ℝ≥0∞) μ := fun h =>
    if hh : MemLp (fh h) (2 : ℝ≥0∞) μ then hh.toLp (fh h) else 0
  refine ⟨FLp, ?_, ?_⟩
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    have hroot : Tendsto (fun h : ℝ => √(∫ t, ‖fh h t - f t‖ ^ 2 ∂μ))
        (𝓝[>] 0) (𝓝 0) := by simpa only [Real.sqrt_zero] using hconv.sqrt
    refine hroot.congr' ?_
    filter_upwards [hfh] with h hh
    have hd := hh.sub hf
    have heq : FLp h - hf.toLp f = hd.toLp (fh h - f) := by
      apply Lp.ext
      filter_upwards [hh.coeFn_toLp, hf.coeFn_toLp, hd.coeFn_toLp,
        Lp.coeFn_sub (FLp h) (hf.toLp f)] with t h1 h2 h3 h4
      rw [h4, h3]
      simp only [FLp, dif_pos hh, Pi.sub_apply] at h1 h2 ⊢
      rw [h1, h2]
    rw [heq]
    rw [Lp.norm_def, eLpNorm_congr_ae hd.coeFn_toLp,
      hd.eLpNorm_eq_integral_rpow_norm (by norm_num) (by simp)]
    simp
    rw [ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun _ => sq_nonneg _) _)]
    rw [Real.sqrt_eq_rpow]
    congr 1
    norm_num
  · filter_upwards [hfh] with h hh
    simpa only [FLp, dif_pos hh] using hh.coeFn_toLp

/-- Strong \(L^2\) convergence is preserved by the pointwise positive-part map. -/
theorem tendsto_positivePart_sqNorm_integral_of_sqNorm
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (μ : Measure ℝ)
    [IsFiniteMeasure μ] (f : ℝ → H10HilbertGraph hΩ)
    (fh : ℝ → ℝ → H10HilbertGraph hΩ)
    (hf : MemLp f (2 : ℝ≥0∞) μ)
    (hfh : ∀ᶠ h : ℝ in 𝓝[>] 0, MemLp (fh h) (2 : ℝ≥0∞) μ)
    (hconv : Tendsto (fun h : ℝ => ∫ t, ‖fh h t - f t‖ ^ 2 ∂μ)
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun h : ℝ => ∫ t,
      ‖h10PositivePart hΩ (fh h t) - h10PositivePart hΩ (f t)‖ ^ 2 ∂μ)
      (𝓝[>] 0) (𝓝 0) := by
  let fLp := hf.toLp f
  obtain ⟨FLp, hFLp, hFLpAE⟩ := tendsto_localToLp_of_sqNorm μ f fh hf hfh hconv
  have hposLp := (continuous_localPositivePart hΩ μ).continuousAt.tendsto.comp hFLp
  rw [tendsto_iff_norm_sub_tendsto_zero] at hposLp
  have hsquare := hposLp.pow 2
  simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hsquare.congr' (by
    filter_upwards [hfh, hFLpAE] with h hh hfhAE
    let A := localPositivePart hΩ μ (FLp h) - localPositivePart hΩ μ fLp
    have hAmem : MemLp (A : ℝ → H10HilbertGraph hΩ) (2 : ℝ≥0∞) μ := Lp.memLp A
    have hsquare : (∫ t, ‖A t‖ ^ 2 ∂μ) = ‖A‖ ^ 2 := by
      rw [Lp.norm_def, hAmem.eLpNorm_eq_integral_rpow_norm (by norm_num) (by simp)]
      simp
      rw [ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun _ => sq_nonneg _) _)]
      exact (Real.rpow_inv_natCast_pow
        (integral_nonneg fun _ => sq_nonneg _) (by norm_num)).symm
    change ‖A‖ ^ 2 = _
    rw [← hsquare]
    apply integral_congr_ae
    filter_upwards [coeFn_localPositivePart hΩ μ (FLp h),
      coeFn_localPositivePart hΩ μ fLp, hfhAE, hf.coeFn_toLp,
      Lp.coeFn_sub (localPositivePart hΩ μ (FLp h))
        (localPositivePart hΩ μ fLp)] with t h1 h2 h3 h4 h5
    simp only [fLp] at h2
    simp only [A, h5, Pi.sub_apply]
    rw [h1, h2, h3, h4])


/-- Strong \(L^2\) convergence of primal and dual approximations implies
\(L^1\) convergence of their dual pairing after applying the positive-part map
to the primal approximation. -/
theorem tendsto_dualPairing_positivePart_of_sqNorm
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (μ : Measure ℝ)
    [IsFiniteMeasure μ]
    (u : ℝ → H10HilbertGraph hΩ) (g : ℝ → H10HilbertGraphDual hΩ)
    (uh : ℝ → ℝ → H10HilbertGraph hΩ) (gh : ℝ → ℝ → H10HilbertGraphDual hΩ)
    (hu : MemLp u 2 μ) (hg : MemLp g 2 μ)
    (huh : ∀ᶠ h : ℝ in 𝓝[>] 0, MemLp (uh h) 2 μ)
    (hgh : ∀ᶠ h : ℝ in 𝓝[>] 0, MemLp (gh h) 2 μ)
    (hU : Tendsto (fun h : ℝ => ∫ t, ‖uh h t - u t‖ ^ 2 ∂μ)
      (𝓝[>] 0) (𝓝 0))
    (hG : Tendsto (fun h : ℝ => ∫ t, ‖gh h t - g t‖ ^ 2 ∂μ)
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun h : ℝ => ∫ t,
      |(gh h t) (h10PositivePart hΩ (uh h t)) -
        (g t) (h10PositivePart hΩ (u t))| ∂μ) (𝓝[>] 0) (𝓝 0) := by
  have hUpos := tendsto_positivePart_sqNorm_integral_of_sqNorm hΩ μ u uh hu huh hU
  have huPos : MemLp (fun t => h10PositivePart hΩ (u t)) 2 μ := by
    apply MemLp.of_le hu
    · exact (continuous_h10PositivePart hΩ).comp_aestronglyMeasurable
        hu.aestronglyMeasurable
    · filter_upwards with t
      exact norm_h10PositivePart_le hΩ _
  have huhPos : ∀ᶠ h : ℝ in 𝓝[>] 0,
      MemLp (fun t => h10PositivePart hΩ (uh h t)) 2 μ := by
    filter_upwards [huh] with h hh
    apply MemLp.of_le hh
    · exact (continuous_h10PositivePart hΩ).comp_aestronglyMeasurable
        hh.aestronglyMeasurable
    · filter_upwards with t
      exact norm_h10PositivePart_le hΩ _
  exact tendsto_dualPairing_of_sqNorm hΩ μ
    (fun t => h10PositivePart hΩ (u t)) g
    (fun h t => h10PositivePart hΩ (uh h t)) gh
    huPos hg huhPos hgh hUpos hG

end HypoellipticAleksandrov.Parabolic.Dirichlet
