module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeShiftedPositivePart
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeBochnerContinuous
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeSteklovEndpoint
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ShiftedPositivePartEnergySupport
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimePositivePartPairingConvergence

/-!
# Continuity of affine-threshold shifted positive parts in reverse time

This module decomposes the finite-measure Vitali argument proving strong
continuity of the affine-threshold shifted positive-part operation on the
reverse-time Bochner `L²` space.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

variable {d : ℕ} {Ω : Set (PDE.Vec d)}

/-- Raw representatives of a sequence of affine-threshold shifted positive
parts. -/
def shiftedPositivePartSequence
    (hΩ : IsOpen Ω) (M N : ℝ≥0)
    (un : ℕ → ℝ → H10HilbertGraph hΩ) :
    ℕ → ℝ → H10HilbertGraph hΩ :=
  fun n τ => h10ShiftedPositivePart hΩ (un n τ)
    (reverseTimeAffineThreshold M N τ)

/-- The sharp spatial norm bound transfers uniform integrability to the
affine-threshold shifted positive parts. -/
theorem unifIntegrable_shiftedPositivePartSequence
    (hΩ : IsOpen Ω) (T : ℝ) (M N : ℝ≥0)
    (un : ℕ → ReverseTimeL2V hΩ T)
    (hunUI : UnifIntegrable (fun n τ => un n τ) (2 : ℝ≥0∞)
      (reverseTimeVolume T)) :
    UnifIntegrable
      (shiftedPositivePartSequence hΩ M N (fun n τ => un n τ))
      (2 : ℝ≥0∞) (reverseTimeVolume T) := by
  rw [unifIntegrable_iff']
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := unifIntegrable_iff'.mp hunUI ε hε
  refine ⟨δ, hδ, fun n s hs hμs => ?_⟩
  refine (eLpNorm_mono
    ((continuous_h10ShiftedPositivePart hΩ).comp_aestronglyMeasurable
      ((Lp.memLp (un n)).aestronglyMeasurable.prodMk
        (continuous_const.add (continuous_real_toNNReal.mul continuous_const)
          |>.aestronglyMeasurable))).restrict ?_).trans (hbound n s hs hμs)
  intro τ
  exact norm_h10ShiftedPositivePart_le hΩ (un n τ)
    (reverseTimeAffineThreshold M N τ)

/-- At a fixed reverse time, convergence of the spatial inputs implies
convergence of their shifted positive parts with the affine threshold held
fixed. -/
theorem tendsto_shiftedPositivePart_at_fixed_time
    (hΩ : IsOpen Ω) (M N : ℝ≥0)
    (un : ℕ → H10HilbertGraph hΩ)
    (u : H10HilbertGraph hΩ) (τ : ℝ)
    (hτ : Tendsto un atTop (𝓝 u)) :
    Tendsto
      (fun n => h10ShiftedPositivePart hΩ (un n)
        (reverseTimeAffineThreshold M N τ))
      atTop
      (𝓝 (h10ShiftedPositivePart hΩ u
        (reverseTimeAffineThreshold M N τ))) := by
  let k := reverseTimeAffineThreshold M N τ
  have hc : Continuous (fun v : H10HilbertGraph hΩ =>
      h10ShiftedPositivePart hΩ v k) :=
    (continuous_h10ShiftedPositivePart hΩ).comp
      (continuous_id.prodMk continuous_const)
  exact hc.continuousAt.tendsto.comp hτ

private theorem exists_subseq_tendsto_reverseTimeShiftedPositivePart
    (hΩ : IsOpen Ω) (T : ℝ) (M N : ℝ≥0)
    (un : ℕ → ReverseTimeL2V hΩ T) (u : ReverseTimeL2V hΩ T)
    (hun : Tendsto un atTop (𝓝 u))
    (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop) :
    ∃ ms : ℕ → ℕ, StrictMono ms ∧
      Tendsto
        (fun n => reverseTimeShiftedPositivePart hΩ T M N (un (ns (ms n))))
        atTop (𝓝 (reverseTimeShiftedPositivePart hΩ T M N u)) := by
  letI : IsFiniteMeasure (reverseTimeVolume T) := by
    change IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) T))
    infer_instance
  let f : ℕ → ℝ → H10HilbertGraph hΩ := fun n τ => un n τ
  let g : ℕ → ℝ → H10HilbertGraph hΩ :=
    shiftedPositivePartSequence hΩ M N f
  let g₀ : ℝ → H10HilbertGraph hΩ := fun τ =>
    h10ShiftedPositivePart hΩ (u τ) (reverseTimeAffineThreshold M N τ)
  have hfMem : ∀ n, MemLp (f n) (2 : ℝ≥0∞) (reverseTimeVolume T) :=
    fun n => Lp.memLp (un n)
  have huMem : MemLp (fun τ => u τ) (2 : ℝ≥0∞) (reverseTimeVolume T) :=
    Lp.memLp u
  have hfLp : Tendsto (fun n => eLpNorm (f n - fun τ => u τ) 2
      (reverseTimeVolume T)) atTop (𝓝 0) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm' un u).1 hun
  have hfUI : UnifIntegrable f (2 : ℝ≥0∞) (reverseTimeVolume T) :=
    unifIntegrable_of_tendsto_Lp (by norm_num) (by norm_num) hfMem huMem hfLp
  have hgUI : UnifIntegrable g (2 : ℝ≥0∞) (reverseTimeVolume T) := by
    exact unifIntegrable_shiftedPositivePartSequence hΩ T M N un hfUI
  have hgMem : ∀ n, MemLp (g n) (2 : ℝ≥0∞) (reverseTimeVolume T) := by
    intro n
    exact (memLp_congr_ae
      (coeFn_reverseTimeShiftedPositivePart hΩ T M N (un n))).mp
      (Lp.memLp (reverseTimeShiftedPositivePart hΩ T M N (un n)))
  have hg₀Mem : MemLp g₀ (2 : ℝ≥0∞) (reverseTimeVolume T) :=
    (memLp_congr_ae (coeFn_reverseTimeShiftedPositivePart hΩ T M N u)).mp
      (Lp.memLp (reverseTimeShiftedPositivePart hΩ T M N u))
  obtain ⟨ms, hms, hae⟩ :=
    (tendstoInMeasure_of_tendsto_Lp
      (hun.comp hns)).exists_seq_tendsto_ae
  refine ⟨ms, hms, ?_⟩
  have hpoint : ∀ᵐ τ ∂reverseTimeVolume T,
      Tendsto (fun n => g (ns (ms n)) τ) atTop (𝓝 (g₀ τ)) := by
    filter_upwards [hae] with τ hτ
    exact tendsto_shiftedPositivePart_at_fixed_time hΩ M N
      (fun n => un (ns (ms n)) τ) (u τ) τ hτ
  have hnorm : Tendsto (fun n => eLpNorm
      (g (ns (ms n)) - g₀) (2 : ℝ≥0∞) (reverseTimeVolume T))
      atTop (𝓝 0) := by
    apply tendsto_Lp_finite_of_tendsto_ae (p := (2 : ℝ≥0∞))
      (by norm_num) (by norm_num)
    · exact fun n => (hgMem (ns (ms n))).aestronglyMeasurable
    · exact hg₀Mem
    · rw [unifIntegrable_iff]
      intro ε hε
      obtain ⟨δ, hδ, hbound⟩ := unifIntegrable_iff.mp hgUI ε hε
      exact ⟨δ, hδ, fun n => hbound (ns (ms n))⟩
    · exact hpoint
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  refine hnorm.congr' ?_
  filter_upwards with n
  apply eLpNorm_congr_ae
  filter_upwards
      [coeFn_reverseTimeShiftedPositivePart hΩ T M N (un (ns (ms n))),
        coeFn_reverseTimeShiftedPositivePart hΩ T M N u] with τ hleft hright
  simp only [Pi.sub_apply, g, g₀, shiftedPositivePartSequence]
  change _ = (reverseTimeShiftedPositivePart hΩ T M N (un (ns (ms n)))) τ -
    (reverseTimeShiftedPositivePart hΩ T M N u) τ
  rw [hleft, hright]

/-- The affine-threshold shifted positive-part operation is strongly
continuous on reverse-time Bochner `L²(V)`. -/
theorem continuous_reverseTimeShiftedPositivePart
    (hΩ : IsOpen Ω) (T : ℝ) (M N : ℝ≥0) :
    Continuous (reverseTimeShiftedPositivePart hΩ T M N :
      ReverseTimeL2V hΩ T → ReverseTimeL2V hΩ T) := by
  rw [continuous_iff_seqContinuous]
  intro un u hun
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms, -, hconv⟩ :=
    exists_subseq_tendsto_reverseTimeShiftedPositivePart
      hΩ T M N un u hun ns hns
  exact ⟨ms, hconv⟩

/-- The forward Steklov average as a totalized reverse-time Bochner `L²`
class.  Nonpositive averaging widths are assigned the original class. -/
noncomputable def reverseTimeForwardSteklovL2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T h : ℝ) (f : MeasureTheory.Lp E (2 : ℝ≥0∞) (reverseTimeVolume T)) :
    MeasureTheory.Lp E (2 : ℝ≥0∞) (reverseTimeVolume T) :=
  if hh : 0 < h then
    reverseTimeL2OfContinuousOn T (reverseTimeForwardSteklov T h f)
      (continuous_reverseTimeForwardSteklov T h hh f).continuousOn
  else
    f

/-- At a positive averaging width, the lifted forward Steklov class is
represented almost everywhere by the pointwise average. -/
theorem coeFn_reverseTimeForwardSteklovL2_of_pos
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : ℝ) {h : ℝ} (hh : 0 < h)
    (f : MeasureTheory.Lp E (2 : ℝ≥0∞) (reverseTimeVolume T)) :
    reverseTimeForwardSteklovL2 T h f =ᵐ[reverseTimeVolume T]
      reverseTimeForwardSteklov T h f := by
  rw [reverseTimeForwardSteklovL2, dif_pos hh]
  exact coeFn_reverseTimeL2OfContinuousOn T _ _

/-- The totalized forward Steklov lift converges strongly to the original
reverse-time Bochner `L²` class as the averaging width tends to zero from the
right. -/
theorem tendsto_reverseTimeForwardSteklovL2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : ℝ) (hT : 0 < T)
    (f : MeasureTheory.Lp E (2 : ℝ≥0∞) (reverseTimeVolume T)) :
    Tendsto (fun h : ℝ => reverseTimeForwardSteklovL2 T h f)
      (nhdsWithin 0 (Ioi 0)) (nhds f) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsq := tendsto_forwardSteklov_sqNorm_integral_on_Icc_zero_T T hT f
  have hsqrt : Tendsto
      (fun h : ℝ => √(∫ t in Icc 0 T,
        ‖reverseTimeForwardSteklov T h f t - f t‖ ^ 2))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa only [Real.sqrt_zero, Function.comp_def] using
      (Continuous.tendsto Real.continuous_sqrt 0).comp hsq
  refine hsqrt.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hraw : MemLp (reverseTimeForwardSteklov T h f)
      (2 : ℝ≥0∞) (reverseTimeVolume T) :=
    memLp_two_reverseTime_of_continuousOn T _
      (continuous_reverseTimeForwardSteklov T h hh f).continuousOn
  let hsub := hraw.sub (Lp.memLp f)
  have htoLp : hsub.toLp
      (reverseTimeForwardSteklov T h f - fun t => f t) =
      reverseTimeForwardSteklovL2 T h f - f := by
    apply Lp.ext
    filter_upwards [hsub.coeFn_toLp,
        coeFn_reverseTimeForwardSteklovL2_of_pos T hh f,
        Lp.coeFn_sub (reverseTimeForwardSteklovL2 T h f) f]
      with t hsubt hlift hliftSub
    rw [hsubt]
    calc
      (reverseTimeForwardSteklov T h f - fun t => f t) t =
          reverseTimeForwardSteklovL2 T h f t - f t := by
        rw [Pi.sub_apply, hlift]
      _ = (reverseTimeForwardSteklovL2 T h f - f) t := hliftSub.symm
  have hint : (∫ t in Icc 0 T,
      ‖reverseTimeForwardSteklov T h f t - f t‖ ^ 2) =
      ‖hsub.toLp
        (reverseTimeForwardSteklov T h f - fun t => f t)‖ ^ 2 := by
    simpa only [reverseTimeVolume, reverseTimeOpenInterval,
      restrict_Ioo_eq_restrict_Icc, Pi.sub_apply] using
      integral_norm_sq_eq_norm_sq_toLp
        (reverseTimeForwardSteklov T h f - fun t => f t) hsub
  rw [← Real.sqrt_sq (norm_nonneg
    (reverseTimeForwardSteklovL2 T h f - f)), ← htoLp, ← hint]

private theorem tendsto_sqNorm_integral_restrict_of_Lp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {ι : Type*} {l : Filter ι}
    {T : ℝ} {f : MeasureTheory.Lp E 2 (reverseTimeVolume T)}
    {fh : ι → MeasureTheory.Lp E 2 (reverseTimeVolume T)}
    (hfh : Tendsto fh l (𝓝 f)) (s : Set ℝ)
    (hs : volume.restrict s ≤ reverseTimeVolume T) :
    Tendsto (fun h : ι => ∫ t in s, ‖fh h t - f t‖ ^ 2) l (𝓝 0) := by
  have hnorm : Tendsto (fun h : ι => ‖fh h - f‖ ^ 2) l (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      (tendsto_iff_norm_sub_tendsto_zero.mp hfh).pow 2
  apply squeeze_zero'
  · filter_upwards with h
    exact integral_nonneg fun _ => sq_nonneg _
  · filter_upwards with h
    have hm : MemLp (fun t => fh h t - f t) 2 (reverseTimeVolume T) :=
      (Lp.memLp (fh h)).sub (Lp.memLp f)
    calc
      (∫ t in s, ‖fh h t - f t‖ ^ 2) ≤
          ∫ t, ‖fh h t - f t‖ ^ 2 ∂reverseTimeVolume T := by
        apply integral_mono_measure
        · exact hs
        · exact Eventually.of_forall fun _ => sq_nonneg _
        · exact hm.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
      _ = ‖fh h - f‖ ^ 2 := by
        have hsub : (fun t => fh h t - f t) =ᵐ[reverseTimeVolume T]
            fun t => (fh h - f) t := by
          filter_upwards [Lp.coeFn_sub (fh h) f] with t ht
          exact ht.symm
        have htoLp : hm.toLp (fun t => fh h t - f t) = fh h - f := by
          apply Lp.ext
          filter_upwards [hm.coeFn_toLp, hsub] with t h1 h2
          rw [h1, h2]
        simpa only [Pi.sub_apply, htoLp] using
          integral_norm_sq_eq_norm_sq_toLp (fun t => fh h t - f t) hm
  · exact hnorm

private theorem shifted_abs_sq_sub_le_of_bounds
    {a b N delta y : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hN : 0 ≤ N)
    (hdelta : 0 ≤ delta) (hy : 0 ≤ y)
    (hdiff : |a - b| ≤ N * delta)
    (hsum : a + b ≤ N * delta + 2 * N * y) :
    |a ^ 2 - b ^ 2| ≤ N ^ 2 * delta ^ 2 + 2 * N ^ 2 * y * delta := by
  rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg ha hb)]
  calc
    (a + b) * |a - b| ≤ (N * delta + 2 * N * y) * (N * delta) :=
      mul_le_mul hsum hdiff (abs_nonneg _) (by positivity)
    _ = _ := by ring

private theorem shifted_abs_sqNorm_valueCLM_sub_le
    (hΩ : IsOpen Ω) (x y : H10HilbertGraph hΩ) :
    |‖valueCLM hΩ x‖ ^ 2 - ‖valueCLM hΩ y‖ ^ 2| ≤
      ‖valueCLM hΩ‖ ^ 2 * ‖x - y‖ ^ 2 +
        2 * ‖valueCLM hΩ‖ ^ 2 * ‖y‖ * ‖x - y‖ := by
  let L := valueCLM hΩ
  have hLx := L.le_opNorm x
  have hLy := L.le_opNorm y
  have hLsub := L.le_opNorm (x - y)
  have hx : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
    calc
      ‖x‖ = ‖(x - y) + y‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  have hdiff : |‖L x‖ - ‖L y‖| ≤ ‖L‖ * ‖x - y‖ := by
    calc
      _ ≤ ‖L x - L y‖ := abs_norm_sub_norm_le _ _
      _ = ‖L (x - y)‖ := by rw [L.map_sub]
      _ ≤ _ := hLsub
  have hsum : ‖L x‖ + ‖L y‖ ≤ ‖L‖ * ‖x - y‖ + 2 * ‖L‖ * ‖y‖ := by
    calc
      _ ≤ ‖L‖ * (‖x - y‖ + ‖y‖) + ‖L‖ * ‖y‖ :=
        add_le_add (hLx.trans (mul_le_mul_of_nonneg_left hx (norm_nonneg _))) hLy
      _ = _ := by ring
  exact shifted_abs_sq_sub_le_of_bounds (norm_nonneg _) (norm_nonneg _)
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hdiff hsum

private theorem tendsto_integral_mul_of_tendsto_integral_abs
    {ι : Type*} {l : Filter ι} {μ : Measure ℝ} {F : ι → ℝ → ℝ}
    {f phi : ℝ → ℝ}
    (hF : ∀ᶠ h : ι in l, Integrable (F h) μ)
    (hf : Integrable f μ) (hphi : AEStronglyMeasurable phi μ)
    (hbound : ∃ C : ℝ, ∀ t : ℝ, ‖phi t‖ ≤ C)
    (hlim : Tendsto (fun h : ι => ∫ t, |F h t - f t| ∂μ) l (𝓝 0)) :
    Tendsto (fun h : ι => ∫ t, F h t * phi t ∂μ) l
      (𝓝 (∫ t, f t * phi t ∂μ)) := by
  obtain ⟨C, hC⟩ := hbound
  have hCnorm : ∀ t : ℝ, ‖‖phi t‖‖ ≤ C := by
    intro t
    simpa only [norm_norm] using hC t
  have hC0 : 0 ≤ C := (norm_nonneg (phi 0)).trans (hC 0)
  have herr : Tendsto (fun h : ι => ∫ t, (F h t - f t) * phi t ∂μ)
      l (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero'
    · exact Eventually.of_forall fun _ => norm_nonneg _
    · filter_upwards [hF] with h hFh
      have hd : Integrable (fun t => F h t - f t) μ := hFh.sub hf
      have hprod : Integrable (fun t => |F h t - f t| * ‖phi t‖) μ :=
        hd.norm.mul_bdd hphi.norm (Eventually.of_forall fun t => hCnorm t)
      calc
        ‖∫ t, (F h t - f t) * phi t ∂μ‖ ≤
            ∫ t, ‖(F h t - f t) * phi t‖ ∂μ :=
          norm_integral_le_integral_norm _
        _ ≤ ∫ t, C * |F h t - f t| ∂μ := by
          apply integral_mono
          · simpa only [norm_mul, Real.norm_eq_abs] using hprod
          · exact hd.norm.const_mul C
          · intro t
            simp only [norm_mul, Real.norm_eq_abs]
            calc
              |F h t - f t| * ‖phi t‖ ≤ |F h t - f t| * C :=
                mul_le_mul_of_nonneg_left (hC t) (abs_nonneg _)
              _ = C * |F h t - f t| := mul_comm _ _
        _ = C * (∫ t, |F h t - f t| ∂μ) := integral_const_mul _ _
    · simpa only [mul_zero] using tendsto_const_nhds.mul hlim
  have := herr.add (tendsto_const_nhds : Tendsto (fun _ : ι =>
      ∫ t, f t * phi t ∂μ) l _)
  simpa only [zero_add] using this.congr' (by
    filter_upwards [hF] with h hFh
    have hd : Integrable (fun t => F h t - f t) μ := hFh.sub hf
    have hp := hd.mul_bdd hphi (Eventually.of_forall hC)
    have hr := hf.mul_bdd hphi (Eventually.of_forall hC)
    rw [← integral_add hp hr]
    apply integral_congr_ae
    filter_upwards with t
    ring)

/-- Strong reverse-time `L²` convergence gives local convergence of the
square of the spatial `L²` value norm. -/
theorem tendsto_integral_abs_valueCLM_sq_of_tendsto
    (hΩ : IsOpen Ω) {T a b : ℝ}
    (u : ReverseTimeL2V hΩ T) (un : ℕ → ReverseTimeL2V hΩ T)
    (hun : Tendsto un atTop (𝓝 u))
    (hμ : volume.restrict (Icc a b) ≤ reverseTimeVolume T) :
    Tendsto (fun n => ∫ t in Icc a b,
      |‖valueCLM hΩ (un n t)‖ ^ 2 - ‖valueCLM hΩ (u t)‖ ^ 2|)
      atTop (𝓝 0) := by
  let μ : Measure ℝ := volume.restrict (Icc a b)
  let L : H10HilbertGraph hΩ →L[ℝ]
      MeasureTheory.Lp ℝ 2 (PDE.volumeOn Ω) := valueCLM hΩ
  have hu : MemLp (u : ℝ → H10HilbertGraph hΩ) 2 μ :=
    (Lp.memLp u).mono_measure hμ
  have hunMem : ∀ n, MemLp (un n : ℝ → H10HilbertGraph hΩ) 2 μ :=
    fun n => (Lp.memLp (un n)).mono_measure hμ
  have hsq : Tendsto (fun n => ∫ t, ‖un n t - u t‖ ^ 2 ∂μ)
      atTop (𝓝 0) := by
    exact tendsto_sqNorm_integral_restrict_of_Lp hun (Icc a b) hμ
  let C : ℝ := ‖L‖ ^ 2
  have hsqrt : Tendsto (fun n => √(∫ t, ‖un n t - u t‖ ^ 2 ∂μ))
      atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero, Function.comp_def] using hsq.sqrt
  have hbound : ∀ n,
      (∫ t, |‖L (un n t)‖ ^ 2 - ‖L (u t)‖ ^ 2| ∂μ) ≤
        C * (∫ t, ‖un n t - u t‖ ^ 2 ∂μ) +
        2 * C * √(∫ t, ‖u t‖ ^ 2 ∂μ) *
          √(∫ t, ‖un n t - u t‖ ^ 2 ∂μ) := by
    intro n
    have hdu := (hunMem n).sub hu
    have hLun := (hunMem n).continuousLinearMap_comp L
    have hLu := hu.continuousLinearMap_comp L
    have hleft : Integrable (fun t =>
        |‖L (un n t)‖ ^ 2 - ‖L (u t)‖ ^ 2|) μ := by
      simpa only [Real.norm_eq_abs, Pi.sub_def] using
        ((hLun.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).sub
          (hLu.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))).norm
    have hterm1 : Integrable (fun t => C * ‖un n t - u t‖ ^ 2) μ :=
      (hdu.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).const_mul _
    have hterm2 : Integrable (fun t =>
        2 * C * ‖u t‖ * ‖un n t - u t‖) μ := by
      apply ((hu.norm).integrable_mul hdu.norm).const_mul (2 * C) |>.congr
      filter_upwards with t
      change 2 * C * (((fun x => ‖u x‖) * fun x => ‖un n x - u x‖) t) = _
      simp only [Pi.mul_apply]
      ring
    have hp : ∀ t,
        |‖L (un n t)‖ ^ 2 - ‖L (u t)‖ ^ 2| ≤
          C * ‖un n t - u t‖ ^ 2 + 2 * C * ‖u t‖ * ‖un n t - u t‖ := by
      intro t
      simpa only [L, C] using
        shifted_abs_sqNorm_valueCLM_sub_le hΩ (un n t) (u t)
    calc
      _ ≤ ∫ t, C * ‖un n t - u t‖ ^ 2 +
          2 * C * ‖u t‖ * ‖un n t - u t‖ ∂μ :=
        integral_mono hleft (hterm1.add hterm2) hp
      _ = C * (∫ t, ‖un n t - u t‖ ^ 2 ∂μ) +
          2 * C * (∫ t, ‖u t‖ * ‖un n t - u t‖ ∂μ) := by
        rw [integral_add hterm1 hterm2, integral_const_mul]
        rw [show (fun t => 2 * C * ‖u t‖ * ‖un n t - u t‖) =
          fun t => (2 * C) * (‖u t‖ * ‖un n t - u t‖) by funext t; ring,
          integral_const_mul]
      _ ≤ _ := by
        apply add_le_add_right
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
          (integral_mul_norm_le_sqrt_mul_sqrt u (fun t => un n t - u t) hu hdu)
          (by positivity : 0 ≤ 2 * C)
  apply squeeze_zero'
  · exact Eventually.of_forall fun _ => integral_nonneg fun _ => abs_nonneg _
  · exact Eventually.of_forall hbound
  · have hfirst : Tendsto (fun n =>
        C * (∫ t, ‖un n t - u t‖ ^ 2 ∂μ)) atTop (𝓝 0) := by
      simpa only [mul_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => C) atTop (𝓝 C)).mul hsq
    have hsecond := (tendsto_const_nhds : Tendsto (fun _ : ℕ =>
        2 * C * √(∫ t, ‖u t‖ ^ 2 ∂μ)) atTop _).mul hsqrt
    simpa only [mul_zero, add_zero] using hfirst.add hsecond

/-- A bounded scalar functional sends strong reverse-time `L²` convergence to
local `L¹` convergence. -/
theorem tendsto_integral_abs_continuousLinearMap_of_tendsto
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {T a b : ℝ} (Q : E →L[ℝ] ℝ)
    (u : MeasureTheory.Lp E 2 (reverseTimeVolume T))
    (un : ℕ → MeasureTheory.Lp E 2 (reverseTimeVolume T))
    (hun : Tendsto un atTop (𝓝 u))
    (hμ : volume.restrict (Icc a b) ≤ reverseTimeVolume T) :
    Tendsto (fun n => ∫ t in Icc a b, |Q (un n t) - Q (u t)|)
      atTop (𝓝 0) := by
  let μ := volume.restrict (Icc a b)
  have hsq := tendsto_sqNorm_integral_restrict_of_Lp hun (Icc a b) hμ
  have hsqrt : Tendsto (fun n => √(∫ t, ‖un n t - u t‖ ^ 2 ∂μ))
      atTop (𝓝 0) := by simpa only [Real.sqrt_zero, Function.comp_def] using hsq.sqrt
  apply squeeze_zero'
  · exact Eventually.of_forall fun _ => integral_nonneg fun _ => abs_nonneg _
  · filter_upwards with n
    have hd : MemLp (fun t => un n t - u t) 2 μ :=
      ((Lp.memLp (un n)).mono_measure hμ).sub ((Lp.memLp u).mono_measure hμ)
    calc
      (∫ t, |Q (un n t) - Q (u t)| ∂μ) =
          ∫ t, ‖Q (un n t - u t)‖ ∂μ := by
        apply integral_congr_ae
        filter_upwards with t
        rw [map_sub]
        rfl
      _ ≤ ‖Q‖ * ∫ t, ‖un n t - u t‖ ∂μ := by
        rw [← integral_const_mul]
        apply integral_mono
        · exact (hd.continuousLinearMap_comp Q).integrable (by norm_num) |>.norm
        · exact hd.integrable (by norm_num) |>.norm.const_mul _
        · intro t
          exact Q.le_opNorm _
      _ ≤ ‖Q‖ * √(∫ _t : ℝ, ‖(1 : ℝ)‖ ^ 2 ∂μ) *
          √(∫ t, ‖un n t - u t‖ ^ 2 ∂μ) := by
        have hh := integral_mul_norm_le_sqrt_mul_sqrt
          (fun _ : ℝ => (1 : ℝ)) (fun t => un n t - u t)
          (memLp_const (μ := μ) (p := (2 : ℝ≥0∞)) (1 : ℝ)) hd
        have hh' : (∫ t, ‖un n t - u t‖ ∂μ) ≤
            √(∫ _t : ℝ, ‖(1 : ℝ)‖ ^ 2 ∂μ) *
              √(∫ t, ‖un n t - u t‖ ^ 2 ∂μ) := by
          simpa only [norm_one, one_mul] using hh
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_left hh' (norm_nonneg Q)
  · simpa only [mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ =>
        ‖Q‖ * √(∫ _t : ℝ, ‖(1 : ℝ)‖ ^ 2 ∂μ)) atTop _).mul hsqrt

/-- The spatial-mass specialization of the bounded-functional adapter. -/
theorem tendsto_integral_abs_spatialMass_value_of_tendsto
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω) {T a b : ℝ}
    (u : ReverseTimeL2V hΩ T) (un : ℕ → ReverseTimeL2V hΩ T)
    (hun : Tendsto un atTop (𝓝 u))
    (hμ : volume.restrict (Icc a b) ≤ reverseTimeVolume T) :
    Tendsto (fun n => ∫ t in Icc a b,
      |((spatialMassCLM hΩbounded).comp (valueCLM hΩ)) (un n t) -
        ((spatialMassCLM hΩbounded).comp (valueCLM hΩ)) (u t)|)
      atTop (𝓝 0) :=
  tendsto_integral_abs_continuousLinearMap_of_tendsto
    ((spatialMassCLM hΩbounded).comp (valueCLM hΩ)) u un hun hμ

private theorem shifted_dualPairing_pointwise_le
    (hΩ : IsOpen Ω) (u uh : H10HilbertGraph hΩ)
    (g gh : H10HilbertGraphDual hΩ) :
    |gh uh - g u| ≤ ‖gh - g‖ * ‖uh‖ + ‖g‖ * ‖uh - u‖ := by
  change ‖gh uh - g u‖ ≤ _
  calc
    _ = ‖(gh - g) uh + g (uh - u)‖ := by
      congr 1
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.map_sub]
      ring
    _ ≤ ‖(gh - g) uh‖ + ‖g (uh - u)‖ := norm_add_le _ _
    _ ≤ _ := add_le_add (ContinuousLinearMap.le_opNorm _ _)
      (ContinuousLinearMap.le_opNorm _ _)

private theorem shifted_integrable_dualPairing
    (hΩ : IsOpen Ω) {μ : Measure ℝ}
    (u : ℝ → H10HilbertGraph hΩ) (g : ℝ → H10HilbertGraphDual hΩ)
    (hu : MemLp u 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun t => (g t) (u t)) μ := by
  let pairing : H10HilbertGraphDual hΩ →L[ℝ] H10HilbertGraph hΩ →L[ℝ] ℝ :=
    ContinuousLinearMap.flip (ContinuousLinearMap.apply ℝ ℝ)
  simpa only [pairing, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.apply_apply] using
    memLp_one_iff_integrable.mp (pairing.memLp_of_bilin 1 hg hu)

private theorem shifted_dualPairing_integral_le
    (hΩ : IsOpen Ω) {μ : Measure ℝ}
    (u uh : ℝ → H10HilbertGraph hΩ)
    (g gh : ℝ → H10HilbertGraphDual hΩ)
    (hu : MemLp u 2 μ) (huh : MemLp uh 2 μ)
    (hg : MemLp g 2 μ) (hgh : MemLp gh 2 μ) :
    (∫ t, |(gh t) (uh t) - (g t) (u t)| ∂μ) ≤
      √(∫ t, ‖gh t - g t‖ ^ 2 ∂μ) * √(∫ t, ‖uh t‖ ^ 2 ∂μ) +
      √(∫ t, ‖g t‖ ^ 2 ∂μ) * √(∫ t, ‖uh t - u t‖ ^ 2 ∂μ) := by
  have hdU := huh.sub hu
  have hdG := hgh.sub hg
  have hp1 := shifted_integrable_dualPairing hΩ uh gh huh hgh
  have hp0 := shifted_integrable_dualPairing hΩ u g hu hg
  calc
    _ ≤ ∫ t, ‖gh t - g t‖ * ‖uh t‖ + ‖g t‖ * ‖uh t - u t‖ ∂μ := by
      apply integral_mono
      · simpa only [Real.norm_eq_abs, Pi.sub_def] using (hp1.sub hp0).norm
      · exact (hdG.norm.integrable_mul huh.norm).add
          (hg.norm.integrable_mul hdU.norm)
      · exact fun t => shifted_dualPairing_pointwise_le hΩ _ _ _ _
    _ = (∫ t, ‖gh t - g t‖ * ‖uh t‖ ∂μ) +
        ∫ t, ‖g t‖ * ‖uh t - u t‖ ∂μ :=
      integral_add (hdG.norm.integrable_mul huh.norm)
        (hg.norm.integrable_mul hdU.norm)
    _ ≤ _ := add_le_add
      (integral_mul_norm_le_sqrt_mul_sqrt _ _ hdG huh)
      (integral_mul_norm_le_sqrt_mul_sqrt _ _ hg hdU)

private theorem integral_abs_sub_mul_sub_le
    {μ : Measure ℝ} (A B X Y : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hA : Integrable A μ) (hB : Integrable B μ)
    (hX : Integrable X μ) (hY : Integrable Y μ) :
    (∫ t, |A t - c * X t - (B t - c * Y t)| ∂μ) ≤
      (∫ t, |A t - B t| ∂μ) + c * (∫ t, |X t - Y t| ∂μ) := by
  have hAB := (hA.sub hB).norm
  have hXY := (hX.sub hY).norm
  have hAB' : Integrable (fun t => |A t - B t|) μ := by
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using hAB
  have hXY' : Integrable (fun t => |X t - Y t|) μ := by
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using hXY
  calc
    _ ≤ ∫ t, |A t - B t| + c * |X t - Y t| ∂μ := by
      apply integral_mono
      · exact ((hA.sub (hX.const_mul c)).sub
          (hB.sub (hY.const_mul c))).norm
      · exact hAB'.add (hXY'.const_mul c)
      · intro t
        calc
          |A t - c * X t - (B t - c * Y t)| =
              |(A t - B t) - c * (X t - Y t)| := by
            congr 1
            ring
          _ ≤ |A t - B t| + |c * (X t - Y t)| := abs_sub _ _
          _ = _ := by rw [abs_mul, abs_of_nonneg hc]
    _ = _ := by
      rw [integral_add hAB' (hXY'.const_mul c), integral_const_mul]

/-- Strong convergence in the primal and dual reverse-time `L²` spaces gives
local `L¹` convergence of their pointwise dual pairing. -/
theorem tendsto_integral_abs_dualPairing_of_tendsto
    (hΩ : IsOpen Ω) {T a b : ℝ}
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (un : ℕ → ReverseTimeL2V hΩ T)
    (gn : ℕ → ReverseTimeL2VStar hΩ T)
    (hun : Tendsto un atTop (𝓝 u)) (hgn : Tendsto gn atTop (𝓝 g))
    (hμ : volume.restrict (Icc a b) ≤ reverseTimeVolume T) :
    Tendsto (fun n => ∫ t in Icc a b,
      |(gn n t) (un n t) - (g t) (u t)|) atTop (𝓝 0) := by
  let μ := volume.restrict (Icc a b)
  have hu : MemLp (u : ℝ → H10HilbertGraph hΩ) 2 μ :=
    (Lp.memLp u).mono_measure hμ
  have hg : MemLp (g : ℝ → H10HilbertGraphDual hΩ) 2 μ :=
    (Lp.memLp g).mono_measure hμ
  have hunm : ∀ n, MemLp (un n : ℝ → H10HilbertGraph hΩ) 2 μ :=
    fun n => (Lp.memLp (un n)).mono_measure hμ
  have hgnm : ∀ n, MemLp (gn n : ℝ → H10HilbertGraphDual hΩ) 2 μ :=
    fun n => (Lp.memLp (gn n)).mono_measure hμ
  have hU := tendsto_sqNorm_integral_restrict_of_Lp hun (Icc a b) hμ
  have hG := tendsto_sqNorm_integral_restrict_of_Lp hgn (Icc a b) hμ
  have hUs : Tendsto (fun n => √(∫ t, ‖un n t - u t‖ ^ 2 ∂μ))
      atTop (𝓝 0) := by simpa only [Real.sqrt_zero, Function.comp_def] using hU.sqrt
  have hGs : Tendsto (fun n => √(∫ t, ‖gn n t - g t‖ ^ 2 ∂μ))
      atTop (𝓝 0) := by simpa only [Real.sqrt_zero, Function.comp_def] using hG.sqrt
  have hub : IsBoundedUnder LE.le atTop (fun n => ‖un n‖) :=
    hun.norm.isBoundedUnder_le
  have hlocalb : IsBoundedUnder LE.le atTop
      (fun n => √(∫ t, ‖un n t‖ ^ 2 ∂μ)) := by
    obtain ⟨C, hC⟩ := hub.eventually_le
    apply isBoundedUnder_of_eventually_le
    filter_upwards [hC] with n hn
    have hglobal := Lp.memLp (un n)
    have hi : (∫ t, ‖un n t‖ ^ 2 ∂μ) ≤
        ∫ t, ‖un n t‖ ^ 2 ∂reverseTimeVolume T :=
      integral_mono_measure hμ (Eventually.of_forall fun _ => sq_nonneg _)
        (hglobal.integrable_norm_pow (by norm_num))
    rw [integral_norm_sq_eq_norm_sq_toLp (un n) hglobal] at hi
    have hto : hglobal.toLp (un n) = un n := by
      apply Lp.ext
      exact hglobal.coeFn_toLp
    rw [hto] at hi
    exact (Real.sqrt_le_sqrt hi).trans_eq (Real.sqrt_sq (norm_nonneg _)) |>.trans hn
  have hlocalbnorm : IsBoundedUnder LE.le atTop
      (fun n => ‖√(∫ t, ‖un n t‖ ^ 2 ∂μ)‖) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using hlocalb
  have hfirst := hGs.zero_mul_isBoundedUnder_le hlocalbnorm
  have hsecond : Tendsto (fun n => √(∫ t, ‖g t‖ ^ 2 ∂μ) *
      √(∫ t, ‖un n t - u t‖ ^ 2 ∂μ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hUs
  apply squeeze_zero'
  · exact Eventually.of_forall fun _ => integral_nonneg fun _ => abs_nonneg _
  · filter_upwards with n
    exact shifted_dualPairing_integral_le hΩ u (un n) g (gn n)
      hu (hunm n) hg (hgnm n)
  · simpa only [zero_add] using hfirst.add hsecond

/-- Forward Steklov regularization preserves the tested affine-threshold
shifted-positive-part energy in the zero-width limit. -/
theorem tendsto_forwardSteklov_shiftedPositivePartEnergy_test
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (M N : ℝ≥0) (T : ℝ)
    (u : ReverseTimeL2V hΩ T) (eta : ReverseTimeScalarTest T) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b < T) :
    Tendsto (fun h : ℝ => ∫ t in Icc a b,
      shiftedPositivePartEnergy hΩ M N
        (fun t => reverseTimeForwardSteklov T h u t) t * eta.deriv t)
      (𝓝[>] 0) (𝓝 (∫ t in Icc a b,
        shiftedPositivePartEnergy hΩ M N (fun t => u t) t * eta.deriv t)) := by
  have hT : 0 < T := lt_trans ha (lt_trans hab hb)
  have hK : Icc a b ⊆ Ioo (0 : ℝ) T := by
    intro t ht
    exact ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩
  have hμ : volume.restrict (Icc a b) ≤ reverseTimeVolume T := by
    change volume.restrict (Icc a b) ≤ volume.restrict (Ioo (0 : ℝ) T)
    exact Measure.restrict_mono' (ae_of_all _ fun t ht => hK ht) le_rfl
  rw [tendsto_iff_seq_tendsto]
  intro hs hhs
  let uh : ℕ → ReverseTimeL2V hΩ T := fun n =>
    reverseTimeForwardSteklovL2 T (hs n) u
  let up : ReverseTimeL2V hΩ T := reverseTimeShiftedPositivePart hΩ T M N u
  let uhp : ℕ → ReverseTimeL2V hΩ T := fun n =>
    reverseTimeShiftedPositivePart hΩ T M N (uh n)
  have huh : Tendsto uh atTop (𝓝 u) :=
    (tendsto_reverseTimeForwardSteklovL2 T hT u).comp hhs
  have huhp : Tendsto uhp atTop (𝓝 up) :=
    (continuous_reverseTimeShiftedPositivePart hΩ T M N).continuousAt.tendsto.comp huh
  have hclass := tendsto_integral_abs_valueCLM_sq_of_tendsto
    hΩ up uhp huhp hμ
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < hs n :=
    hhs (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)
  have hEabs : Tendsto (fun n => ∫ t in Icc a b,
      |shiftedPositivePartEnergy hΩ M N
          (fun t => reverseTimeForwardSteklov T (hs n) u t) t -
        shiftedPositivePartEnergy hΩ M N (fun t => u t) t|)
      atTop (𝓝 0) := by
    apply hclass.congr'
    filter_upwards [hpos] with n hn
    apply integral_congr_ae
    filter_upwards
        [(coeFn_reverseTimeForwardSteklovL2_of_pos T hn u).filter_mono
            (ae_mono hμ),
          (coeFn_reverseTimeShiftedPositivePart hΩ T M N (uh n)).filter_mono
            (ae_mono hμ),
          (coeFn_reverseTimeShiftedPositivePart hΩ T M N u).filter_mono
            (ae_mono hμ)]
      with t hraw hshift hlimit
    simp only [uhp, up, shiftedPositivePartEnergy]
    rw [hshift, hlimit, hraw]
  have hraw : Integrable
      (shiftedPositivePartEnergy hΩ M N (fun t => u t))
      (volume.restrict (Icc a b)) := by
    have hm := (Lp.memLp up).mono_measure hμ
    have hv := hm.continuousLinearMap_comp (valueCLM hΩ)
    apply (hv.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).congr
    filter_upwards [(coeFn_reverseTimeShiftedPositivePart hΩ T M N u).filter_mono
        (ae_mono hμ)] with t ht
    simp only [shiftedPositivePartEnergy]
    rw [ht]
  have hforward : ∀ᶠ n : ℕ in atTop, Integrable
      (shiftedPositivePartEnergy hΩ M N
        (fun t => reverseTimeForwardSteklov T (hs n) u t))
      (volume.restrict (Icc a b)) := by
    filter_upwards [hpos] with n hn
    exact (((valueCLM hΩ).continuous.comp
      ((continuous_h10ShiftedPositivePart hΩ).comp
        ((continuous_reverseTimeForwardSteklov T (hs n) hn u).prodMk
          (continuous_const.add
            (continuous_real_toNNReal.mul continuous_const))))).norm.pow 2).integrableOn_Icc
  exact tendsto_integral_mul_of_tendsto_integral_abs hforward hraw
    eta.contDiff_deriv.continuous.aestronglyMeasurable eta.exists_norm_deriv_le hEabs

private theorem ae_shiftedPositivePartEnergyRate_forwardSteklovL2
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω) (M N : ℝ≥0)
    (T : ℝ) {h : ℝ} (hh : 0 < h)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) :
    (fun t => shiftedPositivePartEnergyRate hΩ hΩbounded M N
      (fun r => reverseTimeForwardSteklov T h u r)
      (fun r => reverseTimeForwardSteklov T h g r) t) =ᵐ[reverseTimeVolume T]
    fun t => (reverseTimeForwardSteklovL2 T h g t)
      (reverseTimeShiftedPositivePart hΩ T M N
        (reverseTimeForwardSteklovL2 T h u) t) -
      (N : ℝ) * ((spatialMassCLM hΩbounded).comp (valueCLM hΩ))
        (reverseTimeShiftedPositivePart hΩ T M N
          (reverseTimeForwardSteklovL2 T h u) t) := by
  letI : NormedAddCommGroup (H10HilbertGraphDual hΩ) := by infer_instance
  letI : ContinuousENorm (H10HilbertGraphDual hΩ) := by infer_instance
  letI : NormedSpace ℝ (H10HilbertGraphDual hΩ) := by infer_instance
  letI : CompleteSpace (H10HilbertGraphDual hΩ) := by infer_instance
  filter_upwards [coeFn_reverseTimeForwardSteklovL2_of_pos T hh u,
      coeFn_reverseTimeForwardSteklovL2_of_pos T hh g,
      coeFn_reverseTimeShiftedPositivePart hΩ T M N
        (reverseTimeForwardSteklovL2 T h u)] with t hu hg hup
  simp only [shiftedPositivePartEnergyRate, ContinuousLinearMap.comp_apply]
  simp only [← hup, ← hu, ← hg]

private theorem ae_shiftedPositivePartEnergyRate_L2
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω) (M N : ℝ≥0)
    (T : ℝ) (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) :
    (fun t => shiftedPositivePartEnergyRate hΩ hΩbounded M N
      (fun r => u r) (fun r => g r) t) =ᵐ[reverseTimeVolume T]
    fun t => (g t) (reverseTimeShiftedPositivePart hΩ T M N u t) -
      (N : ℝ) * ((spatialMassCLM hΩbounded).comp (valueCLM hΩ))
        (reverseTimeShiftedPositivePart hΩ T M N u t) := by
  filter_upwards [coeFn_reverseTimeShiftedPositivePart hΩ T M N u] with t hup
  simp only [shiftedPositivePartEnergyRate, ContinuousLinearMap.comp_apply]
  rw [hup]

private theorem integrable_shiftedPositivePartEnergyRate_L2_on_Icc
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω) (M N : ℝ≥0)
    (T : ℝ) (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    {a b : ℝ} (hμ : volume.restrict (Icc a b) ≤ reverseTimeVolume T) :
    Integrable (shiftedPositivePartEnergyRate hΩ hΩbounded M N
      (fun t => u t) (fun t => g t)) (volume.restrict (Icc a b)) := by
  have huLocal := (Lp.memLp (reverseTimeShiftedPositivePart hΩ T M N u)).mono_measure hμ
  have hgLocal : MemLp (g : ℝ → H10HilbertGraphDual hΩ) 2
      (volume.restrict (Icc a b)) := (Lp.memLp g).mono_measure hμ
  have hp := shifted_integrable_dualPairing hΩ
    (reverseTimeShiftedPositivePart hΩ T M N u) g huLocal hgLocal
  have hm := huLocal.continuousLinearMap_comp
    ((spatialMassCLM hΩbounded).comp (valueCLM hΩ))
  apply (hp.sub ((hm.integrable (by norm_num)).const_mul (N : ℝ))).congr
  exact (ae_shiftedPositivePartEnergyRate_L2 hΩ hΩbounded M N T u g).symm.filter_mono
    (ae_mono hμ)

private theorem integrable_shiftedPositivePartEnergyRate_forwardSteklov_on_Icc
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω) (M N : ℝ≥0)
    (T : ℝ) {h : ℝ} (hh : 0 < h)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) (a b : ℝ) :
    Integrable (shiftedPositivePartEnergyRate hΩ hΩbounded M N
      (fun t => reverseTimeForwardSteklov T h u t)
      (fun t => reverseTimeForwardSteklov T h g t))
      (volume.restrict (Icc a b)) := by
  have hk : Continuous (reverseTimeAffineThreshold M N) :=
    continuous_const.add (continuous_real_toNNReal.mul continuous_const)
  have hp := (continuous_h10ShiftedPositivePart hΩ).comp
    ((continuous_reverseTimeForwardSteklov T h hh u).prodMk hk)
  exact (((continuous_reverseTimeForwardSteklov T h hh g).clm_apply hp).sub
    (continuous_const.mul
      (((spatialMassCLM hΩbounded).comp (valueCLM hΩ)).continuous.comp hp))
    |>.integrableOn_Icc)

/-- Forward Steklov regularization preserves the tested affine-threshold
shifted-positive-part energy rate in the zero-width limit. -/
theorem tendsto_forwardSteklov_shiftedPositivePartEnergyRate_test
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (M N : ℝ≥0) (T : ℝ)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (eta : ReverseTimeScalarTest T) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b < T) :
    Tendsto (fun h : ℝ => ∫ t in Icc a b,
      shiftedPositivePartEnergyRate hΩ hΩbounded M N
        (fun t => reverseTimeForwardSteklov T h u t)
        (fun t => reverseTimeForwardSteklov T h g t) t * eta t)
      (𝓝[>] 0) (𝓝 (∫ t in Icc a b,
        shiftedPositivePartEnergyRate hΩ hΩbounded M N
          (fun t => u t) (fun t => g t) t * eta t)) := by
  letI : NormedAddCommGroup (H10HilbertGraphDual hΩ) := by infer_instance
  letI : ContinuousENorm (H10HilbertGraphDual hΩ) := by infer_instance
  letI : NormedSpace ℝ (H10HilbertGraphDual hΩ) := by infer_instance
  letI : CompleteSpace (H10HilbertGraphDual hΩ) := by infer_instance
  have hT : 0 < T := lt_trans ha (lt_trans hab hb)
  have hK : Icc a b ⊆ Ioo (0 : ℝ) T := by
    intro t ht
    exact ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩
  have hμ : volume.restrict (Icc a b) ≤ reverseTimeVolume T := by
    change volume.restrict (Icc a b) ≤ volume.restrict (Ioo (0 : ℝ) T)
    exact Measure.restrict_mono' (ae_of_all _ fun t ht => hK ht) le_rfl
  rw [tendsto_iff_seq_tendsto]
  intro hs hhs
  let uh : ℕ → ReverseTimeL2V hΩ T := fun n =>
    reverseTimeForwardSteklovL2 T (hs n) u
  let gh : ℕ → ReverseTimeL2VStar hΩ T := fun n =>
    reverseTimeForwardSteklovL2 T (hs n) g
  let up : ReverseTimeL2V hΩ T := reverseTimeShiftedPositivePart hΩ T M N u
  let uhp : ℕ → ReverseTimeL2V hΩ T := fun n =>
    reverseTimeShiftedPositivePart hΩ T M N (uh n)
  have huh : Tendsto uh atTop (𝓝 u) :=
    (tendsto_reverseTimeForwardSteklovL2 T hT u).comp hhs
  have hgh : Tendsto gh atTop (𝓝 g) :=
    (tendsto_reverseTimeForwardSteklovL2 T hT g).comp hhs
  have huhp : Tendsto uhp atTop (𝓝 up) :=
    (continuous_reverseTimeShiftedPositivePart hΩ T M N).continuousAt.tendsto.comp huh
  let Q := (spatialMassCLM hΩbounded).comp (valueCLM hΩ)
  have hpair := tendsto_integral_abs_dualPairing_of_tendsto
    hΩ up g uhp gh huhp hgh hμ
  have hmass := tendsto_integral_abs_spatialMass_value_of_tendsto
    hΩ hΩbounded up uhp huhp hμ
  have herrClass : Tendsto (fun n => ∫ t in Icc a b,
      |(gh n t) (uhp n t) - (N : ℝ) *
          Q (uhp n t) -
        ((g t) (up t) - (N : ℝ) *
          Q (up t))|)
      atTop (𝓝 0) := by
    apply squeeze_zero' (g := fun n =>
      (∫ t in Icc a b, |(gh n t) (uhp n t) - (g t) (up t)|) +
      (N : ℝ) * (∫ t in Icc a b,
        |Q (uhp n t) - Q (up t)|))
    · exact Eventually.of_forall fun _ => integral_nonneg fun _ => abs_nonneg _
    · filter_upwards with n
      have huLocal := (Lp.memLp up).mono_measure hμ
      have huhLocal := (Lp.memLp (uhp n)).mono_measure hμ
      have hgLocal : MemLp (g : ℝ → H10HilbertGraphDual hΩ) 2
          (volume.restrict (Icc a b)) := (Lp.memLp g).mono_measure hμ
      have hghLocal : MemLp (gh n : ℝ → H10HilbertGraphDual hΩ) 2
          (volume.restrict (Icc a b)) := (Lp.memLp (gh n)).mono_measure hμ
      have hp0 := shifted_integrable_dualPairing hΩ up g huLocal hgLocal
      have hp1 := shifted_integrable_dualPairing hΩ (uhp n) (gh n)
        huhLocal hghLocal
      have hm0 := huLocal.continuousLinearMap_comp
        Q
      have hm1 := huhLocal.continuousLinearMap_comp
        Q
      exact integral_abs_sub_mul_sub_le
        (fun t => (gh n t) (uhp n t)) (fun t => (g t) (up t))
        (fun t => Q (uhp n t)) (fun t => Q (up t)) (N : ℝ) N.coe_nonneg
        hp1 hp0 (hm1.integrable (by norm_num)) (hm0.integrable (by norm_num))
    · have hscaled : Tendsto (fun n => (N : ℝ) * (∫ t in Icc a b,
          |Q (uhp n t) - Q (up t)|))
          atTop (𝓝 0) := by
        simpa only [mul_zero] using tendsto_const_nhds.mul hmass
      simpa only [zero_add] using hpair.add hscaled
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < hs n :=
    hhs (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)
  have herr : Tendsto (fun n => ∫ t in Icc a b,
      |shiftedPositivePartEnergyRate hΩ hΩbounded M N
          (fun t => reverseTimeForwardSteklov T (hs n) u t)
          (fun t => reverseTimeForwardSteklov T (hs n) g t) t -
        shiftedPositivePartEnergyRate hΩ hΩbounded M N
          (fun t => u t) (fun t => g t) t|) atTop (𝓝 0) := by
    apply herrClass.congr'
    filter_upwards [hpos] with n hn
    apply integral_congr_ae
    filter_upwards
        [(ae_shiftedPositivePartEnergyRate_forwardSteklovL2 hΩ hΩbounded
            M N T hn u g).filter_mono (ae_mono hμ),
          (ae_shiftedPositivePartEnergyRate_L2 hΩ hΩbounded M N T u g).filter_mono
            (ae_mono hμ)] with t hforwardRate hlimitRate
    exact congrArg₂ (fun x y : ℝ => |x - y|) hforwardRate.symm hlimitRate.symm
  have hraw := integrable_shiftedPositivePartEnergyRate_L2_on_Icc
    hΩ hΩbounded M N T u g hμ
  have hforward : ∀ᶠ n : ℕ in atTop, Integrable
      (shiftedPositivePartEnergyRate hΩ hΩbounded M N
        (fun t => reverseTimeForwardSteklov T (hs n) u t)
        (fun t => reverseTimeForwardSteklov T (hs n) g t))
      (volume.restrict (Icc a b)) := by
    filter_upwards [hpos] with n hn
    exact integrable_shiftedPositivePartEnergyRate_forwardSteklov_on_Icc
      hΩ hΩbounded M N T hn u g a b
  exact tendsto_integral_mul_of_tendsto_integral_abs hforward hraw
    eta.contDiff.continuous.aestronglyMeasurable eta.exists_norm_le herr

end HypoellipticAleksandrov.Parabolic.Dirichlet
