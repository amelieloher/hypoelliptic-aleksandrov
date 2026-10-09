module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.H10PositivePart
public import HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialSobolevNorm

/-!
# Continuity of positive parts in spatial `H¹₀`

This module proves the sharp graph-norm contraction of the positive-part
operation and its strong continuity on an arbitrary open set.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

variable {d : ℕ} {Ω : Set (PDE.Vec d)}

private theorem tendsto_eLpNorm_two_zero_of_ae_dominated
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {F : ℕ → α → E} {bound : α → E}
    (hF : ∀ n, AEStronglyMeasurable (F n) μ)
    (hboundMem : MemLp bound (2 : ℝ≥0∞) μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ ‖bound x‖)
    (hzero : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (F n) (2 : ℝ≥0∞) μ) atTop (𝓝 0) := by
  let G : ℕ → α → ℝ≥0∞ := fun n x => ‖F n x‖ₑ ^ (2 : ℝ)
  let B : α → ℝ≥0∞ := fun x => ‖bound x‖ₑ ^ (2 : ℝ)
  have hGMeas : ∀ n, AEMeasurable (G n) μ := by
    intro n
    exact (hF n).enorm.pow_const _
  have hGBound : ∀ n, G n ≤ᵐ[μ] B := by
    intro n
    filter_upwards [hbound n] with x hx
    have henorm : ‖F n x‖ₑ ≤ ‖bound x‖ₑ := by
      simpa only [ofReal_norm_eq_enorm] using ENNReal.ofReal_le_ofReal hx
    exact ENNReal.rpow_le_rpow henorm (by norm_num)
  have hBFinite : ∫⁻ x, B x ∂μ ≠ ∞ :=
    (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) hboundMem).ne
  have hGZero : ∀ᵐ x ∂μ, Tendsto (fun n => G n x) atTop (𝓝 0) := by
    filter_upwards [hzero] with x hx
    have henorm : Tendsto (fun n => ‖F n x‖ₑ) atTop (𝓝 0) := by
      simpa only [enorm_zero, Function.comp_def] using (continuous_enorm.tendsto 0).comp hx
    simpa only [G, Function.comp_def, enorm_zero,
      ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)] using
      ((ENNReal.continuous_rpow_const :
        Continuous (fun a : ℝ≥0∞ => a ^ (2 : ℝ))).tendsto 0).comp henorm
  have hint : Tendsto (fun n => ∫⁻ x, G n x ∂μ) atTop (𝓝 0) := by
    simpa only [lintegral_zero] using
      tendsto_lintegral_of_dominated_convergence'
        B hGMeas hGBound hBFinite hGZero
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (hF _)]
  simpa only [G, Function.comp_def, ENNReal.toReal_ofNat, one_div,
    ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)] using
    ((ENNReal.continuous_rpow_const :
      Continuous (fun a : ℝ≥0∞ => a ^ ((2 : ℝ)⁻¹))).tendsto 0).comp hint

private theorem tendsto_indicator_sub_indicator_of_tendsto
    {α E : Type*} [NormedAddCommGroup E] {f : ℕ → α → ℝ} {f₀ : α → ℝ}
    {g₀ : α → E} {x : α}
    (hf : Tendsto (fun n => f n x) atTop (𝓝 (f₀ x)))
    (hzero : f₀ x = 0 → g₀ x = 0) :
    Tendsto (fun n =>
      {y | 0 < f n y}.indicator g₀ x - {y | 0 < f₀ y}.indicator g₀ x)
      atTop (𝓝 0) := by
  rcases lt_trichotomy (f₀ x) 0 with hneg | hz | hpos
  · have hevent : ∀ᶠ n in atTop, f n x < 0 :=
      (tendsto_order.1 hf).2 _ hneg
    apply (tendsto_congr' (hevent.mono fun n hn => ?_)).2 tendsto_const_nhds
    simp only [indicator_apply, Set.mem_setOf_eq, hn.not_gt, hneg.not_gt, sub_self]
  · have hgzero : g₀ x = 0 := hzero hz
    have heq : (fun n =>
        {y | 0 < f n y}.indicator g₀ x - {y | 0 < f₀ y}.indicator g₀ x) =
        (fun _ => (0 : E)) := by
      funext n
      simp only [indicator_apply, hgzero]
      split <;> split <;> simp
    rw [heq]
    exact tendsto_const_nhds
  · have hevent : ∀ᶠ n in atTop, 0 < f n x :=
      (tendsto_order.1 hf).1 _ hpos
    apply (tendsto_congr' (hevent.mono fun n hn => ?_)).2 tendsto_const_nhds
    simp only [indicator_apply, Set.mem_setOf_eq, hn, hpos, sub_self]

private theorem indicator_gradient_error_ae
    {α E : Type*} [MeasurableSpace α] [AddCommGroup E]
    {μ : Measure α} {f f₀ : α → ℝ} {g g₀ p p₀ q : α → E}
    (hp : p =ᵐ[μ] {y | 0 < f y}.indicator g)
    (hp₀ : p₀ =ᵐ[μ] {y | 0 < f₀ y}.indicator g₀)
    (hout : q =ᵐ[μ] fun x => p x - p₀ x) :
    q =ᵐ[μ] fun x =>
      {y | 0 < f y}.indicator (g - g₀) x +
        ({y | 0 < f y}.indicator g₀ x - {y | 0 < f₀ y}.indicator g₀ x) := by
  filter_upwards [hp, hp₀, hout] with x hpx hp₀x houtx
  rw [houtx, hpx, hp₀x]
  simp only [Pi.sub_apply, indicator_apply]
  split <;> split <;> simp

/-- Taking the positive part contracts the full spatial `H¹₀` graph norm,
with sharp constant one. -/
theorem norm_h10PositivePart_le
    (hΩ : IsOpen Ω) (u : H10HilbertGraph hΩ) :
    ‖h10PositivePart hΩ u‖ ≤ ‖u‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [norm_sq_h10HilbertGraph hΩ, norm_sq_h10HilbertGraph hΩ]
  exact add_le_add
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.2
      (norm_valueCLM_h10PositivePart_le hΩ u))
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.2
      (norm_gradientCLM_h10PositivePart_le hΩ u))

/-- The positive-part operation is strongly continuous on the spatial
`H¹₀` Hilbert graph. -/
theorem continuous_h10PositivePart (hΩ : IsOpen Ω) :
    Continuous (h10PositivePart hΩ :
      H10HilbertGraph hΩ → H10HilbertGraph hΩ) := by
  rw [continuous_iff_seqContinuous]
  intro un u hun
  have hvalue : Tendsto (fun n => valueCLM hΩ (h10PositivePart hΩ (un n)))
      atTop (𝓝 (valueCLM hΩ (h10PositivePart hΩ u))) := by
    simpa only [valueCLM_h10PositivePart, Function.comp_def] using
      Lp.continuous_posPart.comp (valueCLM hΩ).continuous |>.tendsto u |>.comp hun
  have huValue : Tendsto (fun n => valueCLM hΩ (un n))
      atTop (𝓝 (valueCLM hΩ u)) :=
    ((valueCLM hΩ).continuous.tendsto u).comp hun
  have huGrad : Tendsto (fun n => gradientCLM hΩ (un n))
      atTop (𝓝 (gradientCLM hΩ u)) :=
    ((gradientCLM hΩ).continuous.tendsto u).comp hun
  let μ := PDE.volumeOn Ω
  let f : ℕ → PDE.Vec d → ℝ := fun n => valueCLM hΩ (un n)
  let f₀ : PDE.Vec d → ℝ := valueCLM hΩ u
  let g : ℕ → PDE.Vec d → WithLp 2 (PDE.Vec d) :=
    fun n => gradientCLM hΩ (un n)
  let g₀ : PDE.Vec d → WithLp 2 (PDE.Vec d) := gradientCLM hΩ u
  let A : ℕ → PDE.Vec d → WithLp 2 (PDE.Vec d) := fun n x =>
    {y | 0 < f n y}.indicator (g n) x
  let A₀ : PDE.Vec d → WithLp 2 (PDE.Vec d) := fun x =>
    {y | 0 < f₀ y}.indicator g₀ x
  let R : ℕ → PDE.Vec d → WithLp 2 (PDE.Vec d) := fun n x =>
    {y | 0 < f n y}.indicator g₀ x - A₀ x
  have hfMeasure : TendstoInMeasure μ f atTop f₀ := by
    exact tendstoInMeasure_of_tendsto_Lp huValue
  have hR : Tendsto (fun n => eLpNorm (R n) 2 μ) atTop (𝓝 0) := by
    apply tendsto_of_subseq_tendsto
    intro ns hns
    obtain ⟨ms, -, hae⟩ :=
      (hfMeasure.comp hns).exists_seq_tendsto_ae
    refine ⟨ms, ?_⟩
    apply tendsto_eLpNorm_two_zero_of_ae_dominated
    · intro n
      apply AEStronglyMeasurable.sub
      · rw [aestronglyMeasurable_indicator_iff₀
          (nullMeasurableSet_lt aemeasurable_const
            (Lp.aestronglyMeasurable (valueCLM hΩ (un (ns (ms n))))).aemeasurable)]
        exact (Lp.aestronglyMeasurable (gradientCLM hΩ u)).restrict
      · rw [aestronglyMeasurable_indicator_iff₀
          (nullMeasurableSet_lt aemeasurable_const
            (Lp.aestronglyMeasurable (valueCLM hΩ u)).aemeasurable)]
        exact (Lp.aestronglyMeasurable (gradientCLM hΩ u)).restrict
    · exact (Lp.memLp (gradientCLM hΩ u))
    · intro n
      filter_upwards with x
      simp only [R, A₀, f, f₀, g₀, indicator_apply]
      split <;> split <;> simp
    · filter_upwards [hae, gradientCLM_ae_zero_on_level_set hΩ u 0] with x hx hgrad
      exact tendsto_indicator_sub_indicator_of_tendsto hx hgrad
  have hgrad : Tendsto
      (fun n => gradientCLM hΩ (h10PositivePart hΩ (un n)))
      atTop (𝓝 (gradientCLM hΩ (h10PositivePart hΩ u))) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    have hfirst : Tendsto (fun n =>
        eLpNorm ({y | 0 < f n y}.indicator (g n - g₀)) 2 μ)
        atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        ((Lp.tendsto_Lp_iff_tendsto_eLpNorm'
          (fun n => gradientCLM hΩ (un n)) (gradientCLM hΩ u)).1 huGrad)
        (fun n => zero_le') (fun n => eLpNorm_indicator_le _
          (measurableSet_lt measurable_const
            (Lp.stronglyMeasurable (valueCLM hΩ (un n))).measurable))
    have hindicatorMeas : ∀ n, AEStronglyMeasurable
        ({y | 0 < f n y}.indicator (g n - g₀)) μ := by
      intro n
      rw [aestronglyMeasurable_indicator_iff₀
        (nullMeasurableSet_lt aemeasurable_const
          (Lp.aestronglyMeasurable (valueCLM hΩ (un n))).aemeasurable)]
      exact ((Lp.aestronglyMeasurable (gradientCLM hΩ (un n))).sub
        (Lp.aestronglyMeasurable (gradientCLM hΩ u))).restrict
    have hRMeas : ∀ n, AEStronglyMeasurable (R n) μ := by
      intro n
      apply AEStronglyMeasurable.sub
      · rw [aestronglyMeasurable_indicator_iff₀
          (nullMeasurableSet_lt aemeasurable_const
            (Lp.aestronglyMeasurable (valueCLM hΩ (un n))).aemeasurable)]
        exact (Lp.aestronglyMeasurable (gradientCLM hΩ u)).restrict
      · rw [aestronglyMeasurable_indicator_iff₀
          (nullMeasurableSet_lt aemeasurable_const
            (Lp.aestronglyMeasurable (valueCLM hΩ u)).aemeasurable)]
        exact (Lp.aestronglyMeasurable (gradientCLM hΩ u)).restrict
    have hsum : Tendsto (fun n =>
        eLpNorm ({y | 0 < f n y}.indicator (g n - g₀) + R n) 2 μ)
        atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (by simpa only [zero_add] using hfirst.add hR)
        (fun n => zero_le')
        (fun n => eLpNorm_add_le (by norm_num))
    refine hsum.congr' ?_
    filter_upwards with n
    apply eLpNorm_congr_ae
    simpa only [μ, f, f₀, g, g₀, R, A₀, Pi.add_def, Pi.sub_def] using
      (indicator_gradient_error_ae
      (q := fun x =>
        gradientCLM hΩ (h10PositivePart hΩ (un n)) x -
          gradientCLM hΩ (h10PositivePart hΩ u) x)
      (gradientCLM_h10PositivePart hΩ (un n))
      (gradientCLM_h10PositivePart hΩ u)
      (Filter.Eventually.of_forall fun _ => rfl)).symm
  rw [Metric.tendsto_atTop] at hvalue hgrad ⊢
  intro ε hε
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  obtain ⟨Nv, hNv⟩ := hvalue (ε / Real.sqrt 2)
    (div_pos hε (Real.sqrt_pos.2 (by norm_num)))
  obtain ⟨Ng, hNg⟩ := hgrad (ε / Real.sqrt 2)
    (div_pos hε (Real.sqrt_pos.2 (by norm_num)))
  refine ⟨max Nv Ng, fun n hn => ?_⟩
  have hv := hNv n (le_trans (le_max_left _ _) hn)
  have hg := hNg n (le_trans (le_max_right _ _) hn)
  rw [dist_eq_norm, Function.comp_apply]
  change ‖h10PositivePart hΩ (un n) - h10PositivePart hΩ u‖ < ε
  apply (sq_lt_sq₀ (norm_nonneg _) hε.le).1
  rw [norm_sq_h10HilbertGraph hΩ]
  simp only [map_sub]
  rw [dist_eq_norm] at hv hg
  have hv2 := (sq_lt_sq₀ (norm_nonneg _) (div_pos hε
    (Real.sqrt_pos.2 (by norm_num))).le).2 hv
  have hg2 := (sq_lt_sq₀ (norm_nonneg _) (div_pos hε
    (Real.sqrt_pos.2 (by norm_num))).le).2 hg
  have hdivsq : (ε / Real.sqrt 2) ^ 2 = ε ^ 2 / 2 := by
    rw [div_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  rw [hdivsq] at hv2 hg2
  linarith

end HypoellipticAleksandrov.Parabolic.Dirichlet
