module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.GeneralOpenH1ZeroLevel

/-!
# Strong continuity of positive parts in H¹ on general open sets

Strong convergence of exact `H1Function` representatives is preserved by the
positive-part operation.  The gradient proof uses convergence in measure,
almost-everywhere convergence along subsubsequences, and vanishing of the weak
gradient on the zero set of the limiting representative.
-/

@[expose] public section

namespace PDE.H1Function

open Filter MeasureTheory Set
open scoped ENNReal Topology

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
  have hGMeas : ∀ n, AEMeasurable (G n) μ := fun n => (hF n).enorm.pow_const _
  have hGBound : ∀ n, G n ≤ᵐ[μ] B := by
    intro n
    filter_upwards [hbound n] with x hx
    exact ENNReal.rpow_le_rpow (by
      simpa only [ofReal_norm_eq_enorm] using ENNReal.ofReal_le_ofReal hx) (by norm_num)
  have hBFinite : ∫⁻ x, B x ∂μ ≠ ∞ :=
    (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) (memLp_iff.mp hboundMem)).ne
  have hGZero : ∀ᵐ x ∂μ, Tendsto (fun n => G n x) atTop (𝓝 0) := by
    filter_upwards [hzero] with x hx
    have henorm : Tendsto (fun n => ‖F n x‖ₑ) atTop (𝓝 0) := by
      simpa only [Function.comp_def, enorm_zero] using (continuous_enorm.tendsto 0).comp hx
    simpa only [Function.comp_def, G, enorm_zero,
       ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)] using
      ((ENNReal.continuous_rpow_const :
        Continuous (fun a : ℝ≥0∞ => a ^ (2 : ℝ))).tendsto 0).comp henorm
  have hint : Tendsto (fun n => ∫⁻ x, G n x ∂μ) atTop (𝓝 0) := by
    simpa only [lintegral_zero] using
      tendsto_lintegral_of_dominated_convergence' B hGMeas hGBound hBFinite hGZero
  simpa only [Function.comp_def, G, eLpNorm_eq_lintegral_rpow_enorm_toReal
       (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (hF _), ENNReal.toReal_ofNat, one_div,
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
  · have hevent : ∀ᶠ n in atTop, f n x < 0 := (tendsto_order.1 hf).2 _ hneg
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
  · have hevent : ∀ᶠ n in atTop, 0 < f n x := (tendsto_order.1 hf).1 _ hpos
    apply (tendsto_congr' (hevent.mono fun n hn => ?_)).2 tendsto_const_nhds
    simp only [indicator_apply, Set.mem_setOf_eq, hn, hpos, sub_self]

/-- Positive parts of exact `H¹` representatives and their strict-superlevel
gradients converge strongly in `L²` on an arbitrary open set. -/
theorem tendsto_positivePart_of_tendsto_eLpNorm
    {d : ℕ} {U : Set (PDE.Vec d)} (hU : IsOpen U)
    (u : ℕ → PDE.H1Function U) (v : PDE.H1Function U)
    (hval : Tendsto
      (fun n => eLpNorm ((u n).toFun - v.toFun)
        (2 : ℝ≥0∞) (PDE.volumeOn U)) atTop (𝓝 0))
    (hgrad : ∀ i : Fin d, Tendsto
      (fun n => eLpNorm (fun x => (u n).grad x i - v.grad x i)
        (2 : ℝ≥0∞) (PDE.volumeOn U)) atTop (𝓝 0)) :
    Tendsto
      (fun n => eLpNorm
        ((fun x => max ((u n).toFun x) 0) - (fun x => max (v.toFun x) 0))
        (2 : ℝ≥0∞) (PDE.volumeOn U)) atTop (𝓝 0) ∧
    ∀ i : Fin d, Tendsto
      (fun n => eLpNorm
        (fun x =>
          {y | 0 < (u n).toFun y}.indicator (u n).grad x i -
          {y | 0 < v.toFun y}.indicator v.grad x i)
        (2 : ℝ≥0∞) (PDE.volumeOn U)) atTop (𝓝 0) := by
  let μ := PDE.volumeOn U
  let f : ℕ → PDE.Vec d → ℝ := fun n => (u n).toFun
  let f₀ : PDE.Vec d → ℝ := v.toFun
  have hfMeas : ∀ n, AEStronglyMeasurable (f n) μ := fun n => (u n).memL2.aestronglyMeasurable
  have hf₀Meas : AEStronglyMeasurable f₀ μ := v.memL2.aestronglyMeasurable
  constructor
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hval
      (fun _ => zero_le') (fun n => eLpNorm_mono_ae
        ((continuous_max.comp_aestronglyMeasurable₂ (hfMeas n) aestronglyMeasurable_const).sub
          (continuous_max.comp_aestronglyMeasurable₂ hf₀Meas aestronglyMeasurable_const)) ?_)
    filter_upwards with x
    simp only [Pi.sub_apply, Real.norm_eq_abs]
    exact abs_max_sub_max_le_abs ((u n).toFun x) (v.toFun x) 0
  · intro i
    let g : ℕ → PDE.Vec d → ℝ := fun n x => (u n).grad x i
    let g₀ : PDE.Vec d → ℝ := fun x => v.grad x i
    let R : ℕ → PDE.Vec d → ℝ := fun n x =>
      {y | 0 < f n y}.indicator g₀ x - {y | 0 < f₀ y}.indicator g₀ x
    have hgMeas : ∀ n, AEStronglyMeasurable (g n) μ :=
      fun n => (u n).gradMemL2 i |>.aestronglyMeasurable
    have hg₀Meas : AEStronglyMeasurable g₀ μ := (v.gradMemL2 i).aestronglyMeasurable
    have hfMeasure : TendstoInMeasure μ f atTop f₀ :=
      tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hval
    have hR : Tendsto (fun n => eLpNorm (R n) 2 μ) atTop (𝓝 0) := by
      apply tendsto_of_subseq_tendsto
      intro ns hns
      obtain ⟨ms, -, hae⟩ := (hfMeasure.comp hns).exists_seq_tendsto_ae
      refine ⟨ms, ?_⟩
      apply tendsto_eLpNorm_two_zero_of_ae_dominated (bound := g₀)
      · intro n
        apply AEStronglyMeasurable.sub
        · exact hg₀Meas.indicator₀
            (nullMeasurableSet_lt aemeasurable_const (hfMeas (ns (ms n))).aemeasurable)
        · exact hg₀Meas.indicator₀
            (nullMeasurableSet_lt aemeasurable_const hf₀Meas.aemeasurable)
      · exact v.gradMemL2 i
      · intro n
        filter_upwards with x
        simp only [R, indicator_apply]
        split <;> split <;> simp
      · filter_upwards [hae, grad_ae_zero_on_zero_set_of_isOpen hU v] with x hx hz
        exact tendsto_indicator_sub_indicator_of_tendsto hx fun hvx =>
          congrFun (hz hvx) i
    have hfirst : Tendsto (fun n =>
        eLpNorm ({y | 0 < f n y}.indicator (g n - g₀)) 2 μ) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hgrad i)
        (fun _ => zero_le') (fun n => ?_)
      apply eLpNorm_mono_ae (g := g n - g₀) (((hgMeas n).sub hg₀Meas).indicator₀
        (nullMeasurableSet_lt aemeasurable_const (hfMeas n).aemeasurable))
      filter_upwards with x
      exact norm_indicator_le_norm_self
        (s := {y | 0 < f n y}) (f := g n - g₀) (a := x)
    have hindicatorMeas : ∀ n,
        AEStronglyMeasurable ({y | 0 < f n y}.indicator (g n - g₀)) μ := by
      intro n
      exact ((hgMeas n).sub hg₀Meas).indicator₀
        (nullMeasurableSet_lt aemeasurable_const (hfMeas n).aemeasurable)
    have hRMeas : ∀ n, AEStronglyMeasurable (R n) μ := by
      intro n
      exact (hg₀Meas.indicator₀
        (nullMeasurableSet_lt aemeasurable_const (hfMeas n).aemeasurable)).sub
        (hg₀Meas.indicator₀
          (nullMeasurableSet_lt aemeasurable_const hf₀Meas.aemeasurable))
    have hsum : Tendsto (fun n =>
        eLpNorm ({y | 0 < f n y}.indicator (g n - g₀) + R n) 2 μ)
        atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (by simpa only [zero_add] using hfirst.add hR)
        (fun _ => zero_le') (fun n => eLpNorm_add_le (by norm_num))
    refine hsum.congr' ?_
    filter_upwards with n
    apply eLpNorm_congr_ae
    filter_upwards with x
    simp only [f, f₀, g, g₀, R, Pi.sub_apply, Pi.add_apply, indicator_apply]
    split <;> split <;> simp

end PDE.H1Function
