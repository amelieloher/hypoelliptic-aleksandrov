module

public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelLayer

/-!
# The terminal-layer limit

For a bounded measurable function `m` on `ℝ × E`, vanishing outside `ℝ × K` with `ν K < ∞`,
and having left limits `m₀(w)` at `t = r` for every `w`, the layer averages
`∫ h⁻¹ layerKernel ((r - t)/h) m(t,w)` converge to `∫ m₀ dν` as `h ↓ 0`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open MeasureTheory Set Filter
open scoped Topology

variable {E : Type*} [MeasurableSpace E]

/-- Where the kernel is nonzero, the rescaled argument lies in `(1,2)`. -/
theorem layerKernel_ne_zero_mem {s : ℝ} (h : layerKernel s ≠ 0) : 1 < s ∧ s < 2 := by
  constructor
  · by_contra h1
    exact h (layerKernel_eq_zero_of_le (not_lt.1 h1))
  · by_contra h2
    exact h (layerKernel_eq_zero_of_ge (not_lt.1 h2))

/-- For a fixed `w`, the inner layer integral converges to `m₀ w`. -/
theorem layer_inner_tendsto (r : ℝ) (m : ℝ → ℝ) (hm : Measurable m) (M : ℝ)
    (hM : ∀ t, |m t| ≤ M) (m₀ : ℝ) (hlim : Tendsto m (𝓝[<] r) (𝓝 m₀)) :
    Tendsto (fun h : ℝ => ∫ s, layerKernel s * m (r - h * s)) (𝓝[>] 0) (𝓝 m₀) := by
  have hbound : Integrable (fun s => |layerKernel s| * M) :=
    integrable_layerKernel.norm.mul_const M
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := (volume : Measure ℝ)) (l := 𝓝[>] (0 : ℝ))
    (F := fun (h : ℝ) s => layerKernel s * m (r - h * s)) (f := fun s => layerKernel s * m₀)
    (fun s => |layerKernel s| * M)
    (Eventually.of_forall fun h =>
      (continuous_layerKernel.measurable.mul
        (hm.comp (measurable_const.sub (measurable_const.mul measurable_id)))).aestronglyMeasurable)
    (Eventually.of_forall fun h => Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hM _) (abs_nonneg _))
    hbound
    (Eventually.of_forall fun s => by
      by_cases hs : layerKernel s = 0
      · simp only [hs, zero_mul]
        exact tendsto_const_nhds
      · have hs1 := (layerKernel_ne_zero_mem hs).1
        have : Tendsto (fun h : ℝ => r - h * s) (𝓝[>] 0) (𝓝[<] r) := by
          refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
          · have hc : Continuous fun h : ℝ => r - h * s := by fun_prop
            have := hc.tendsto 0
            simp only [zero_mul, sub_zero] at this
            exact this.mono_left nhdsWithin_le_nhds
          · filter_upwards [self_mem_nhdsWithin] with h hh
            simp only [mem_Iio]
            have : 0 < h * s := mul_pos hh (by linarith)
            linarith
        exact (hlim.comp this).const_mul _)
  simpa [integral_mul_const, integral_layerKernel] using h

/-- **The terminal-layer limit.**  The averages of `m` against the rescaled layer kernel at `t = r`
converge to the integral of the left limit `m₀`. -/
theorem layer_prod_tendsto (ν : Measure E) [SigmaFinite ν] (r : ℝ) (m : ℝ × E → ℝ)
    (hm : Measurable m) (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ q, |m q| ≤ M) (K : Set E)
    (hK : MeasurableSet K) (hKν : ν K < ⊤) (hmK : ∀ t w, w ∉ K → m (t, w) = 0) (m₀ : E → ℝ)
    (hlim : ∀ w, Tendsto (fun t => m (t, w)) (𝓝[<] r) (𝓝 (m₀ w))) :
    Tendsto (fun h : ℝ =>
        ∫ q, h⁻¹ * layerKernel ((r - q.1) / h) * m q ∂((volume : Measure ℝ).prod ν))
      (𝓝[>] 0) (𝓝 (∫ w, m₀ w ∂ν)) := by
  obtain ⟨Mρ, hMρ0, hMρ⟩ := exists_bound_layerKernel
  have hG : ∀ h : ℝ, Measurable (fun q : ℝ × E => h⁻¹ * layerKernel ((r - q.1) / h) * m q) :=
    fun h => (measurable_const.mul (continuous_layerKernel.measurable.comp
      ((measurable_const.sub measurable_fst).div_const h))).mul hm
  have hGint : ∀ h : ℝ, 0 < h →
      Integrable (fun q : ℝ × E => h⁻¹ * layerKernel ((r - q.1) / h) * m q)
        ((volume : Measure ℝ).prod ν) := by
    intro h hh
    have h1 : Integrable ((Icc (r - 2 * h) (r - h)).indicator (fun _ => (1 : ℝ))) :=
      (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp))
    have h2 : Integrable (K.indicator (fun _ => (1 : ℝ))) ν :=
      (integrable_indicator_iff hK).2 (integrableOn_const hKν.ne)
    have h3 := (h1.mul_prod h2).const_mul (h⁻¹ * Mρ * M)
    refine h3.mono' (hG h).aestronglyMeasurable (Eventually.of_forall fun q => ?_)
    have hb0 : 0 ≤ (h⁻¹ * Mρ * M) * ((Icc (r - 2 * h) (r - h)).indicator (fun _ => (1 : ℝ)) q.1 *
        K.indicator (fun _ => (1 : ℝ)) q.2) :=
      mul_nonneg (by positivity) (mul_nonneg (indicator_nonneg (fun _ _ => zero_le_one) _)
        (indicator_nonneg (fun _ _ => zero_le_one) _))
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    by_cases hw : q.2 ∈ K
    · by_cases ht : layerKernel ((r - q.1) / h) = 0
      · rw [ht, abs_zero, mul_zero, zero_mul]
        exact hb0
      · have hmem := layerKernel_ne_zero_mem ht
        have hq1 : q.1 ∈ Icc (r - 2 * h) (r - h) := by
          obtain ⟨a1, a2⟩ := hmem
          rw [lt_div_iff₀ hh] at a1
          rw [div_lt_iff₀ hh] at a2
          constructor <;> linarith
        simp only [indicator_of_mem hq1, indicator_of_mem hw, mul_one, abs_inv, abs_of_pos hh]
        gcongr
        · exact hMρ _
        · exact hM q
    · rw [hmK q.1 q.2 hw, abs_zero, mul_zero]
      exact hb0
  have hEq : ∀ h : ℝ, 0 < h →
      ∫ q, h⁻¹ * layerKernel ((r - q.1) / h) * m q ∂((volume : Measure ℝ).prod ν) =
        ∫ w, ∫ s, layerKernel s * m (r - h * s, w) ∂volume ∂ν := by
    intro h hh
    rw [integral_prod_symm _ (hGint h hh)]
    congr 1
    funext w
    exact integral_layer_substitution r h hh (fun t => m (t, w))
  have hΦ : Tendsto (fun h : ℝ => ∫ w, ∫ s, layerKernel s * m (r - h * s, w) ∂volume ∂ν)
      (𝓝[>] 0) (𝓝 (∫ w, m₀ w ∂ν)) := by
    have hdom := tendsto_integral_filter_of_dominated_convergence
      (μ := ν) (l := 𝓝[>] (0 : ℝ))
      (F := fun (h : ℝ) w => ∫ s, layerKernel s * m (r - h * s, w) ∂volume) (f := m₀)
      (fun w => ((∫ s, |layerKernel s|) * M) * K.indicator (fun _ => (1 : ℝ)) w)
      (Eventually.of_forall fun h => by
        have hm' : Measurable (fun q : ℝ × E => layerKernel q.1 * m (r - h * q.1, q.2)) :=
          (continuous_layerKernel.measurable.comp measurable_fst).mul
            (hm.comp ((measurable_const.sub (measurable_const.mul measurable_fst)).prodMk
              measurable_snd))
        exact (hm'.stronglyMeasurable.integral_prod_left' (μ := (volume : Measure ℝ))
          ).aestronglyMeasurable)
      (Eventually.of_forall fun h => Eventually.of_forall fun w => by
        by_cases hw : w ∈ K
        · simp only [indicator_of_mem hw, mul_one]
          calc ‖∫ s, layerKernel s * m (r - h * s, w)‖
              ≤ ∫ s, ‖layerKernel s * m (r - h * s, w)‖ := norm_integral_le_integral_norm _
            _ ≤ ∫ s, |layerKernel s| * M := by
              apply integral_mono_of_nonneg (Eventually.of_forall fun s => norm_nonneg _)
                (integrable_layerKernel.norm.mul_const M)
              exact Eventually.of_forall fun s => by
                dsimp only
                rw [Real.norm_eq_abs, abs_mul]
                exact mul_le_mul_of_nonneg_left (hM _) (abs_nonneg _)
            _ = (∫ s, |layerKernel s|) * M := by rw [integral_mul_const]
        · simp only [hmK _ _ hw, mul_zero, integral_zero, norm_zero, indicator_of_notMem hw]
          exact le_rfl)
      (((integrable_indicator_iff hK).2 (integrableOn_const hKν.ne)).const_mul _)
      (Eventually.of_forall fun w => layer_inner_tendsto r (fun t => m (t, w))
        (hm.comp (measurable_id.prodMk measurable_const)) M (fun t => hM _) (m₀ w) (hlim w))
    exact hdom
  refine hΦ.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact (hEq h hh).symm

/-- The smooth step tends to one at `+∞`. -/
theorem tendsto_layerStep_atTop : Tendsto layerStep atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [Ici_mem_atTop (2 : ℝ)] with y hy using (layerStep_of_ge hy).symm

section Identity

variable [TopologicalSpace E] [BorelSpace E] [T2Space E] [SecondCountableTopology E]
  (ν : Measure E) [SigmaFinite ν] [IsFiniteMeasureOnCompacts ν]

/-- **Terminal-layer identity.**  If the cut-off weak identities hold for every layer width `h`,
then in the limit the weak identity holds on the open slab `t < r`, with the terminal trace
`m₀` as boundary term. -/
theorem layer_slice_identity (r : ℝ) (U Ψ Λ : ℝ × E → ℝ) (hU : Measurable U) (C : ℝ)
    (hC0 : 0 ≤ C) (hUb : ∀ q, |U q| ≤ C) (hΨ : Continuous Ψ) (hΨc : HasCompactSupport Ψ)
    (hΛ : Continuous Λ) (hΛc : HasCompactSupport Λ)
    (hI : ∀ h : ℝ, 0 < h →
      ∫ q, layerStep ((r - q.1) / h) * (U q * Λ q) ∂((volume : Measure ℝ).prod ν) +
        ∫ q, h⁻¹ * layerKernel ((r - q.1) / h) * (U q * Ψ q)
          ∂((volume : Measure ℝ).prod ν) = 0)
    (m₀ : E → ℝ)
    (hlim : ∀ w, Tendsto (fun t => U (t, w) * Ψ (t, w)) (𝓝[<] r) (𝓝 (m₀ w))) :
    ∫ q, {q : ℝ × E | q.1 < r}.indicator (fun q => U q * Λ q) q
        ∂((volume : Measure ℝ).prod ν) + ∫ w, m₀ w ∂ν = 0 := by
  obtain ⟨MΨ, hMΨ⟩ := hΨ.bounded_above_of_compact_support hΨc
  have hMΨ0 : 0 ≤ max MΨ 0 := le_max_right _ _
  have hKc : IsCompact (Prod.snd '' tsupport Ψ) := hΨc.image continuous_snd
  have hmeasΛ : Measurable Λ := hΛ.measurable
  have hΛint : Integrable Λ ((volume : Measure ℝ).prod ν) := by
    have : Integrable Λ (volume.prod ν) := hΛ.integrable_of_hasCompactSupport hΛc
    exact this
  have h1 : Tendsto (fun h : ℝ => ∫ q, layerStep ((r - q.1) / h) * (U q * Λ q)
      ∂((volume : Measure ℝ).prod ν)) (𝓝[>] 0)
      (𝓝 (∫ q, {q : ℝ × E | q.1 < r}.indicator (fun q => U q * Λ q) q
        ∂((volume : Measure ℝ).prod ν))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (μ := (volume : Measure ℝ).prod ν) (l := 𝓝[>] (0 : ℝ))
      (F := fun (h : ℝ) q => layerStep ((r - q.1) / h) * (U q * Λ q))
      (f := {q : ℝ × E | q.1 < r}.indicator (fun q => U q * Λ q))
      (fun q => C * |Λ q|) ?_ ?_ ?_ ?_
    · refine Eventually.of_forall fun h => ?_
      exact ((contDiff_layerStep.continuous.measurable.comp
        ((measurable_const.sub measurable_fst).div_const h)).mul
          (hU.mul hmeasΛ)).aestronglyMeasurable
    · refine Eventually.of_forall fun h => Eventually.of_forall fun q => ?_
      have h0 : 0 ≤ layerStep ((r - q.1) / h) := Real.smoothTransition.nonneg _
      have h1 : layerStep ((r - q.1) / h) ≤ 1 := Real.smoothTransition.le_one _
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg h0]
      have := hUb q
      calc layerStep ((r - q.1) / h) * (|U q| * |Λ q|) ≤ 1 * (C * |Λ q|) := by
            gcongr
        _ = C * |Λ q| := one_mul _
    · exact (hΛint.norm.const_mul C)
    · refine Eventually.of_forall fun q => ?_
      by_cases hq : q.1 < r
      · rw [indicator_of_mem (show q ∈ {q : ℝ × E | q.1 < r} from hq)]
        have ht : Tendsto (fun h : ℝ => (r - q.1) / h) (𝓝[>] 0) atTop := by
          simp only [div_eq_mul_inv]
          exact tendsto_inv_nhdsGT_zero.const_mul_atTop (sub_pos.2 hq)
        have := (tendsto_layerStep_atTop.comp ht).mul_const (U q * Λ q)
        simpa using this
      · rw [indicator_of_notMem (show q ∉ {q : ℝ × E | q.1 < r} from hq)]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with h hh
        have : (r - q.1) / h ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (by linarith [not_lt.1 hq]) (le_of_lt hh)
        rw [layerStep_of_le (by linarith)]
        simp
  have hKm : MeasurableSet (Prod.snd '' tsupport Ψ) := hKc.isClosed.measurableSet
  have h2 := layer_prod_tendsto ν r (fun q => U q * Ψ q) (hU.mul hΨ.measurable)
    (C * max MΨ 0) (mul_nonneg hC0 hMΨ0)
    (fun q => by
      rw [abs_mul]
      refine mul_le_mul (hUb q) ?_ (abs_nonneg _) hC0
      simpa only [Real.norm_eq_abs] using (hMΨ q).trans (le_max_left _ _))
    (Prod.snd '' tsupport Ψ) hKm hKc.measure_lt_top
    (fun t w hw => by
      have : Ψ (t, w) = 0 := image_eq_zero_of_notMem_tsupport (fun h => hw ⟨_, h, rfl⟩)
      simp [this])
    m₀ hlim
  have h3 := h1.add h2
  have h4 : Tendsto (fun h : ℝ =>
      ∫ q, layerStep ((r - q.1) / h) * (U q * Λ q) ∂((volume : Measure ℝ).prod ν) +
        ∫ q, h⁻¹ * layerKernel ((r - q.1) / h) * (U q * Ψ q)
          ∂((volume : Measure ℝ).prod ν)) (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact (hI h hh).symm
  exact tendsto_nhds_unique h3 h4

end Identity

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
