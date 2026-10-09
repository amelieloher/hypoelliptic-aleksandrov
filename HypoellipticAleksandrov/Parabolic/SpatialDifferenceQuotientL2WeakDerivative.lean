module

public import HypoellipticAleksandrov.Parabolic.SpatialDifferenceQuotientL2Transpose
public import HypoellipticAleksandrov.Parabolic.SpatialDifferenceQuotientPairingLimit
public import HypoellipticAleksandrov.Parabolic.Dirichlet.HilbertWeakSequentialCompactnessCLM
public import HypoellipticAleksandrov.Topology.WeakLimitNorm
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Uniform spatial difference quotients and weak velocity derivatives

This module turns a positive-step uniform interior `L²` difference-quotient
bound into a restricted-`L²` weak velocity derivative.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter MeasureTheory Set
open scoped ENNReal Topology

/-- A positive-step family of spatial difference quotients uniformly bounded by
`C` has an `L²` weak velocity-partial limit whose norm is at most `C`. -/
theorem exists_hasWeakVelocityPartialDerivOn_norm_le_of_uniform_spatialDifferenceQuotient
    {d : ℕ} (U : Set (TimeVelocity d)) (hU : IsOpen U)
    (k : Fin d) (u : TimeVelocity d → ℝ)
    (hu : ParabolicMemLpOn U (2 : ℝ≥0∞) u)
    (δ C : ℝ) (hδ : 0 < δ)
    (hDQmem : ∀ h : ℝ, 0 < h → h < δ →
      ParabolicMemLpOn U (2 : ℝ≥0∞)
        (spatialDifferenceQuotient k h u))
    (hDQbound : ∀ (h : ℝ) (hh0 : 0 < h) (hhδ : h < δ),
      ‖(hDQmem h hh0 hhδ).toLp
        (spatialDifferenceQuotient k h u)‖ ≤ C) :
    ∃ g : TimeVelocity d → ℝ,
      ∃ hg : ParabolicMemLpOn U (2 : ℝ≥0∞) g,
        HasWeakVelocityPartialDerivOn U k u g ∧
          ‖hg.toLp g‖ ≤ C := by
  let μ : Measure (TimeVelocity d) := timeVelocityVolumeOn U
  letI : IsLocallyFiniteMeasure μ :=
    Measure.isLocallyFiniteMeasure_of_le Measure.restrict_le_self
  have huLoc : LocallyIntegrableOn u U (volume : Measure (TimeVelocity d)) := by
    exact locallyIntegrableOn_of_locallyIntegrable_restrict
      (hu.locallyIntegrable (by norm_num))
  let a : ℕ → ℝ := fun n => δ / ((n + 2 : ℕ) : ℝ)
  have ha_pos : ∀ n, 0 < a n := by
    intro n
    dsimp [a]
    positivity
  have ha_lt : ∀ n, a n < δ := by
    intro n
    dsimp [a]
    have hdenNat : 1 < n + 2 := by omega
    have hden : 1 < ((n + 2 : ℕ) : ℝ) := by exact_mod_cast hdenNat
    rw [div_lt_iff₀ (by positivity : 0 < ((n + 2 : ℕ) : ℝ))]
    nlinarith
  have ha_tendsto : Tendsto a atTop (𝓝[≠] 0) := by
    apply (tendsto_nhdsWithin_iff).2
    constructor
    · simpa only [Function.comp_def, a] using (tendsto_const_div_atTop_nhds_zero_nat δ).comp
        (tendsto_add_atTop_nat 2)
    · filter_upwards with n
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using (ne_of_gt (ha_pos n))
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  letI : IsSeparable μ := by infer_instance
  let H := Lp ℝ (2 : ℝ≥0∞) μ
  let q : ℕ → H := fun n =>
    (hDQmem (a n) (ha_pos n) (ha_lt n)).toLp
      (spatialDifferenceQuotient k (a n) u)
  have hq_bound : ∀ n, ‖q n‖ ≤ C := by
    intro n
    simpa only [q] using hDQbound (a n) (ha_pos n) (ha_lt n)
  obtain ⟨v, σ, hσ, hweak⟩ :=
    Dirichlet.exists_strictMono_tendsto_clm_of_norm_le q C hq_bound
  have hv_norm : ‖v‖ ≤ C :=
    HypoellipticAleksandrov.norm_le_of_tendsto_clm_of_norm_le
      (fun n => q (σ n)) v C (fun n => hq_bound (σ n)) hweak
  have haσ_tendsto : Tendsto (a ∘ σ) atTop (𝓝[≠] 0) :=
    ha_tendsto.comp hσ.tendsto_atTop
  let hg : ParabolicMemLpOn U (2 : ℝ≥0∞) (fun z => v z) := Lp.memLp v
  refine ⟨fun z => v z, hg, ?_, ?_⟩
  intro φ hφ hφcompact hφU
  let φLp : H := (hφ.continuous.memLp_of_hasCompactSupport hφcompact).toLp φ
  let ell : H →L[ℝ] ℝ := InnerProductSpace.toDual ℝ H φLp
  have hq_ae : ∀ n, (q n : TimeVelocity d → ℝ) =ᵐ[μ]
      spatialDifferenceQuotient k (a n) u := by
    intro n
    exact (hDQmem (a n) (ha_pos n) (ha_lt n)).coeFn_toLp
  have hφ_ae : (φLp : TimeVelocity d → ℝ) =ᵐ[μ] φ := by
    exact (hφ.continuous.memLp_of_hasCompactSupport hφcompact).coeFn_toLp
  have hellq : ∀ n, ell (q (σ n)) =
      ∫ z in U, spatialDifferenceQuotient k (a (σ n)) u z * φ z
        ∂(volume : Measure (TimeVelocity d)) := by
    intro n
    change inner ℝ φLp (q (σ n)) = _
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hq_ae (σ n), hφ_ae] with z hzq hzφ
    rw [hzq, hzφ]
    simp [mul_comm]
  have hellv : ell v = ∫ z in U, v z * φ z ∂(volume : Measure (TimeVelocity d)) := by
    change inner ℝ φLp v = _
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hφ_ae] with z hzφ
    rw [hzφ]
    simp [mul_comm]
  have hpair : Tendsto
      (fun n => ∫ z in U, spatialDifferenceQuotient k (a (σ n)) u z * φ z
        ∂(volume : Measure (TimeVelocity d))) atTop
      (𝓝 (∫ z in U, v z * φ z ∂(volume : Measure (TimeVelocity d)))) := by
    rw [← hellv]
    exact (hweak ell).congr' (Filter.Eventually.of_forall hellq)
  obtain ⟨ε, hε, -, hshift⟩ :=
    IsCompact.exists_spatialShift_cthickening_collar hφcompact.isCompact hU hφU
  have haσ_nhds : Tendsto (a ∘ σ) atTop (𝓝 0) :=
    (tendsto_nhdsWithin_iff.mp haσ_tendsto).1
  have hevent_shift : ∀ᶠ n in atTop,
      Set.MapsTo (spatialShift k (a (σ n))) (tsupport φ) U := by
    filter_upwards [haσ_nhds.eventually (Metric.ball_mem_nhds 0 hε)] with n hn
    apply hshift k (a (σ n))
    simpa only [Function.comp_def, Metric.mem_ball, Real.dist_eq, sub_zero] using le_of_lt hn
  have htranspose :
      (fun n => ∫ z in U, spatialDifferenceQuotient k (a (σ n)) u z * φ z
        ∂(volume : Measure (TimeVelocity d))) =ᶠ[atTop]
      fun n => -∫ z in U,
        u z * spatialDifferenceQuotient k (-(a (σ n))) φ z
          ∂(volume : Measure (TimeVelocity d)) := by
    filter_upwards [hevent_shift] with n hn
    exact setIntegral_spatialDifferenceQuotient_mul_eq_neg_mul_spatialDifferenceQuotient_neg
      U k (a (σ n)) u φ hu hφ.continuous hφcompact hφU hn
  have hback := tendsto_setIntegral_mul_backwardSpatialDifferenceQuotient
    hU u φ huLoc (hφ.of_le (by norm_num)) hφcompact hφU k
  have hbackσ := hback.comp haσ_tendsto
  have hback_eq : (fun n => -∫ z in U,
      u z * spatialDifferenceQuotient k (-(a (σ n))) φ z
        ∂(volume : Measure (TimeVelocity d))) =ᶠ[atTop]
      fun n => ∫ z in U, u z *
        ((φ (spatialShift k (-(a (σ n))) z) - φ z) / (a (σ n)))
          ∂(volume : Measure (TimeVelocity d)) := by
    filter_upwards with n
    rw [← integral_neg]
    congr with z
    simp only [spatialDifferenceQuotient_apply, spatialTranslate_apply]
    ring
  have hback_limit : Tendsto (fun n => -∫ z in U,
      u z * spatialDifferenceQuotient k (-(a (σ n))) φ z
        ∂(volume : Measure (TimeVelocity d))) atTop
      (𝓝 (-∫ z in U, u z * velocityGradient φ z k
        ∂(volume : Measure (TimeVelocity d)))) := by
    exact hbackσ.congr' hback_eq.symm
  have hlimit := tendsto_nhds_unique hpair (hback_limit.congr' htranspose.symm)
  linarith
  · simpa only [hg, Lp.toLp_coeFn] using hv_norm

/-- A positive-step, uniformly `L²`-bounded family of spatial difference
quotients has an `L²` weak velocity-partial limit on an open time--velocity set. -/
theorem exists_hasWeakVelocityPartialDerivOn_of_uniform_spatialDifferenceQuotient
    {d : ℕ} (U : Set (TimeVelocity d)) (hU : IsOpen U)
    (k : Fin d) (u : TimeVelocity d → ℝ)
    (hu : ParabolicMemLpOn U (2 : ℝ≥0∞) u)
    (δ C : ℝ) (hδ : 0 < δ)
    (hDQmem : ∀ h : ℝ, 0 < h → h < δ →
      ParabolicMemLpOn U (2 : ℝ≥0∞)
        (spatialDifferenceQuotient k h u))
    (hDQbound : ∀ (h : ℝ) (hh0 : 0 < h) (hhδ : h < δ),
      ‖(hDQmem h hh0 hhδ).toLp
        (spatialDifferenceQuotient k h u)‖ ≤ C) :
    ∃ g : TimeVelocity d → ℝ,
      ParabolicMemLpOn U (2 : ℝ≥0∞) g ∧
      HasWeakVelocityPartialDerivOn U k u g := by
  obtain ⟨g, hg, hweak, -⟩ :=
    exists_hasWeakVelocityPartialDerivOn_norm_le_of_uniform_spatialDifferenceQuotient
      U hU k u hu δ C hδ hDQmem hDQbound
  exact ⟨g, hg, hweak⟩

end HypoellipticAleksandrov.Parabolic
