module

public import HypoellipticAleksandrov.Parabolic.SmoothGradientTimeEnergy
public import HypoellipticAleksandrov.Parabolic.TimeVelocitySmoothCompactPlateau
public import HypoellipticAleksandrov.Parabolic.WeakDerivativesCompactGlobalization
public import HypoellipticAleksandrov.Parabolic.WeakDerivativeSpacetimeMollification
public import HypoellipticAleksandrov.Parabolic.SpacetimeMollifierL2
public import HypoellipticAleksandrov.Analysis.L2ProductConvergence
public import HypoellipticAleksandrov.Parabolic.WeakJetProduct

/-!
# Weak gradient time-energy identity

This file begins the compatible localization of the selected weak spacetime
jet used in the weak gradient time-energy identity.
-/

@[expose] public section

noncomputable section

open Function MeasureTheory Set
open scoped ENNReal Topology

namespace HypoellipticAleksandrov.Parabolic.WeakGradientTimeEnergy

/-- Strong global `L²` convergence descends to every restricted carrier,
without a measurability or finite-measure assumption on the carrier. -/
private theorem tendsto_eLpNorm_two_restrict_of_global
    {d : ℕ} {l : Filter ℝ} (S : Set (TimeVelocity d))
    (f : ℝ → TimeVelocity d → ℝ) (f₀ : TimeVelocity d → ℝ)
    (h : Filter.Tendsto
      (fun a => eLpNorm (fun z => f a z - f₀ z) (2 : ℝ≥0∞)
        (volume : Measure (TimeVelocity d))) l (𝓝 0)) :
    Filter.Tendsto
      (fun a => eLpNorm (fun z => f a z - f₀ z) (2 : ℝ≥0∞)
        ((volume : Measure (TimeVelocity d)).restrict S)) l (𝓝 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds h
    (Filter.Eventually.of_forall fun _ => bot_le)
    (Filter.Eventually.of_forall fun a =>
      eLpNorm_mono_measure (fun z => f a z - f₀ z) Measure.restrict_le_self)

/-- After restriction, multiplication by a fixed `L∞` field preserves
strong `L²` convergence. -/
private theorem tendsto_eLpNorm_two_mul_restrict
    {d : ℕ} {l : Filter ℝ} (S : Set (TimeVelocity d))
    (c : TimeVelocity d → ℝ)
    (f : ℝ → TimeVelocity d → ℝ) (f₀ : TimeVelocity d → ℝ)
    (hc : MemLp c ∞ ((volume : Measure (TimeVelocity d)).restrict S))
    (h : Filter.Tendsto
      (fun a => eLpNorm (fun z => f a z - f₀ z) (2 : ℝ≥0∞)
        ((volume : Measure (TimeVelocity d)).restrict S)) l (𝓝 0)) :
    Filter.Tendsto
      (fun a => eLpNorm (fun z => c z * f a z - c z * f₀ z)
        (2 : ℝ≥0∞) ((volume : Measure (TimeVelocity d)).restrict S))
      l (𝓝 0) := by
  exact HypoellipticAleksandrov.Analysis.tendsto_eLpNorm_mul_sub_mul_of_tendsto_eLpNorm_two
    c f f₀ hc h

/-- Restricted scalar-product integrals converge when both factors converge
strongly in restricted `L²` and have the corresponding eventual membership. -/
private theorem tendsto_integral_mul_restrict
    {d : ℕ} {l : Filter ℝ} (S : Set (TimeVelocity d))
    (f g : ℝ → TimeVelocity d → ℝ)
    (f₀ g₀ : TimeVelocity d → ℝ)
    (hf : ∀ᶠ a in l, MemLp (f a) (2 : ℝ≥0∞)
      ((volume : Measure (TimeVelocity d)).restrict S))
    (hg : ∀ᶠ a in l, MemLp (g a) (2 : ℝ≥0∞)
      ((volume : Measure (TimeVelocity d)).restrict S))
    (hf₀ : MemLp f₀ (2 : ℝ≥0∞)
      ((volume : Measure (TimeVelocity d)).restrict S))
    (hg₀ : MemLp g₀ (2 : ℝ≥0∞)
      ((volume : Measure (TimeVelocity d)).restrict S))
    (hft : Filter.Tendsto
      (fun a => eLpNorm (fun z => f a z - f₀ z) (2 : ℝ≥0∞)
        ((volume : Measure (TimeVelocity d)).restrict S)) l (𝓝 0))
    (hgt : Filter.Tendsto
      (fun a => eLpNorm (fun z => g a z - g₀ z) (2 : ℝ≥0∞)
        ((volume : Measure (TimeVelocity d)).restrict S)) l (𝓝 0)) :
    Filter.Tendsto
      (fun a => ∫ z in S, f a z * g a z ∂volume)
      l (𝓝 (∫ z in S, f₀ z * g₀ z ∂volume)) := by
  exact HypoellipticAleksandrov.Analysis.tendsto_integral_mul_of_tendsto_eLpNorm_two
    f g f₀ g₀ hf hg hf₀ hg₀ hft hgt

/-- A fixed bounded coefficient may be absorbed into the first factor of a
restricted `L² × L²` product limit. -/
private theorem tendsto_integral_fixed_mul_mul_restrict
    {d : ℕ} {l : Filter ℝ} (S : Set (TimeVelocity d))
    (c : TimeVelocity d → ℝ)
    (f g : ℝ → TimeVelocity d → ℝ)
    (f₀ g₀ : TimeVelocity d → ℝ)
    (hc : MemLp c ∞ ((volume : Measure (TimeVelocity d)).restrict S))
    (hf : ∀ᶠ a in l, MemLp (f a) (2 : ℝ≥0∞)
      ((volume : Measure (TimeVelocity d)).restrict S))
    (hg : ∀ᶠ a in l, MemLp (g a) (2 : ℝ≥0∞)
      ((volume : Measure (TimeVelocity d)).restrict S))
    (hf₀ : MemLp f₀ (2 : ℝ≥0∞)
      ((volume : Measure (TimeVelocity d)).restrict S))
    (hg₀ : MemLp g₀ (2 : ℝ≥0∞)
      ((volume : Measure (TimeVelocity d)).restrict S))
    (hft : Filter.Tendsto
      (fun a => eLpNorm (fun z => f a z - f₀ z) (2 : ℝ≥0∞)
        ((volume : Measure (TimeVelocity d)).restrict S)) l (𝓝 0))
    (hgt : Filter.Tendsto
      (fun a => eLpNorm (fun z => g a z - g₀ z) (2 : ℝ≥0∞)
        ((volume : Measure (TimeVelocity d)).restrict S)) l (𝓝 0)) :
    Filter.Tendsto
      (fun a => ∫ z in S, c z * f a z * g a z ∂volume)
      l (𝓝 (∫ z in S, c z * f₀ z * g₀ z ∂volume)) := by
  have hcf : ∀ᶠ a in l, MemLp (fun z => c z * f a z) (2 : ℝ≥0∞)
      ((volume : Measure (TimeVelocity d)).restrict S) := by
    filter_upwards [hf] with a hfa
    simpa only [mul_comm] using hfa.mul' hc
  have hcf₀ : MemLp (fun z => c z * f₀ z) (2 : ℝ≥0∞)
      ((volume : Measure (TimeVelocity d)).restrict S) := by
    simpa only [mul_comm] using hf₀.mul' hc
  have hcft := tendsto_eLpNorm_two_mul_restrict S c f f₀ hc hft
  exact tendsto_integral_mul_restrict S
    (fun a z => c z * f a z) g (fun z => c z * f₀ z) g₀
    hcf hg hcf₀ hg₀ hcft hgt

/-- Coordinatewise scalar limits assemble over the exact finite coordinate
set, including the empty `Fin 0` case. -/
private theorem tendsto_sum_coordinates
    {d : ℕ} {l : Filter ℝ} (F : Fin d → ℝ → ℝ)
    (F₀ : Fin d → ℝ)
    (hF : ∀ i : Fin d, Filter.Tendsto (F i) l (𝓝 (F₀ i))) :
    Filter.Tendsto (fun a => ∑ i : Fin d, F i a) l
      (𝓝 (∑ i : Fin d, F₀ i)) := by
  exact tendsto_finset_sum Finset.univ fun i _ => hF i

/-- A separated spacetime multiplier is globally bounded when both its time
and spatial factors are continuous and compactly supported.  In particular,
compactness is never falsely attributed to the time factor pulled back alone. -/
private theorem separated_multiplier_memLp_top_restrict
    {d : ℕ} (S : Set (TimeVelocity d))
    (a : ℝ → ℝ) (ha : Continuous a) (haCompact : HasCompactSupport a)
    (c : PDE.Vec d → ℝ) (hc : Continuous c) (hcCompact : HasCompactSupport c) :
    MemLp (fun z : TimeVelocity d => a z.1 * c z.2) ∞
      ((volume : Measure (TimeVelocity d)).restrict S) := by
  have hcont : Continuous (fun z : TimeVelocity d => a z.1 * c z.2) :=
    (ha.comp continuous_fst).mul (hc.comp continuous_snd)
  have hcompact : HasCompactSupport (fun z : TimeVelocity d => a z.1 * c z.2) := by
    have hprod : IsCompact (tsupport a ×ˢ tsupport c) :=
      haCompact.isCompact.prod hcCompact.isCompact
    apply HasCompactSupport.of_support_subset_isCompact hprod
    intro z hz
    have ha0 : a z.1 ≠ 0 := by
      intro hzero
      exact hz (by simp [hzero])
    have hc0 : c z.2 ≠ 0 := by
      intro hzero
      exact hz (by simp [hzero])
    exact ⟨subset_tsupport a (Function.mem_support.mpr ha0),
      subset_tsupport c (Function.mem_support.mpr hc0)⟩
  exact (hcont.memLp_of_hasCompactSupport hcompact).restrict S

/-- The three literal coefficients in the coordinatewise energy limits are
bounded on every restricted carrier, with compactness supplied in both time
and velocity variables. -/
private theorem concrete_energy_multipliers_memLp_top
    {d : ℕ} (S : Set (TimeVelocity d))
    (η : PDE.Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηCompact : HasCompactSupport η)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζCompact : HasCompactSupport ζ) :
    (∀ i : Fin d, MemLp
      (fun z : TimeVelocity d => (-2 : ℝ) * ζ z.1 *
        (η z.2 * spatialPartial i η z.2)) ∞
      ((volume : Measure (TimeVelocity d)).restrict S)) ∧
    MemLp (fun z : TimeVelocity d => (-1 : ℝ) * ζ z.1 * η z.2 ^ 2) ∞
      ((volume : Measure (TimeVelocity d)).restrict S) ∧
    MemLp (fun z : TimeVelocity d => _root_.deriv ζ z.1 * η z.2 ^ 2) ∞
      ((volume : Measure (TimeVelocity d)).restrict S) := by
  have hpartialCont (i : Fin d) : Continuous (spatialPartial i η) := by
    unfold spatialPartial
    simpa using (hη.continuous_fderiv (by simp)).clm_apply continuous_const
  have hpartialCompact (i : Fin d) : HasCompactSupport (spatialPartial i η) := by
    unfold spatialPartial
    simpa using hηCompact.fderiv_apply (𝕜 := ℝ) (PDE.basisVec i)
  have hderivCont : Continuous (_root_.deriv ζ) := by
    rw [← show (fun t => (fderiv ℝ ζ t : ℝ → ℝ) 1) = _root_.deriv ζ by
      funext t
      exact fderiv_apply_one_eq_deriv]
    exact (hζ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hderivCompact : HasCompactSupport (_root_.deriv ζ) := by
    rw [← show (fun t => (fderiv ℝ ζ t : ℝ → ℝ) 1) = _root_.deriv ζ by
      funext t
      exact fderiv_apply_one_eq_deriv]
    exact hζCompact.fderiv_apply ℝ 1
  have hetaSqCont : Continuous (fun v => η v ^ 2) := hη.continuous.pow 2
  have hetaSqCompact : HasCompactSupport (fun v => η v ^ 2) := by
    simpa only [pow_two, Pi.mul_def] using hηCompact.mul_right (f' := η)
  constructor
  · intro i
    have hspatialCont : Continuous (fun v => η v * spatialPartial i η v) :=
      hη.continuous.mul (hpartialCont i)
    have hspatialCompact : HasCompactSupport
        (fun v => η v * spatialPartial i η v) :=
      hηCompact.mul_right
    have hbase := separated_multiplier_memLp_top_restrict S ζ hζ.continuous
      hζCompact _ hspatialCont hspatialCompact
    have hscaled := hbase.const_smul (-2 : ℝ)
    convert hscaled using 1
    funext z
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  constructor
  · have hbase := separated_multiplier_memLp_top_restrict S ζ hζ.continuous
      hζCompact _ hetaSqCont hetaSqCompact
    have hscaled := hbase.const_smul (-1 : ℝ)
    convert hscaled using 1
    funext z
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · exact separated_multiplier_memLp_top_restrict S _ hderivCont hderivCompact
      _ hetaSqCont hetaSqCompact

private theorem eventually_spacetimeMollification_memLp_restrict
    {d : ℕ} (S : Set (TimeVelocity d)) (f : TimeVelocity d → ℝ)
    (hf : MemLp f (2 : ℝ≥0∞) (volume : Measure (TimeVelocity d))) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, MemLp
      (SpacetimeMollifier.spacetimeMollification ε f) (2 : ℝ≥0∞)
      ((volume : Measure (TimeVelocity d)).restrict S) := by
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (SpacetimeMollifierL2.spacetimeMollification_memLp hε f hf).restrict S

/-- The three literal coordinate products used by the weak energy identity
converge for the common positive-radius spacetime mollifier. -/
private theorem coordinate_energy_product_limits
    {d : ℕ} (S : Set (TimeVelocity d))
    (η : PDE.Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηCompact : HasCompactSupport η)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζCompact : HasCompactSupport ζ)
    (rt : TimeVelocity d → ℝ)
    (ri rii : Fin d → TimeVelocity d → ℝ)
    (hrt : MemLp rt (2 : ℝ≥0∞) volume)
    (hri : ∀ i, MemLp (ri i) (2 : ℝ≥0∞) volume)
    (hrii : ∀ i, MemLp (rii i) (2 : ℝ≥0∞) volume)
    (i : Fin d) :
    Filter.Tendsto (fun ε : ℝ => ∫ z in S,
        ((-2 : ℝ) * ζ z.1 * (η z.2 * spatialPartial i η z.2)) *
          SpacetimeMollifier.spacetimeMollification ε rt z *
          SpacetimeMollifier.spacetimeMollification ε (ri i) z ∂volume)
      (𝓝[>] 0) (𝓝 (∫ z in S,
        ((-2 : ℝ) * ζ z.1 * (η z.2 * spatialPartial i η z.2)) *
          rt z * ri i z ∂volume)) ∧
    Filter.Tendsto (fun ε : ℝ => ∫ z in S,
        ((-1 : ℝ) * ζ z.1 * η z.2 ^ 2) *
          SpacetimeMollifier.spacetimeMollification ε rt z *
          SpacetimeMollifier.spacetimeMollification ε (rii i) z ∂volume)
      (𝓝[>] 0) (𝓝 (∫ z in S,
        ((-1 : ℝ) * ζ z.1 * η z.2 ^ 2) * rt z * rii i z ∂volume)) ∧
    Filter.Tendsto (fun ε : ℝ => ∫ z in S,
        (_root_.deriv ζ z.1 * η z.2 ^ 2) *
          SpacetimeMollifier.spacetimeMollification ε (ri i) z *
          SpacetimeMollifier.spacetimeMollification ε (ri i) z ∂volume)
      (𝓝[>] 0) (𝓝 (∫ z in S,
        (_root_.deriv ζ z.1 * η z.2 ^ 2) * ri i z * ri i z ∂volume)) := by
  rcases concrete_energy_multipliers_memLp_top S η hη hηCompact ζ hζ hζCompact with
    ⟨hc₁, hc₂, hc₃⟩
  have hrtE := eventually_spacetimeMollification_memLp_restrict S rt hrt
  have hriE := eventually_spacetimeMollification_memLp_restrict S (ri i) (hri i)
  have hriiE := eventually_spacetimeMollification_memLp_restrict S (rii i) (hrii i)
  have hrtR := hrt.restrict S
  have hriR := (hri i).restrict S
  have hriiR := (hrii i).restrict S
  have hrtT := tendsto_eLpNorm_two_restrict_of_global S
    (fun ε => SpacetimeMollifier.spacetimeMollification ε rt) rt
    (SpacetimeMollifierL2.tendsto_eLpNorm_spacetimeMollification_sub rt hrt)
  have hriT := tendsto_eLpNorm_two_restrict_of_global S
    (fun ε => SpacetimeMollifier.spacetimeMollification ε (ri i)) (ri i)
    (SpacetimeMollifierL2.tendsto_eLpNorm_spacetimeMollification_sub (ri i) (hri i))
  have hriiT := tendsto_eLpNorm_two_restrict_of_global S
    (fun ε => SpacetimeMollifier.spacetimeMollification ε (rii i)) (rii i)
    (SpacetimeMollifierL2.tendsto_eLpNorm_spacetimeMollification_sub (rii i) (hrii i))
  exact ⟨
    tendsto_integral_fixed_mul_mul_restrict S _ _ _ rt (ri i)
      (hc₁ i) hrtE hriE hrtR hriR hrtT hriT,
    tendsto_integral_fixed_mul_mul_restrict S _ _ _ rt (rii i)
      hc₂ hrtE hriiE hrtR hriiR hrtT hriiT,
    tendsto_integral_fixed_mul_mul_restrict S _ _ _ (ri i) (ri i)
      hc₃ hriE hriE hriR hriR hriT hriT⟩

/-- The three coordinate limits assemble into the exact finite sums used on
the two sides of the localized weak energy identity. -/
private theorem summed_energy_product_limits
    {d : ℕ} (S : Set (TimeVelocity d))
    (η : PDE.Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηCompact : HasCompactSupport η)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζCompact : HasCompactSupport ζ)
    (rt : TimeVelocity d → ℝ)
    (ri rii : Fin d → TimeVelocity d → ℝ)
    (hrt : MemLp rt (2 : ℝ≥0∞) volume)
    (hri : ∀ i, MemLp (ri i) (2 : ℝ≥0∞) volume)
    (hrii : ∀ i, MemLp (rii i) (2 : ℝ≥0∞) volume) :
    Filter.Tendsto (fun ε : ℝ => ∑ i : Fin d,
        ((∫ z in S, ((-2 : ℝ) * ζ z.1 *
            (η z.2 * spatialPartial i η z.2)) *
            SpacetimeMollifier.spacetimeMollification ε rt z *
            SpacetimeMollifier.spacetimeMollification ε (ri i) z ∂volume) +
          ∫ z in S, ((-1 : ℝ) * ζ z.1 * η z.2 ^ 2) *
            SpacetimeMollifier.spacetimeMollification ε rt z *
            SpacetimeMollifier.spacetimeMollification ε (rii i) z ∂volume))
      (𝓝[>] 0) (𝓝 (∑ i : Fin d,
        ((∫ z in S, ((-2 : ℝ) * ζ z.1 *
            (η z.2 * spatialPartial i η z.2)) * rt z * ri i z ∂volume) +
          ∫ z in S, ((-1 : ℝ) * ζ z.1 * η z.2 ^ 2) *
            rt z * rii i z ∂volume))) ∧
    Filter.Tendsto (fun ε : ℝ => ∑ i : Fin d,
        ∫ z in S, (_root_.deriv ζ z.1 * η z.2 ^ 2) *
          SpacetimeMollifier.spacetimeMollification ε (ri i) z *
          SpacetimeMollifier.spacetimeMollification ε (ri i) z ∂volume)
      (𝓝[>] 0) (𝓝 (∑ i : Fin d,
        ∫ z in S, (_root_.deriv ζ z.1 * η z.2 ^ 2) *
          ri i z * ri i z ∂volume)) := by
  have hcoord (i : Fin d) := coordinate_energy_product_limits S η hη hηCompact
    ζ hζ hζCompact rt ri rii hrt hri hrii i
  constructor
  · apply tendsto_sum_coordinates
    intro i
    exact (hcoord i).1.add (hcoord i).2.1
  · apply tendsto_sum_coordinates
    intro i
    exact (hcoord i).2.2

/-- The coordinate-product presentation is exactly the literal localized
divergence and gradient-square presentation; every integral rewrite is backed
by explicit `L² × L²` integrability. -/
private theorem energy_coordinate_integral_algebra
    {d : ℕ} (S : Set (TimeVelocity d))
    (η : PDE.Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηCompact : HasCompactSupport η)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζCompact : HasCompactSupport ζ)
    (rt : TimeVelocity d → ℝ)
    (ri rii : Fin d → TimeVelocity d → ℝ)
    (hrt : MemLp rt (2 : ℝ≥0∞) ((volume : Measure (TimeVelocity d)).restrict S))
    (hri : ∀ i, MemLp (ri i) (2 : ℝ≥0∞)
      ((volume : Measure (TimeVelocity d)).restrict S))
    (hrii : ∀ i, MemLp (rii i) (2 : ℝ≥0∞)
      ((volume : Measure (TimeVelocity d)).restrict S)) :
    (∑ i : Fin d,
        ((∫ z in S, ((-2 : ℝ) * ζ z.1 *
            (η z.2 * spatialPartial i η z.2)) * rt z * ri i z ∂volume) +
          ∫ z in S, ((-1 : ℝ) * ζ z.1 * η z.2 ^ 2) *
            rt z * rii i z ∂volume)) =
      ∫ z in S, ζ z.1 * rt z *
        localizedGradientDivergence η
          (fun z i => ri i z) (fun z i _ => rii i z) z ∂volume ∧
    (∑ i : Fin d, ∫ z in S,
        (_root_.deriv ζ z.1 * η z.2 ^ 2) * ri i z * ri i z ∂volume) =
      ∫ z in S, _root_.deriv ζ z.1 * η z.2 ^ 2 *
        ∑ i : Fin d, ri i z ^ 2 ∂volume := by
  let μ := (volume : Measure (TimeVelocity d)).restrict S
  rcases concrete_energy_multipliers_memLp_top S η hη hηCompact ζ hζ hζCompact with
    ⟨hc₁, hc₂, hc₃⟩
  let A : Fin d → TimeVelocity d → ℝ := fun i z =>
    ((-2 : ℝ) * ζ z.1 * (η z.2 * spatialPartial i η z.2)) * rt z * ri i z
  let B : Fin d → TimeVelocity d → ℝ := fun i z =>
    ((-1 : ℝ) * ζ z.1 * η z.2 ^ 2) * rt z * rii i z
  let C : Fin d → TimeVelocity d → ℝ := fun i z =>
    (_root_.deriv ζ z.1 * η z.2 ^ 2) * ri i z * ri i z
  have hA (i : Fin d) : Integrable (A i) μ := by
    have hw : MemLp (fun z =>
        ((-2 : ℝ) * ζ z.1 * (η z.2 * spatialPartial i η z.2)) * rt z)
        (2 : ℝ≥0∞) μ := by
      simpa only [mul_comm] using hrt.mul' (hc₁ i)
    simpa only [A, Pi.mul_def] using hw.integrable_mul (hri i)
  have hB (i : Fin d) : Integrable (B i) μ := by
    have hw : MemLp (fun z => ((-1 : ℝ) * ζ z.1 * η z.2 ^ 2) * rt z)
        (2 : ℝ≥0∞) μ := by
      simpa only [mul_comm] using hrt.mul' hc₂
    simpa only [B, Pi.mul_def] using hw.integrable_mul (hrii i)
  have hC (i : Fin d) : Integrable (C i) μ := by
    have hw : MemLp (fun z => (_root_.deriv ζ z.1 * η z.2 ^ 2) * ri i z)
        (2 : ℝ≥0∞) μ := by
      simpa only [mul_comm] using (hri i).mul' hc₃
    simpa only [C, Pi.mul_def] using hw.integrable_mul (hri i)
  constructor
  · calc
      _ = ∑ i : Fin d, ∫ z, A i z + B i z ∂μ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [integral_add (hA i) (hB i)]
      _ = ∫ z, ∑ i : Fin d, (A i z + B i z) ∂μ := by
        exact (integral_finset_sum Finset.univ (fun i _ => (hA i).add (hB i))).symm
      _ = _ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun z => by
          simp only [A, B, localizedGradientDivergence]
          rw [← Finset.sum_neg_distrib, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
  · rw [← integral_finset_sum Finset.univ (fun i _ => hC i)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => by
      simp only [C, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- The exact localized divergence and gradient-square integrals converge for
the one common mollification of all localized representatives. -/
private theorem localized_energy_integral_limits
    {d : ℕ} (S : Set (TimeVelocity d))
    (η : PDE.Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηCompact : HasCompactSupport η)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζCompact : HasCompactSupport ζ)
    (rt : TimeVelocity d → ℝ)
    (ri rii : Fin d → TimeVelocity d → ℝ)
    (hrt : MemLp rt (2 : ℝ≥0∞) volume)
    (hri : ∀ i, MemLp (ri i) (2 : ℝ≥0∞) volume)
    (hrii : ∀ i, MemLp (rii i) (2 : ℝ≥0∞) volume) :
    Filter.Tendsto (fun ε : ℝ => ∫ z in S,
        ζ z.1 * SpacetimeMollifier.spacetimeMollification ε rt z *
          localizedGradientDivergence η
            (fun z i => SpacetimeMollifier.spacetimeMollification ε (ri i) z)
            (fun z i _j => SpacetimeMollifier.spacetimeMollification ε (rii i) z) z
        ∂volume) (𝓝[>] 0) (𝓝 (∫ z in S,
          ζ z.1 * rt z * localizedGradientDivergence η
            (fun z i => ri i z) (fun z i _j => rii i z) z ∂volume)) ∧
    Filter.Tendsto (fun ε : ℝ => ∫ z in S,
        _root_.deriv ζ z.1 * η z.2 ^ 2 *
          ∑ i : Fin d,
            SpacetimeMollifier.spacetimeMollification ε (ri i) z ^ 2 ∂volume)
      (𝓝[>] 0) (𝓝 (∫ z in S,
        _root_.deriv ζ z.1 * η z.2 ^ 2 * ∑ i : Fin d, ri i z ^ 2 ∂volume)) := by
  have hsum := summed_energy_product_limits S η hη hηCompact ζ hζ hζCompact
    rt ri rii hrt hri hrii
  have halg₀ := energy_coordinate_integral_algebra S η hη hηCompact ζ hζ hζCompact
    rt ri rii (hrt.restrict S) (fun i => (hri i).restrict S)
      (fun i => (hrii i).restrict S)
  have hevent : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      ((∑ i : Fin d,
          ((∫ z in S, ((-2 : ℝ) * ζ z.1 *
              (η z.2 * spatialPartial i η z.2)) *
              SpacetimeMollifier.spacetimeMollification ε rt z *
              SpacetimeMollifier.spacetimeMollification ε (ri i) z ∂volume) +
            ∫ z in S, ((-1 : ℝ) * ζ z.1 * η z.2 ^ 2) *
              SpacetimeMollifier.spacetimeMollification ε rt z *
              SpacetimeMollifier.spacetimeMollification ε (rii i) z ∂volume)) =
        ∫ z in S, ζ z.1 * SpacetimeMollifier.spacetimeMollification ε rt z *
          localizedGradientDivergence η
            (fun z i => SpacetimeMollifier.spacetimeMollification ε (ri i) z)
            (fun z i _j => SpacetimeMollifier.spacetimeMollification ε (rii i) z) z ∂volume) ∧
      (∑ i : Fin d, ∫ z in S,
          (_root_.deriv ζ z.1 * η z.2 ^ 2) *
            SpacetimeMollifier.spacetimeMollification ε (ri i) z *
            SpacetimeMollifier.spacetimeMollification ε (ri i) z ∂volume) =
        ∫ z in S, _root_.deriv ζ z.1 * η z.2 ^ 2 *
          ∑ i : Fin d,
            SpacetimeMollifier.spacetimeMollification ε (ri i) z ^ 2 ∂volume := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    apply energy_coordinate_integral_algebra S η hη hηCompact ζ hζ hζCompact
      (SpacetimeMollifier.spacetimeMollification ε rt)
      (fun i => SpacetimeMollifier.spacetimeMollification ε (ri i))
      (fun i => SpacetimeMollifier.spacetimeMollification ε (rii i))
    · exact (SpacetimeMollifierL2.spacetimeMollification_memLp hε rt hrt).restrict S
    · intro i
      exact (SpacetimeMollifierL2.spacetimeMollification_memLp hε (ri i) (hri i)).restrict S
    · intro i
      exact (SpacetimeMollifierL2.spacetimeMollification_memLp hε (rii i) (hrii i)).restrict S
  constructor
  · rw [← halg₀.1]
    exact hsum.1.congr' (hevent.mono fun ε h => h.1)
  · rw [← halg₀.2]
    exact hsum.2.congr' (hevent.mono fun ε h => h.2)

/-- The two literal weak-energy target integrands are integrable directly
from the componentwise `L²` assumptions and bounded compact cutoffs. -/
private theorem weak_energy_targets_integrableOn
    {d : ℕ} (S : Set (TimeVelocity d))
    (QW : TimeVelocity d → ℝ)
    (QG : TimeVelocity d → PDE.Vec d)
    (QH : TimeVelocity d → PDE.Mat d)
    (hQW : ParabolicMemLpOn S (2 : ℝ≥0∞) QW)
    (hQG : ∀ i : Fin d,
      ParabolicMemLpOn S (2 : ℝ≥0∞) (fun z => QG z i))
    (hQH : ∀ i : Fin d,
      ParabolicMemLpOn S (2 : ℝ≥0∞) (fun z => QH z i i))
    (η : PDE.Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηCompact : HasCompactSupport η)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζCompact : HasCompactSupport ζ) :
    IntegrableOn (fun z => ζ z.1 * QW z *
      localizedGradientDivergence η QG QH z) S volume ∧
    IntegrableOn (fun z => _root_.deriv ζ z.1 * η z.2 ^ 2 *
      ∑ i : Fin d, QG z i ^ 2) S volume := by
  let μ := (volume : Measure (TimeVelocity d)).restrict S
  rcases concrete_energy_multipliers_memLp_top S η hη hηCompact ζ hζ hζCompact with
    ⟨hc₁, hc₂, hc₃⟩
  let A : Fin d → TimeVelocity d → ℝ := fun i z =>
    ((-2 : ℝ) * ζ z.1 * (η z.2 * spatialPartial i η z.2)) * QW z * QG z i
  let B : Fin d → TimeVelocity d → ℝ := fun i z =>
    ((-1 : ℝ) * ζ z.1 * η z.2 ^ 2) * QW z * QH z i i
  let C : Fin d → TimeVelocity d → ℝ := fun i z =>
    (_root_.deriv ζ z.1 * η z.2 ^ 2) * QG z i * QG z i
  have hA (i : Fin d) : Integrable (A i) μ := by
    have hw : MemLp (fun z =>
        ((-2 : ℝ) * ζ z.1 * (η z.2 * spatialPartial i η z.2)) * QW z)
        (2 : ℝ≥0∞) μ := by
      simpa only [mul_comm] using hQW.mul' (hc₁ i)
    simpa only [A, Pi.mul_def] using hw.integrable_mul (hQG i)
  have hB (i : Fin d) : Integrable (B i) μ := by
    have hw : MemLp (fun z => ((-1 : ℝ) * ζ z.1 * η z.2 ^ 2) * QW z)
        (2 : ℝ≥0∞) μ := by
      simpa only [mul_comm] using hQW.mul' hc₂
    simpa only [B, Pi.mul_def] using hw.integrable_mul (hQH i)
  have hC (i : Fin d) : Integrable (C i) μ := by
    have hw : MemLp (fun z => (_root_.deriv ζ z.1 * η z.2 ^ 2) * QG z i)
        (2 : ℝ≥0∞) μ := by
      simpa only [mul_comm] using (hQG i).mul' hc₃
    simpa only [C, Pi.mul_def] using hw.integrable_mul (hQG i)
  constructor
  · apply (integrable_finset_sum Finset.univ fun i _ => (hA i).add (hB i)).congr
    exact Filter.Eventually.of_forall fun z => by
      simp only [A, B, localizedGradientDivergence]
      rw [← Finset.sum_neg_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      dsimp only [Pi.add_apply]
      ring
  · apply (integrable_finset_sum Finset.univ fun i _ => hC i).congr
    exact Filter.Eventually.of_forall fun z => by
      simp only [C, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- Plateau agreement on the product of cutoff supports identifies both
localized weighted integrands with the selected raw representatives globally. -/
private theorem weak_energy_integrands_eq_of_eqOn_cutoff_support
    {d : ℕ} (QW rt : TimeVelocity d → ℝ)
    (QG : TimeVelocity d → PDE.Vec d)
    (QH : TimeVelocity d → PDE.Mat d)
    (ri rii : Fin d → TimeVelocity d → ℝ)
    (η : PDE.Vec d → ℝ) (ζ : ℝ → ℝ)
    (hrt : Set.EqOn rt QW (tsupport ζ ×ˢ tsupport η))
    (hri : ∀ i, Set.EqOn (ri i) (fun z => QG z i)
      (tsupport ζ ×ˢ tsupport η))
    (hrii : ∀ i, Set.EqOn (rii i) (fun z => QH z i i)
      (tsupport ζ ×ˢ tsupport η)) :
    (∀ z, ζ z.1 * rt z * localizedGradientDivergence η
        (fun z i => ri i z) (fun z i _j => rii i z) z =
      ζ z.1 * QW z * localizedGradientDivergence η QG QH z) ∧
    ∀ z, _root_.deriv ζ z.1 * η z.2 ^ 2 * ∑ i : Fin d, ri i z ^ 2 =
      _root_.deriv ζ z.1 * η z.2 ^ 2 * ∑ i : Fin d, QG z i ^ 2 := by
  constructor
  · intro z
    by_cases ht : z.1 ∈ tsupport ζ
    · by_cases hv : z.2 ∈ tsupport η
      · rw [hrt ⟨ht, hv⟩]
        unfold localizedGradientDivergence
        congr 2
        apply Finset.sum_congr rfl
        intro i hi
        dsimp only
        rw [hri i ⟨ht, hv⟩, hrii i ⟨ht, hv⟩]
      · have hzero : η z.2 = 0 := image_eq_zero_of_notMem_tsupport hv
        simp [localizedGradientDivergence, hzero]
    · have hzero : ζ z.1 = 0 := image_eq_zero_of_notMem_tsupport ht
      simp [hzero]
  · intro z
    by_cases ht : z.1 ∈ tsupport ζ
    · by_cases hv : z.2 ∈ tsupport η
      · apply congrArg (fun x : ℝ => _root_.deriv ζ z.1 * η z.2 ^ 2 * x)
        apply Finset.sum_congr rfl
        intro i hi
        rw [hri i ⟨ht, hv⟩]
      · have hzero : η z.2 = 0 := image_eq_zero_of_notMem_tsupport hv
        simp [hzero]
    · have hzero : _root_.deriv ζ z.1 = 0 := by
        rw [← fderiv_apply_one_eq_deriv, fderiv_of_notMem_tsupport ℝ ht]
        rfl
      simp [hzero]

/-- The supports of the two cutoffs have one common smooth compact
spacetime plateau inside the literal product cylinder. -/
private theorem exists_common_cutoff_plateau
    {d : ℕ} (s₀ s₁ : ℝ) (O : Set (PDE.Vec d)) (hO : IsOpen O)
    (η : PDE.Vec d → ℝ) (hηCompact : HasCompactSupport η)
    (hηSub : tsupport η ⊆ O)
    (ζ : ℝ → ℝ) (hζCompact : HasCompactSupport ζ)
    (hζSub : tsupport ζ ⊆ Set.Ioo s₀ s₁) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ b : TimeVelocity d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) b ∧ HasCompactSupport b ∧
        tsupport b ⊆ Set.Ioo s₀ s₁ ×ˢ O ∧
        Set.EqOn b 1
          (Metric.cthickening δ (tsupport ζ ×ˢ tsupport η)) := by
  have hU : IsOpen (Set.Ioo s₀ s₁ ×ˢ O) := isOpen_Ioo.prod hO
  have hK : IsCompact (tsupport ζ ×ˢ tsupport η) :=
    hζCompact.isCompact.prod hηCompact.isCompact
  have hKU : tsupport ζ ×ˢ tsupport η ⊆ Set.Ioo s₀ s₁ ×ˢ O := by
    rintro ⟨t, v⟩ ⟨ht, hv⟩
    exact ⟨hζSub ht, hηSub hv⟩
  exact exists_contDiff_one_on_cthickening_tsupport_subset hU hK hKU

/-- A plateau on a positive closed thickening is genuinely locally constant
at every point of the underlying carrier, so its first and second selected
derivatives vanish there. -/
private theorem plateau_value_derivatives
    {d : ℕ} {K : Set (TimeVelocity d)} {δ : ℝ} (hδ : 0 < δ)
    (b : TimeVelocity d → ℝ)
    (hbOne : Set.EqOn b 1 (Metric.cthickening δ K))
    {z : TimeVelocity d} (hz : z ∈ K) :
    b z = 1 ∧ timeDerivative b z = 0 ∧
      (∀ i : Fin d, velocityGradient b z i = 0) ∧
      ∀ i : Fin d, velocityHessian b z i i = 0 := by
  have hev : b =ᶠ[𝓝 z] (1 : TimeVelocity d → ℝ) := by
    filter_upwards [Metric.ball_mem_nhds z hδ] with y hy
    apply hbOne
    exact Metric.mem_cthickening_of_dist_le y z δ K hz hy.le
  have hbz : b z = 1 := hev.self_of_nhds
  have hdb : fderiv ℝ b z = 0 := by
    rw [hev.fderiv_eq]
    simp
  have hddb : fderiv ℝ (fderiv ℝ b) z = 0 := by
    have hevd : fderiv ℝ b =ᶠ[𝓝 z] fderiv ℝ (1 : TimeVelocity d → ℝ) := hev.fderiv
    rw [hevd.fderiv_eq]
    have hconst : fderiv ℝ (1 : TimeVelocity d → ℝ) = 0 := by
      funext y
      simp
    rw [hconst]
    simp
  refine ⟨hbz, ?_, ?_, ?_⟩
  · unfold timeDerivative
    rw [hdb]
    rfl
  · intro i
    unfold velocityGradient
    rw [hdb]
    rfl
  · intro i
    unfold velocityHessian
    rw [hddb]
    rfl

/-- On the plateau carrier, all four localized representatives agree exactly
with the originally selected representatives. -/
private theorem localized_jet_eqOn_plateau
    {d : ℕ} {K : Set (TimeVelocity d)} {δ : ℝ} (hδ : 0 < δ)
    (q QW : TimeVelocity d → ℝ)
    (QG : TimeVelocity d → PDE.Vec d)
    (QH : TimeVelocity d → PDE.Mat d)
    (b : TimeVelocity d → ℝ)
    (hbOne : Set.EqOn b 1 (Metric.cthickening δ K)) :
    Set.EqOn (fun z => b z * q z) q K ∧
      Set.EqOn (fun z => b z * QW z + q z * timeDerivative b z) QW K ∧
      (∀ i : Fin d, Set.EqOn
        (fun z => b z * QG z i + q z * velocityGradient b z i)
        (fun z => QG z i) K) ∧
      ∀ i : Fin d, Set.EqOn
        (fun z => b z * QH z i i + 2 * velocityGradient b z i * QG z i +
          q z * velocityHessian b z i i)
        (fun z => QH z i i) K := by
  constructor
  · intro z hz
    obtain ⟨hbz, hbt, hbi, hbii⟩ := plateau_value_derivatives hδ b hbOne hz
    simp [hbz]
  constructor
  · intro z hz
    obtain ⟨hbz, hbt, hbi, hbii⟩ := plateau_value_derivatives hδ b hbOne hz
    simp [hbz, hbt]
  constructor
  · intro i z hz
    obtain ⟨hbz, hbt, hbi, hbii⟩ := plateau_value_derivatives hδ b hbOne hz
    simp [hbz, hbi i]
  · intro i z hz
    obtain ⟨hbz, hbt, hbi, hbii⟩ := plateau_value_derivatives hδ b hbOne hz
    simp [hbz, hbi i, hbii i]

/-- Multiplication by one smooth cutoff gives the exact selected weak time
derivative and every selected first velocity derivative. -/
private theorem localized_first_jet
    {d : ℕ} {U : Set (TimeVelocity d)}
    (q QW : TimeVelocity d → ℝ)
    (QG : TimeVelocity d → PDE.Vec d)
    (hqLoc : LocallyIntegrableOn q U volume)
    (hQWLoc : LocallyIntegrableOn QW U volume)
    (hQGLoc : ∀ i : Fin d,
      LocallyIntegrableOn (fun z => QG z i) U volume)
    (hqTime : HasWeakTimeDerivOn U q QW)
    (hqVelocity : ∀ i : Fin d,
      HasWeakVelocityPartialDerivOn U i q (fun z => QG z i))
    (b : TimeVelocity d → ℝ)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) :
    HasWeakTimeDerivOn U
        (fun z => b z * q z)
        (fun z => b z * QW z + q z * timeDerivative b z) ∧
      ∀ i : Fin d,
        HasWeakVelocityPartialDerivOn U i
          (fun z => b z * q z)
          (fun z => b z * QG z i + q z * velocityGradient b z i) := by
  constructor
  · exact hqTime.mul_contDiff hb hqLoc hQWLoc
  · intro i
    exact (hqVelocity i).mul_contDiff hb hqLoc (hQGLoc i)

/-- Every field in the localized first jet is supported in the support of the
single common cutoff. -/
private theorem localized_first_jet_tsupport_subset
    {d : ℕ} (q QW : TimeVelocity d → ℝ)
    (QG : TimeVelocity d → PDE.Vec d)
    (b : TimeVelocity d → ℝ) :
    tsupport (fun z => b z * q z) ⊆ tsupport b ∧
      tsupport (fun z => b z * QW z + q z * timeDerivative b z) ⊆ tsupport b ∧
      ∀ i : Fin d,
        tsupport (fun z => b z * QG z i + q z * velocityGradient b z i) ⊆
          tsupport b := by
  have close_support_subset (f : TimeVelocity d → ℝ)
      (hf : Function.support f ⊆ tsupport b) : tsupport f ⊆ tsupport b := by
    have hc : closure (tsupport b) = tsupport b :=
      (isClosed_tsupport b).closure_eq
    simpa only [tsupport, closure_closure] using closure_mono hf
  constructor
  · exact close_support_subset _ fun z hz =>
      tsupport_mul_subset_left (subset_closure hz)
  constructor
  · apply close_support_subset
    intro z hz
    by_contra hzb
    have hb0 : b z = 0 := image_eq_zero_of_notMem_tsupport hzb
    have hdb0 : timeDerivative b z = 0 := by
      unfold timeDerivative
      rw [fderiv_of_notMem_tsupport ℝ hzb]
      rfl
    exact hz (by simp [hb0, hdb0])
  · intro i
    apply close_support_subset
    intro z hz
    by_contra hzb
    have hb0 : b z = 0 := image_eq_zero_of_notMem_tsupport hzb
    have hdb0 : velocityGradient b z i = 0 := by
      unfold velocityGradient
      rw [fderiv_of_notMem_tsupport ℝ hzb]
      rfl
    exact hz (by simp [hb0, hdb0])

private theorem velocityGradient_cutoff_contDiff
    {d : ℕ} (b : TimeVelocity d → ℝ)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => velocityGradient b z i) := by
  unfold velocityGradient
  exact (contDiff_infty_iff_fderiv.mp hb).2.clm_apply contDiff_const

private theorem velocityGradient_cutoff_gradient
    {d : ℕ} (b : TimeVelocity d → ℝ)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (i : Fin d) (z : TimeVelocity d) :
    velocityGradient (fun y => velocityGradient b y i) z i =
      velocityHessian b z i i := by
  unfold velocityGradient velocityHessian
  have hgrad : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ b) :=
    (contDiff_infty_iff_fderiv.mp hb).2
  rw [fderiv_clm_apply
    (hgrad.differentiable (by simp) z) (differentiableAt_const _)]
  rw [fderiv_const_apply]
  simp

/-- The localized selected first velocity representative has the exact
diagonal second weak derivative furnished by the same cutoff. -/
private theorem localized_diagonal_second_jet
    {d : ℕ} {U : Set (TimeVelocity d)}
    (q : TimeVelocity d → ℝ)
    (QG : TimeVelocity d → PDE.Vec d)
    (QH : TimeVelocity d → PDE.Mat d)
    (i : Fin d)
    (hqLoc : LocallyIntegrableOn q U volume)
    (hQGiLoc : LocallyIntegrableOn (fun z => QG z i) U volume)
    (hQHiiLoc : LocallyIntegrableOn (fun z => QH z i i) U volume)
    (hqVelocity : HasWeakVelocityPartialDerivOn U i q (fun z => QG z i))
    (hQGVelocity : HasWeakVelocityPartialDerivOn U i
      (fun z => QG z i) (fun z => QH z i i))
    (b : TimeVelocity d → ℝ)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hfirstLoc : LocallyIntegrableOn (fun z => b z * QG z i) U volume)
    (hfirstDerivLoc : LocallyIntegrableOn
      (fun z => b z * QH z i i + QG z i * velocityGradient b z i) U volume)
    (hsecondLoc : LocallyIntegrableOn
      (fun z => velocityGradient b z i * q z) U volume)
    (hsecondDerivLoc : LocallyIntegrableOn
      (fun z => velocityGradient b z i * QG z i +
        q z * velocityGradient (fun y => velocityGradient b y i) z i) U volume) :
    HasWeakVelocityPartialDerivOn U i
      (fun z => b z * QG z i + q z * velocityGradient b z i)
      (fun z => b z * QH z i i +
        2 * velocityGradient b z i * QG z i +
          q z * velocityHessian b z i i) := by
  have hfirst := hQGVelocity.mul_contDiff hb hQGiLoc hQHiiLoc
  have hdbi := velocityGradient_cutoff_contDiff b hb i
  have hsecond := hqVelocity.mul_contDiff hdbi hqLoc hQGiLoc
  have hadd := hfirst.add hsecond hfirstLoc hfirstDerivLoc hsecondLoc hsecondDerivLoc
  convert hadd using 1 <;> funext z
  · ring
  · rw [velocityGradient_cutoff_gradient b hb i z]
    ring

/-- The exact localized diagonal representative remains supported in the
support of the common cutoff. -/
private theorem localized_diagonal_second_tsupport_subset
    {d : ℕ} (q : TimeVelocity d → ℝ)
    (QG : TimeVelocity d → PDE.Vec d)
    (QH : TimeVelocity d → PDE.Mat d)
    (b : TimeVelocity d → ℝ) (i : Fin d) :
    tsupport (fun z => b z * QH z i i +
      2 * velocityGradient b z i * QG z i +
        q z * velocityHessian b z i i) ⊆ tsupport b := by
  have hsupp : Function.support (fun z => b z * QH z i i +
      2 * velocityGradient b z i * QG z i +
        q z * velocityHessian b z i i) ⊆ tsupport b := by
    intro z hz
    by_contra hzb
    have hb0 : b z = 0 := image_eq_zero_of_notMem_tsupport hzb
    have hdb0 : velocityGradient b z i = 0 := by
      unfold velocityGradient
      rw [fderiv_of_notMem_tsupport ℝ hzb]
      rfl
    have hddb0 : velocityHessian b z i i = 0 := by
      unfold velocityHessian
      have hfirst : fderiv ℝ b z = 0 := fderiv_of_notMem_tsupport ℝ hzb
      have hsecond : fderiv ℝ (fderiv ℝ b) z = 0 := by
        rw [fderiv_of_notMem_tsupport ℝ]
        exact fun hmem => hzb (tsupport_fderiv_subset ℝ hmem)
      rw [hsecond]
      rfl
    exact hz (by simp [hb0, hdb0, hddb0])
  have hc : closure (tsupport b) = tsupport b := (isClosed_tsupport b).closure_eq
  simpa only [tsupport, closure_closure] using closure_mono hsupp

private theorem timeDerivative_cutoff_continuous
    {d : ℕ} (b : TimeVelocity d → ℝ)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) : Continuous (timeDerivative b) := by
  unfold timeDerivative
  simpa using (hb.continuous_fderiv (by simp)).clm_apply continuous_const

private theorem timeDerivative_cutoff_compact
    {d : ℕ} (b : TimeVelocity d → ℝ) (hb : HasCompactSupport b) :
    HasCompactSupport (timeDerivative b) := by
  unfold timeDerivative
  simpa using hb.fderiv_apply (𝕜 := ℝ) ((1, 0) : TimeVelocity d)

private theorem velocityGradient_cutoff_compact
    {d : ℕ} (b : TimeVelocity d → ℝ) (hb : HasCompactSupport b) (i : Fin d) :
    HasCompactSupport (fun z => velocityGradient b z i) := by
  unfold velocityGradient
  simpa using hb.fderiv_apply (𝕜 := ℝ) ((0, Pi.single i 1) : TimeVelocity d)

private theorem velocityHessian_cutoff_continuous
    {d : ℕ} (b : TimeVelocity d → ℝ)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (i : Fin d) :
    Continuous (fun z => velocityHessian b z i i) := by
  unfold velocityHessian
  have hgrad : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ b) :=
    (contDiff_infty_iff_fderiv.mp hb).2
  simpa using (hgrad.continuous_fderiv (by simp)).clm_apply continuous_const |>.clm_apply
    continuous_const

private theorem velocityHessian_cutoff_compact
    {d : ℕ} (b : TimeVelocity d → ℝ) (hb : HasCompactSupport b) (i : Fin d) :
    HasCompactSupport (fun z => velocityHessian b z i i) := by
  unfold velocityHessian
  have hfirst : HasCompactSupport (fderiv ℝ b) := hb.fderiv ℝ
  have hsecond : HasCompactSupport (fderiv ℝ (fderiv ℝ b)) := hfirst.fderiv ℝ
  simpa only [Function.comp_def] using hsecond.comp_left
    (g := fun H : TimeVelocity d →L[ℝ] TimeVelocity d →L[ℝ] ℝ =>
      H ((0, Pi.single i 1) : TimeVelocity d)
        ((0, Pi.single i 1) : TimeVelocity d)) rfl

/-- The four representatives obtained from one smooth compact localization
inherit the `L²` exponent from the selected weak jet. -/
private theorem localized_jet_memLp
    {d : ℕ} {U : Set (TimeVelocity d)}
    (q QW : TimeVelocity d → ℝ)
    (QG : TimeVelocity d → PDE.Vec d)
    (QH : TimeVelocity d → PDE.Mat d)
    (hq : ParabolicMemLpOn U (2 : ℝ≥0∞) q)
    (hQW : ParabolicMemLpOn U (2 : ℝ≥0∞) QW)
    (hQG : ∀ i : Fin d,
      ParabolicMemLpOn U (2 : ℝ≥0∞) (fun z => QG z i))
    (hQH : ∀ i : Fin d,
      ParabolicMemLpOn U (2 : ℝ≥0∞) (fun z => QH z i i))
    (b : TimeVelocity d → ℝ)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hbCompact : HasCompactSupport b) :
    ParabolicMemLpOn U (2 : ℝ≥0∞) (fun z => b z * q z) ∧
      ParabolicMemLpOn U (2 : ℝ≥0∞)
        (fun z => b z * QW z + q z * timeDerivative b z) ∧
      (∀ i : Fin d, ParabolicMemLpOn U (2 : ℝ≥0∞)
        (fun z => b z * QG z i + q z * velocityGradient b z i)) ∧
      ∀ i : Fin d, ParabolicMemLpOn U (2 : ℝ≥0∞)
        (fun z => b z * QH z i i +
          2 * velocityGradient b z i * QG z i +
            q z * velocityHessian b z i i) := by
  have hbTop : ParabolicMemLpOn U ∞ b :=
    (hb.continuous.memLp_of_hasCompactSupport hbCompact).restrict U
  have hbtTop : ParabolicMemLpOn U ∞ (timeDerivative b) :=
    ((timeDerivative_cutoff_continuous b hb).memLp_of_hasCompactSupport
      (timeDerivative_cutoff_compact b hbCompact)).restrict U
  have hbiTop (i : Fin d) : ParabolicMemLpOn U ∞
      (fun z => velocityGradient b z i) :=
    ((velocityGradient_cutoff_contDiff b hb i).continuous.memLp_of_hasCompactSupport
      (velocityGradient_cutoff_compact b hbCompact i)).restrict U
  have hbiiTop (i : Fin d) : ParabolicMemLpOn U ∞
      (fun z => velocityHessian b z i i) :=
    ((velocityHessian_cutoff_continuous b hb i).memLp_of_hasCompactSupport
      (velocityHessian_cutoff_compact b hbCompact i)).restrict U
  have hr : ParabolicMemLpOn U (2 : ℝ≥0∞) (fun z => b z * q z) := by
    simpa only [mul_comm] using hq.mul' hbTop
  have hrt : ParabolicMemLpOn U (2 : ℝ≥0∞)
      (fun z => b z * QW z + q z * timeDerivative b z) := by
    exact (by
      have h1 : ParabolicMemLpOn U (2 : ℝ≥0∞) (fun z => b z * QW z) := by
        simpa only [mul_comm] using hQW.mul' hbTop
      have h2 : ParabolicMemLpOn U (2 : ℝ≥0∞)
          (fun z => q z * timeDerivative b z) := by
        simpa only [mul_comm] using hq.mul' hbtTop
      exact h1.add h2)
  have hri (i : Fin d) : ParabolicMemLpOn U (2 : ℝ≥0∞)
      (fun z => b z * QG z i + q z * velocityGradient b z i) := by
    have h1 : ParabolicMemLpOn U (2 : ℝ≥0∞) (fun z => b z * QG z i) := by
      simpa only [mul_comm] using (hQG i).mul' hbTop
    have h2 : ParabolicMemLpOn U (2 : ℝ≥0∞)
        (fun z => q z * velocityGradient b z i) := by
      simpa only [mul_comm] using hq.mul' (hbiTop i)
    exact h1.add h2
  have hrii (i : Fin d) : ParabolicMemLpOn U (2 : ℝ≥0∞)
      (fun z => b z * QH z i i +
        2 * velocityGradient b z i * QG z i +
          q z * velocityHessian b z i i) := by
    have h1 : ParabolicMemLpOn U (2 : ℝ≥0∞) (fun z => b z * QH z i i) := by
      simpa only [mul_comm] using (hQH i).mul' hbTop
    have h2raw : ParabolicMemLpOn U (2 : ℝ≥0∞)
        (fun z => velocityGradient b z i * QG z i) := by
      simpa only [mul_comm] using (hQG i).mul' (hbiTop i)
    have h2 := h2raw.const_smul (2 : ℝ)
    have h3 : ParabolicMemLpOn U (2 : ℝ≥0∞)
        (fun z => q z * velocityHessian b z i i) := by
      simpa only [mul_comm] using hq.mul' (hbiiTop i)
    convert (h1.add h2).add h3 using 1
    funext z
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  exact ⟨hr, hrt, hri, hrii⟩

/-- One compact localization of the selected diagonal jet globalizes both its
raw weak relations and its `L²` representatives. -/
private theorem localized_jet_univ
    {d : ℕ} {U : Set (TimeVelocity d)} (hU : IsOpen U)
    (q QW : TimeVelocity d → ℝ)
    (QG : TimeVelocity d → PDE.Vec d)
    (QH : TimeVelocity d → PDE.Mat d)
    (hq : ParabolicMemLpOn U (2 : ℝ≥0∞) q)
    (hQW : ParabolicMemLpOn U (2 : ℝ≥0∞) QW)
    (hQG : ∀ i : Fin d,
      ParabolicMemLpOn U (2 : ℝ≥0∞) (fun z => QG z i))
    (hQH : ∀ i : Fin d,
      ParabolicMemLpOn U (2 : ℝ≥0∞) (fun z => QH z i i))
    (hqTime : HasWeakTimeDerivOn U q QW)
    (hqVelocity : ∀ i : Fin d,
      HasWeakVelocityPartialDerivOn U i q (fun z => QG z i))
    (hQGVelocity : ∀ i : Fin d,
      HasWeakVelocityPartialDerivOn U i (fun z => QG z i) (fun z => QH z i i))
    (b : TimeVelocity d → ℝ)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hbCompact : HasCompactSupport b)
    (hbSub : tsupport b ⊆ U) :
    HasWeakTimeDerivOn Set.univ
        (fun z => b z * q z)
        (fun z => b z * QW z + q z * timeDerivative b z) ∧
      (∀ i : Fin d, HasWeakVelocityPartialDerivOn Set.univ i
        (fun z => b z * q z)
        (fun z => b z * QG z i + q z * velocityGradient b z i)) ∧
      (∀ i : Fin d, HasWeakVelocityPartialDerivOn Set.univ i
        (fun z => b z * QG z i + q z * velocityGradient b z i)
        (fun z => b z * QH z i i + 2 * velocityGradient b z i * QG z i +
          q z * velocityHessian b z i i)) ∧
      MemLp (fun z => b z * q z) (2 : ℝ≥0∞) volume ∧
      MemLp (fun z => b z * QW z + q z * timeDerivative b z)
        (2 : ℝ≥0∞) volume ∧
      (∀ i : Fin d, MemLp
        (fun z => b z * QG z i + q z * velocityGradient b z i)
        (2 : ℝ≥0∞) volume) ∧
      ∀ i : Fin d, MemLp
        (fun z => b z * QH z i i + 2 * velocityGradient b z i * QG z i +
          q z * velocityHessian b z i i) (2 : ℝ≥0∞) volume := by
  have hmem := localized_jet_memLp q QW QG QH hq hQW hQG hQH b hb hbCompact
  rcases hmem with ⟨hr, hrt, hri, hrii⟩
  have hfirst := localized_first_jet q QW QG
    (hq.locallyIntegrableOn (by norm_num))
    (hQW.locallyIntegrableOn (by norm_num))
    (fun i => (hQG i).locallyIntegrableOn (by norm_num))
    hqTime hqVelocity b hb
  rcases hfirst with ⟨hrTime, hrVelocity⟩
  have hsupp := localized_first_jet_tsupport_subset q QW QG b
  rcases hsupp with ⟨hrSupp, hrtSupp, hriSupp⟩
  have hbTop : ParabolicMemLpOn U ∞ b :=
    (hb.continuous.memLp_of_hasCompactSupport hbCompact).restrict U
  have hbiTop (i : Fin d) : ParabolicMemLpOn U ∞
      (fun z => velocityGradient b z i) :=
    ((velocityGradient_cutoff_contDiff b hb i).continuous.memLp_of_hasCompactSupport
      (velocityGradient_cutoff_compact b hbCompact i)).restrict U
  have hbiiTop (i : Fin d) : ParabolicMemLpOn U ∞
      (fun z => velocityHessian b z i i) :=
    ((velocityHessian_cutoff_continuous b hb i).memLp_of_hasCompactSupport
      (velocityHessian_cutoff_compact b hbCompact i)).restrict U
  have hdiag (i : Fin d) : HasWeakVelocityPartialDerivOn U i
      (fun z => b z * QG z i + q z * velocityGradient b z i)
      (fun z => b z * QH z i i + 2 * velocityGradient b z i * QG z i +
        q z * velocityHessian b z i i) := by
    have hfirstM : ParabolicMemLpOn U (2 : ℝ≥0∞)
        (fun z => b z * QG z i) := by
      simpa only [mul_comm] using (hQG i).mul' hbTop
    have hfirstDM : ParabolicMemLpOn U (2 : ℝ≥0∞)
        (fun z => b z * QH z i i + QG z i * velocityGradient b z i) := by
      have h1 : ParabolicMemLpOn U (2 : ℝ≥0∞) (fun z => b z * QH z i i) := by
        simpa only [mul_comm] using (hQH i).mul' hbTop
      have h2 : ParabolicMemLpOn U (2 : ℝ≥0∞)
          (fun z => QG z i * velocityGradient b z i) := by
        simpa only [mul_comm] using (hQG i).mul' (hbiTop i)
      exact h1.add h2
    have hsecondM : ParabolicMemLpOn U (2 : ℝ≥0∞)
        (fun z => velocityGradient b z i * q z) := by
      simpa only [mul_comm] using hq.mul' (hbiTop i)
    have hsecondDM : ParabolicMemLpOn U (2 : ℝ≥0∞)
        (fun z => velocityGradient b z i * QG z i +
          q z * velocityGradient (fun y => velocityGradient b y i) z i) := by
      have h1 : ParabolicMemLpOn U (2 : ℝ≥0∞)
          (fun z => velocityGradient b z i * QG z i) := by
        simpa only [mul_comm] using (hQG i).mul' (hbiTop i)
      have h2 : ParabolicMemLpOn U (2 : ℝ≥0∞)
          (fun z => q z * velocityGradient (fun y => velocityGradient b y i) z i) := by
        have hraw : ParabolicMemLpOn U (2 : ℝ≥0∞)
            (fun z => q z * velocityHessian b z i i) := by
          simpa only [mul_comm] using hq.mul' (hbiiTop i)
        simpa only [velocityGradient_cutoff_gradient b hb i] using hraw
      exact h1.add h2
    exact localized_diagonal_second_jet q QG QH i
      (hq.locallyIntegrableOn (by norm_num))
      ((hQG i).locallyIntegrableOn (by norm_num))
      ((hQH i).locallyIntegrableOn (by norm_num))
      (hqVelocity i) (hQGVelocity i) b hb
      (hfirstM.locallyIntegrableOn (by norm_num))
      (hfirstDM.locallyIntegrableOn (by norm_num))
      (hsecondM.locallyIntegrableOn (by norm_num))
      (hsecondDM.locallyIntegrableOn (by norm_num))
  have hdiagSupp (i : Fin d) := localized_diagonal_second_tsupport_subset q QG QH b i
  have hrTimeUniv := hrTime.univ_of_tsupport_subset hU
    (hrSupp.trans hbSub) (hrtSupp.trans hbSub)
  have hrVelocityUniv (i : Fin d) := (hrVelocity i).univ_of_tsupport_subset hU
    (hrSupp.trans hbSub) ((hriSupp i).trans hbSub)
  have hdiagUniv (i : Fin d) := (hdiag i).univ_of_tsupport_subset hU
    ((hriSupp i).trans hbSub) ((hdiagSupp i).trans hbSub)
  have globalize {f : TimeVelocity d → ℝ}
      (hf : ParabolicMemLpOn U (2 : ℝ≥0∞) f)
      (hs : tsupport f ⊆ U) : MemLp f (2 : ℝ≥0∞) volume :=
    hf.memLp_of_support_subset hU.measurableSet
      (subset_tsupport f |>.trans hs)
  exact ⟨hrTimeUniv, hrVelocityUniv, hdiagUniv,
    globalize hr (hrSupp.trans hbSub),
    globalize hrt (hrtSupp.trans hbSub),
    fun i => globalize (hri i) ((hriSupp i).trans hbSub),
    fun i => globalize (hrii i) ((hdiagSupp i).trans hbSub)⟩

/-- The single mollification of the localized scalar realizes all selected
time, first velocity, and diagonal second derivatives and converges strongly
to their localized representatives. -/
private theorem common_mollifier_of_localized_jet
    {d : ℕ} {U : Set (TimeVelocity d)} (hU : IsOpen U)
    (q QW : TimeVelocity d → ℝ)
    (QG : TimeVelocity d → PDE.Vec d)
    (QH : TimeVelocity d → PDE.Mat d)
    (hq : ParabolicMemLpOn U (2 : ℝ≥0∞) q)
    (hQW : ParabolicMemLpOn U (2 : ℝ≥0∞) QW)
    (hQG : ∀ i : Fin d,
      ParabolicMemLpOn U (2 : ℝ≥0∞) (fun z => QG z i))
    (hQH : ∀ i : Fin d,
      ParabolicMemLpOn U (2 : ℝ≥0∞) (fun z => QH z i i))
    (hqTime : HasWeakTimeDerivOn U q QW)
    (hqVelocity : ∀ i : Fin d,
      HasWeakVelocityPartialDerivOn U i q (fun z => QG z i))
    (hQGVelocity : ∀ i : Fin d,
      HasWeakVelocityPartialDerivOn U i (fun z => QG z i) (fun z => QH z i i))
    (b : TimeVelocity d → ℝ)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hbCompact : HasCompactSupport b)
    (hbSub : tsupport b ⊆ U)
    (ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞)
        (SpacetimeMollifier.spacetimeMollification ε (fun z => b z * q z)) ∧
      timeDerivative
          (SpacetimeMollifier.spacetimeMollification ε (fun z => b z * q z)) =
        SpacetimeMollifier.spacetimeMollification ε
          (fun z => b z * QW z + q z * timeDerivative b z) ∧
      (∀ i : Fin d,
        (fun z => velocityGradient
          (SpacetimeMollifier.spacetimeMollification ε (fun z => b z * q z)) z i) =
          SpacetimeMollifier.spacetimeMollification ε
            (fun z => b z * QG z i + q z * velocityGradient b z i)) ∧
      (∀ i : Fin d,
        (fun z => velocityHessian
          (SpacetimeMollifier.spacetimeMollification ε (fun z => b z * q z)) z i i) =
          SpacetimeMollifier.spacetimeMollification ε
            (fun z => b z * QH z i i + 2 * velocityGradient b z i * QG z i +
              q z * velocityHessian b z i i)) ∧
      Filter.Tendsto (fun a : ℝ => eLpNorm
          (SpacetimeMollifier.spacetimeMollification a (fun z => b z * q z) -
            fun z => b z * q z) (2 : ℝ≥0∞) volume)
        (𝓝[>] 0) (𝓝 0) ∧
      Filter.Tendsto (fun a : ℝ => eLpNorm
          (SpacetimeMollifier.spacetimeMollification a
              (fun z => b z * QW z + q z * timeDerivative b z) -
            fun z => b z * QW z + q z * timeDerivative b z)
          (2 : ℝ≥0∞) volume) (𝓝[>] 0) (𝓝 0) ∧
      (∀ i : Fin d, Filter.Tendsto (fun a : ℝ => eLpNorm
          (SpacetimeMollifier.spacetimeMollification a
              (fun z => b z * QG z i + q z * velocityGradient b z i) -
            fun z => b z * QG z i + q z * velocityGradient b z i)
          (2 : ℝ≥0∞) volume) (𝓝[>] 0) (𝓝 0)) ∧
      ∀ i : Fin d, Filter.Tendsto (fun a : ℝ => eLpNorm
          (SpacetimeMollifier.spacetimeMollification a
              (fun z => b z * QH z i i + 2 * velocityGradient b z i * QG z i +
                q z * velocityHessian b z i i) -
            fun z => b z * QH z i i + 2 * velocityGradient b z i * QG z i +
              q z * velocityHessian b z i i)
          (2 : ℝ≥0∞) volume) (𝓝[>] 0) (𝓝 0) := by
  rcases localized_jet_univ hU q QW QG QH hq hQW hQG hQH
      hqTime hqVelocity hQGVelocity b hb hbCompact hbSub with
    ⟨hrTime, hrVelocity, hriiVelocity, hrMem, hrtMem, hriMem, hriiMem⟩
  have hrLoc := hrMem.locallyIntegrable (by norm_num)
  have hrtLoc := hrtMem.locallyIntegrable (by norm_num)
  have hriLoc (i : Fin d) := (hriMem i).locallyIntegrable (by norm_num)
  have hriiLoc (i : Fin d) := (hriiMem i).locallyIntegrable (by norm_num)
  have hsmooth := SpacetimeMollifier.contDiff_spacetimeMollification hε
    (fun z => b z * q z) hrLoc
  have htime := SpacetimeMollifier.timeDerivative_spacetimeMollification hε
    (fun z => b z * q z)
    (fun z => b z * QW z + q z * timeDerivative b z) hrLoc hrtLoc hrTime
  have hgrad (i : Fin d) := SpacetimeMollifier.velocityGradient_spacetimeMollification hε i
    (fun z => b z * q z)
    (fun z => b z * QG z i + q z * velocityGradient b z i)
    hrLoc (hriLoc i) (hrVelocity i)
  have hhess (i : Fin d) :
      (fun z => velocityHessian
        (SpacetimeMollifier.spacetimeMollification ε (fun z => b z * q z)) z i i) =
        SpacetimeMollifier.spacetimeMollification ε
          (fun z => b z * QH z i i + 2 * velocityGradient b z i * QG z i +
            q z * velocityHessian b z i i) := by
    have hsecond := SpacetimeMollifier.velocityGradient_spacetimeMollification hε i
      (fun z => b z * QG z i + q z * velocityGradient b z i)
      (fun z => b z * QH z i i + 2 * velocityGradient b z i * QG z i +
        q z * velocityHessian b z i i)
      (hriLoc i) (hriiLoc i) (hriiVelocity i)
    rw [← hgrad i] at hsecond
    funext z
    rw [← hsecond]
    exact (velocityGradient_cutoff_gradient _ hsmooth i z).symm
  exact ⟨hsmooth, htime, hgrad, hhess,
    SpacetimeMollifierL2.tendsto_eLpNorm_spacetimeMollification_sub _ hrMem,
    SpacetimeMollifierL2.tendsto_eLpNorm_spacetimeMollification_sub _ hrtMem,
    fun i => SpacetimeMollifierL2.tendsto_eLpNorm_spacetimeMollification_sub _ (hriMem i),
    fun i => SpacetimeMollifierL2.tendsto_eLpNorm_spacetimeMollification_sub _ (hriiMem i)⟩

/-- Compactly supported weak gradient time-energy identity on a literal
product cylinder. -/
theorem weakGradient_timeEnergy
    {d : ℕ} (s₀ s₁ : ℝ)
    (O : Set (PDE.Vec d)) (hO : IsOpen O)
    (q QW : TimeVelocity d → ℝ)
    (QG : TimeVelocity d → PDE.Vec d)
    (QH : TimeVelocity d → PDE.Mat d)
    (hq_memLp :
      ParabolicMemLpOn (Set.Ioo s₀ s₁ ×ˢ O) (2 : ℝ≥0∞) q)
    (hQW_memLp :
      ParabolicMemLpOn (Set.Ioo s₀ s₁ ×ˢ O) (2 : ℝ≥0∞) QW)
    (hQG_memLp : ∀ i : Fin d,
      ParabolicMemLpOn (Set.Ioo s₀ s₁ ×ˢ O) (2 : ℝ≥0∞)
        (fun z => QG z i))
    (hQHdiag_memLp : ∀ i : Fin d,
      ParabolicMemLpOn (Set.Ioo s₀ s₁ ×ˢ O) (2 : ℝ≥0∞)
        (fun z => QH z i i))
    (hq_time :
      HasWeakTimeDerivOn (Set.Ioo s₀ s₁ ×ˢ O) q QW)
    (hq_velocity : ∀ i : Fin d,
      HasWeakVelocityPartialDerivOn
        (Set.Ioo s₀ s₁ ×ˢ O) i q (fun z => QG z i))
    (hQG_velocity : ∀ i : Fin d,
      HasWeakVelocityPartialDerivOn
        (Set.Ioo s₀ s₁ ×ˢ O) i
        (fun z => QG z i) (fun z => QH z i i))
    (η : PDE.Vec d → ℝ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηcompact : HasCompactSupport η)
    (hηsupport : tsupport η ⊆ O)
    (ζ : ℝ → ℝ)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζcompact : HasCompactSupport ζ)
    (hζsupport : tsupport ζ ⊆ Set.Ioo s₀ s₁) :
    IntegrableOn
        (fun z =>
          ζ z.1 * QW z *
            localizedGradientDivergence η QG QH z)
        (Set.Ioo s₀ s₁ ×ˢ O) volume ∧
      IntegrableOn
        (fun z =>
          _root_.deriv ζ z.1 * η z.2 ^ 2 *
            ∑ i : Fin d, QG z i ^ 2)
        (Set.Ioo s₀ s₁ ×ˢ O) volume ∧
      2 * (∫ z in Set.Ioo s₀ s₁ ×ˢ O,
          ζ z.1 * QW z *
            localizedGradientDivergence η QG QH z
          ∂volume) =
        -(∫ z in Set.Ioo s₀ s₁ ×ˢ O,
          _root_.deriv ζ z.1 * η z.2 ^ 2 *
            ∑ i : Fin d, QG z i ^ 2
          ∂volume) := by
  let U : Set (TimeVelocity d) := Set.Ioo s₀ s₁ ×ˢ O
  let K : Set (TimeVelocity d) := tsupport ζ ×ˢ tsupport η
  have hU : IsOpen U := isOpen_Ioo.prod hO
  obtain ⟨δ, hδ, b, hb, hbCompact, hbSub, hbOne⟩ :=
    exists_common_cutoff_plateau s₀ s₁ O hO η hηcompact hηsupport
      ζ hζcompact hζsupport
  let rt : TimeVelocity d → ℝ := fun z => b z * QW z + q z * timeDerivative b z
  let ri : Fin d → TimeVelocity d → ℝ := fun i z =>
    b z * QG z i + q z * velocityGradient b z i
  let rii : Fin d → TimeVelocity d → ℝ := fun i z =>
    b z * QH z i i + 2 * velocityGradient b z i * QG z i +
      q z * velocityHessian b z i i
  rcases localized_jet_univ hU q QW QG QH hq_memLp hQW_memLp hQG_memLp
      hQHdiag_memLp hq_time hq_velocity hQG_velocity b hb hbCompact hbSub with
    ⟨hrTime, hrVelocity, hriiVelocity, hrMem, hrtMem, hriMem, hriiMem⟩
  have hlimits := localized_energy_integral_limits U η hη hηcompact ζ hζ hζcompact
    rt ri rii hrtMem hriMem hriiMem
  have hsmoothEq : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      2 * (∫ z in U, ζ z.1 * SpacetimeMollifier.spacetimeMollification ε rt z *
        localizedGradientDivergence η
          (fun z i => SpacetimeMollifier.spacetimeMollification ε (ri i) z)
          (fun z i _j => SpacetimeMollifier.spacetimeMollification ε (rii i) z) z ∂volume) =
      -(∫ z in U, _root_.deriv ζ z.1 * η z.2 ^ 2 *
        ∑ i : Fin d, SpacetimeMollifier.spacetimeMollification ε (ri i) z ^ 2
        ∂volume) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rcases common_mollifier_of_localized_jet hU q QW QG QH hq_memLp hQW_memLp
        hQG_memLp hQHdiag_memLp hq_time hq_velocity hQG_velocity
        b hb hbCompact hbSub ε hε with
      ⟨hrSmooth, hrtEq, hriEq, hriiEq, _⟩
    have hs := smoothGradient_timeEnergy s₀ s₁ O hO
      (SpacetimeMollifier.spacetimeMollification ε (fun z => b z * q z)) hrSmooth
      η hη hηcompact hηsupport ζ hζ hζcompact hζsupport
    dsimp [U, rt, ri, rii] at hrtEq hriEq hriiEq ⊢
    rw [hrtEq] at hs
    convert hs using 1 <;> congr 1 <;> apply integral_congr_ae
    · exact Filter.Eventually.of_forall fun z => by
        dsimp only
        apply congrArg (fun x : ℝ =>
          ζ z.1 * SpacetimeMollifier.spacetimeMollification ε
            (fun z => b z * QW z + q z * timeDerivative b z) z * x)
        unfold localizedGradientDivergence
        apply congrArg Neg.neg
        apply Finset.sum_congr rfl
        intro i hi
        dsimp only
        rw [← congrFun (hriEq i) z, ← congrFun (hriiEq i) z]
    · exact Filter.Eventually.of_forall fun z => by
        dsimp only
        apply congrArg (fun x : ℝ => _root_.deriv ζ z.1 * η z.2 ^ 2 * x)
        apply Finset.sum_congr rfl
        intro i hi
        rw [← congrFun (hriEq i) z]
  have hleftT := hlimits.1.const_mul 2
  have hrightT := hlimits.2.neg
  have hleftAsRight := hleftT.congr' hsmoothEq
  have hlocalIdentity := tendsto_nhds_unique hleftAsRight hrightT
  have hplateau := localized_jet_eqOn_plateau hδ q QW QG QH b hbOne
  rcases hplateau with ⟨hrEq, hrtEq, hriEq, hriiEq⟩
  have hid := weak_energy_integrands_eq_of_eqOn_cutoff_support QW rt QG QH ri rii η ζ
    (by simpa only [K, rt] using hrtEq)
    (fun i => by simpa only [K, ri] using hriEq i)
    (fun i => by simpa only [K, rii] using hriiEq i)
  have htargetInt := weak_energy_targets_integrableOn U QW QG QH hQW_memLp
    hQG_memLp hQHdiag_memLp η hη hηcompact ζ hζ hζcompact
  refine ⟨htargetInt.1, htargetInt.2, ?_⟩
  rw [show (∫ z in U, ζ z.1 * QW z * localizedGradientDivergence η QG QH z
      ∂volume) = ∫ z in U, ζ z.1 * rt z * localizedGradientDivergence η
        (fun z i => ri i z) (fun z i _j => rii i z) z ∂volume by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => (hid.1 z).symm]
  rw [show (∫ z in U, _root_.deriv ζ z.1 * η z.2 ^ 2 *
      ∑ i : Fin d, QG z i ^ 2 ∂volume) =
      ∫ z in U, _root_.deriv ζ z.1 * η z.2 ^ 2 *
        ∑ i : Fin d, ri i z ^ 2 ∂volume by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => (hid.2 z).symm]
  exact hlocalIdentity

end HypoellipticAleksandrov.Parabolic.WeakGradientTimeEnergy
