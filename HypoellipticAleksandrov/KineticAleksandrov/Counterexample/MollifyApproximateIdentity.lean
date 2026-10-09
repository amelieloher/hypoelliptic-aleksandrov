module

public import PDEFoundation.Ambient.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Tactic.Positivity

/-!
# Bounded approximate identities on finite-measure regions

These analytic helpers use actual normalized smooth kernels. They are independent
of the Appendix C profile constructor and apply to measurable coefficients.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open Filter MeasureTheory ContinuousLinearMap
open scoped Topology Convolution ENNReal

/-- Native spatial volume is the product of the two coordinate Lebesgue Haar measures. -/
instance nativeSpatialVolume_isAddHaarMeasure (d : ℕ) :
    Measure.IsAddHaarMeasure (volume : Measure (PDE.Vec d × PDE.Vec d)) := by
  change Measure.IsAddHaarMeasure
    ((volume : Measure (PDE.Vec d)).prod (volume : Measure (PDE.Vec d)))
  let : Measure.IsAddHaarMeasure (volume : Measure (PDE.Vec d)) :=
    isAddHaarMeasure_volume_pi (Fin d)
  exact Measure.prod.instIsAddHaarMeasure _ _

/-- Bounded almost-everywhere convergence implies finite-exponent norm convergence. -/
theorem bounded_convergence_eLpNorm {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsFiniteMeasure ν] (p : ℝ≥0∞) (hp0 : p ≠ 0) (hp : p ≠ ∞)
    (F : ℕ → X → ℝ) (hF : ∀ n, AEStronglyMeasurable (F n) ν)
    (C : ℝ) (hbound : ∀ n, ∀ᵐ x ∂ν, ‖F n x‖ ≤ C)
    (hlim : ∀ᵐ x ∂ν, Tendsto (fun n => F n x) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (F n) p ν) atTop (𝓝 0) := by
  have hpow : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hi : Tendsto (fun n => ∫⁻ x, ‖F n x‖ₑ ^ p.toReal ∂ν) atTop (𝓝 0) := by
    have hh := tendsto_lintegral_of_dominated_convergence'
      (μ := ν) (F := fun n x => ‖F n x‖ₑ ^ p.toReal) (f := fun _ => 0)
      (fun _ => ENNReal.ofReal C ^ p.toReal)
      (fun n => (hF n).enorm.pow_const p.toReal) ?_ ?_ ?_
    · simpa only [lintegral_zero] using! hh
    · intro n
      filter_upwards [hbound n] with x hx
      apply ENNReal.rpow_le_rpow _ hpow.le
      simpa only [ofReal_norm] using! ENNReal.ofReal_le_ofReal hx
    · simp only [lintegral_const]
      exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hpow.le
        ENNReal.ofReal_ne_top) (measure_ne_top ν Set.univ)
    · filter_upwards [hlim] with x hx
      have hn : Tendsto (fun n => ‖F n x‖ₑ) atTop (𝓝 0) := by
        simpa only [Function.comp_apply, enorm_zero] using!
          (continuous_enorm.tendsto (0 : ℝ)).comp hx
      simpa only [Function.comp_apply, ENNReal.zero_rpow_of_pos hpow] using!
        (ENNReal.continuous_rpow_const (y := p.toReal).tendsto (0 : ℝ≥0∞)).comp hn
  have hr := (ENNReal.continuous_rpow_const (y := 1 / p.toReal).tendsto
    (0 : ℝ≥0∞)).comp hi
  have hresult : Tendsto (fun n =>
      (∫⁻ x, ‖F n x‖ₑ ^ p.toReal ∂ν) ^ (1 / p.toReal)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, ENNReal.zero_rpow_of_pos (one_div_pos.mpr hpow)] using! hr
  apply hresult.congr
  intro n
  exact (eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp (hF n)).symm

section Kernels
variable {G : Type*} [NormedAddCommGroup G]

/-- A smooth spatial kernel with inner radius half its specified outer radius. -/
def spatialMollifier (h : ℝ) (hh : 0 < h) : ContDiffBump (0 : G) where
  rIn := h / 2
  rOut := h
  rIn_pos := half_pos hh
  rIn_lt_rOut := half_lt_self hh

/-- A concrete family of kernels at scales `1/(n+1)`. -/
def standardMollifierSequence (n : ℕ) : ContDiffBump (0 : G) :=
  spatialMollifier (1 / ((n : ℝ) + 1)) (by positivity)

/-- The concrete kernels have radii tending to zero. -/
theorem standardMollifierSequence_rOut_tendsto :
    Tendsto (fun n => (standardMollifierSequence (G := G) n).rOut) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- Uniform inner-to-outer radius ratio for the concrete kernels. -/
theorem standardMollifierSequence_radius_ratio (n : ℕ) :
    (standardMollifierSequence (G := G) n).rOut ≤
      2 * (standardMollifierSequence (G := G) n).rIn := by
  change 1 / ((n : ℝ) + 1) ≤ 2 * (1 / ((n : ℝ) + 1) / 2)
  linarith

end Kernels

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [MeasureSpace G] [BorelSpace G] [FiniteDimensional ℝ G]
   [Measure.IsAddHaarMeasure (volume : Measure G)]

omit [BorelSpace G] in
/-- A bounded measurable function on the spatial carrier is locally integrable. -/
theorem bounded_locallyIntegrable (g : G → ℝ)
    (hg : AEStronglyMeasurable g volume) (C : ℝ) (hbound : ∀ x, ‖g x‖ ≤ C) :
    LocallyIntegrable g volume := by
  apply locallyIntegrable_iff.mpr
  intro k hk
  let : IsFiniteMeasure (volume.restrict k) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hk.measure_lt_top⟩
  exact ⟨hg.restrict, HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall hbound)⟩

/-- Spatial smoothing by an actual normalized bump kernel. -/
def spatialMollify (φ : ContDiffBump (0 : G)) (g : G → ℝ) : G → ℝ :=
  φ.normed volume ⋆[lsmul ℝ ℝ, volume] g

/-- Bounded input gives the same uniform bound after normalized convolution. -/
theorem spatialMollify_norm_le (φ : ContDiffBump (0 : G)) (g : G → ℝ)
    (hg : AEStronglyMeasurable g volume) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x, ‖g x‖ ≤ C) (x : G) : ‖spatialMollify φ g x‖ ≤ C := by
  have h := dist_convolution_le (μ := volume) (x₀ := x) (z₀ := (0 : ℝ)) hC
    φ.support_normed_eq.subset φ.nonneg_normed φ.integral_normed hg
    (fun y _ => by simpa only [dist_zero_right] using! hbound y)
  simpa only [spatialMollify, dist_zero_right] using! h

/-- Spatial convolution is smooth; this does not assert joint time smoothness. -/
theorem spatialMollify_contDiff (φ : ContDiffBump (0 : G)) (g : G → ℝ)
    (hg : LocallyIntegrable g volume) :
    ContDiff ℝ (⊤ : ℕ∞) (spatialMollify φ g) :=
  φ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
    φ.contDiff_normed hg

/-- Bounded normalized convolutions converge in every finite norm on a finite region. -/
theorem spatialMollify_sub_tendsto (φ : ℕ → ContDiffBump (0 : G))
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0))
    (K : ℝ) (hK : ∀ᶠ n in atTop, (φ n).rOut ≤ K * (φ n).rIn)
    (g : G → ℝ) (hg : LocallyIntegrable g volume)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, ‖g x‖ ≤ C)
    (S : Set G) [IsFiniteMeasure (volume.restrict S)]
    (p : ℝ≥0∞) (hp0 : p ≠ 0) (hp : p ≠ ∞) :
    Tendsto (fun n => eLpNorm (fun x => spatialMollify (φ n) g x - g x)
      p (volume.restrict S)) atTop (𝓝 0) := by
  have hmeas := hg.aestronglyMeasurable
  apply bounded_convergence_eLpNorm (volume.restrict S) p hp0 hp
    (fun n x => spatialMollify (φ n) g x - g x)
    (fun n => ((spatialMollify_contDiff (φ n) g hg).continuous.aestronglyMeasurable.sub
      hmeas).restrict) (2 * C)
  · intro n
    exact Filter.Eventually.of_forall fun x => (norm_sub_le _ _).trans
      (by linarith only [spatialMollify_norm_le (φ n) g hmeas C hC hbound x, hbound x])
  · have ha := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hφ hK hg
    filter_upwards [ae_restrict_of_ae ha] with x hx
    simpa only [sub_self] using! hx.sub_const (g x)

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
