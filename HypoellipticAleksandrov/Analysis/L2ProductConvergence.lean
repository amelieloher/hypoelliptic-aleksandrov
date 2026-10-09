module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Convergence of products of strongly convergent `L²` functions

This file records convergence of scalar product integrals under strong `L²`
convergence and stability of strong `L²` convergence under a fixed `L∞`
multiplier.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace HypoellipticAleksandrov.Analysis

private theorem norm_integral_mul_le_eLpNorm_two
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : MemLp f (2 : ℝ≥0∞) μ)
    (hg : MemLp g (2 : ℝ≥0∞) μ) :
    ‖∫ x, f x * g x ∂μ‖ ≤
      (eLpNorm f (2 : ℝ≥0∞) μ).toReal *
        (eLpNorm g (2 : ℝ≥0∞) μ).toReal := by
  have hholder : (2 : ℝ).HolderConjugate 2 := by
    constructor <;> norm_num
  have hf' : MemLp f (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hf
  have hg' : MemLp g (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hg
  have hraw := integral_mul_norm_le_Lp_mul_Lq hholder hf' hg'
  have hfNorm :
      (eLpNorm f (2 : ℝ≥0∞) μ).toReal =
        (∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
    have h := congrArg ENNReal.toReal
      (hf.eLpNorm_eq_integral_rpow_norm (by norm_num) ENNReal.ofNat_ne_top)
    simp only [ENNReal.toReal_ofNat] at h
    rw [ENNReal.toReal_ofReal (by positivity)] at h
    convert h using 1
    norm_num
  have hgNorm :
      (eLpNorm g (2 : ℝ≥0∞) μ).toReal =
        (∫ x, ‖g x‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
    have h := congrArg ENNReal.toReal
      (hg.eLpNorm_eq_integral_rpow_norm (by norm_num) ENNReal.ofNat_ne_top)
    simp only [ENNReal.toReal_ofNat] at h
    rw [ENNReal.toReal_ofReal (by positivity)] at h
    convert h using 1
    norm_num
  calc
    ‖∫ x, f x * g x ∂μ‖ ≤ ∫ x, ‖f x * g x‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ = ∫ x, ‖f x‖ * ‖g x‖ ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => norm_mul _ _
    _ ≤ (∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
        (∫ x, ‖g x‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := hraw
    _ = _ := by rw [← hfNorm, ← hgNorm]

/-- Strong `L²` convergence of both factors implies convergence of their
scalar product integrals. -/
theorem tendsto_integral_mul_of_tendsto_eLpNorm_two
    {α ι : Type*} [MeasurableSpace α]
    {μ : Measure α} {l : Filter ι}
    (f g : ι → α → ℝ) (f₀ g₀ : α → ℝ)
    (hf : ∀ᶠ n in l, MemLp (f n) (2 : ℝ≥0∞) μ)
    (hg : ∀ᶠ n in l, MemLp (g n) (2 : ℝ≥0∞) μ)
    (hf₀ : MemLp f₀ (2 : ℝ≥0∞) μ)
    (hg₀ : MemLp g₀ (2 : ℝ≥0∞) μ)
    (hft : Filter.Tendsto
      (fun n => eLpNorm (fun x => f n x - f₀ x) (2 : ℝ≥0∞) μ)
      l (𝓝 0))
    (hgt : Filter.Tendsto
      (fun n => eLpNorm (fun x => g n x - g₀ x) (2 : ℝ≥0∞) μ)
      l (𝓝 0)) :
    Filter.Tendsto
      (fun n => ∫ x, f n x * g n x ∂μ)
      l (𝓝 (∫ x, f₀ x * g₀ x ∂μ)) := by
  let F : ι → ℝ≥0∞ := fun n =>
    eLpNorm (fun x => f n x - f₀ x) (2 : ℝ≥0∞) μ
  let G : ι → ℝ≥0∞ := fun n =>
    eLpNorm (fun x => g n x - g₀ x) (2 : ℝ≥0∞) μ
  have hFt : Tendsto (fun n => (F n).toReal) l (𝓝 0) := by
    simpa only [F, Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp hft
  have hGt : Tendsto (fun n => (G n).toReal) l (𝓝 0) := by
    simpa only [G, Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp hgt
  let f₀Norm : ℝ := (eLpNorm f₀ (2 : ℝ≥0∞) μ).toReal
  let g₀Norm : ℝ := (eLpNorm g₀ (2 : ℝ≥0∞) μ).toReal
  let bound : ι → ℝ := fun n =>
    (F n).toReal * ((G n).toReal + g₀Norm) + f₀Norm * (G n).toReal
  have hbound : Tendsto bound l (𝓝 0) := by
    dsimp only [bound]
    simpa only [zero_mul, mul_zero, zero_add, add_zero] using
      (hFt.mul (hGt.add tendsto_const_nhds)).add
        (tendsto_const_nhds.mul hGt)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      ?_ hbound
  filter_upwards [hf, hg] with n hfn hgn
  have hfd : MemLp (fun x => f n x - f₀ x) (2 : ℝ≥0∞) μ := by
    exact hfn.sub hf₀
  have hgd : MemLp (fun x => g n x - g₀ x) (2 : ℝ≥0∞) μ := by
    exact hgn.sub hg₀
  have hgnorm : (eLpNorm (g n) (2 : ℝ≥0∞) μ).toReal ≤
      (G n).toReal + g₀Norm := by
    have htri : eLpNorm (g n) (2 : ℝ≥0∞) μ ≤ G n + eLpNorm g₀ 2 μ := by
      have hle := eLpNorm_add_le (f := fun x => g n x - g₀ x) (g := g₀)
        (μ := μ) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      rw [show g n = (fun x => g n x - g₀ x) + g₀ by
        funext x
        simp only [Pi.add_apply]
        ring]
      exact hle
    rw [show g₀Norm = (eLpNorm g₀ 2 μ).toReal by rfl]
    exact ENNReal.toReal_le_add htri hgd.eLpNorm_ne_top hg₀.eLpNorm_ne_top
  have hprodFn : Integrable (fun x => f n x * g n x) μ := by
    exact hfn.integrable_mul hgn
  have hprod₀ : Integrable (fun x => f₀ x * g₀ x) μ := by
    exact hf₀.integrable_mul hg₀
  have hfirst : Integrable (fun x => (f n x - f₀ x) * g n x) μ := by
    exact hfd.integrable_mul hgn
  have hsecond : Integrable (fun x => f₀ x * (g n x - g₀ x)) μ := by
    exact hf₀.integrable_mul hgd
  have hint :
      (∫ x, f n x * g n x ∂μ) - ∫ x, f₀ x * g₀ x ∂μ =
        (∫ x, (f n x - f₀ x) * g n x ∂μ) +
          ∫ x, f₀ x * (g n x - g₀ x) ∂μ := by
    rw [← integral_sub hprodFn hprod₀, ← integral_add hfirst hsecond]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by ring
  rw [hint]
  calc
    ‖(∫ x, (f n x - f₀ x) * g n x ∂μ) +
        ∫ x, f₀ x * (g n x - g₀ x) ∂μ‖ ≤
        ‖∫ x, (f n x - f₀ x) * g n x ∂μ‖ +
          ‖∫ x, f₀ x * (g n x - g₀ x) ∂μ‖ := norm_add_le _ _
    _ ≤ (F n).toReal * (eLpNorm (g n) 2 μ).toReal +
        f₀Norm * (G n).toReal := by
      exact add_le_add (norm_integral_mul_le_eLpNorm_two hfd hgn)
        (norm_integral_mul_le_eLpNorm_two hf₀ hgd)
    _ ≤ bound n := by
      dsimp only [bound]
      exact add_le_add
        (mul_le_mul_of_nonneg_left hgnorm ENNReal.toReal_nonneg) le_rfl

/-- Multiplication by a fixed `L∞` scalar preserves strong `L²`
convergence. -/
theorem tendsto_eLpNorm_mul_sub_mul_of_tendsto_eLpNorm_two
    {α ι : Type*} [MeasurableSpace α]
    {μ : Measure α} {l : Filter ι}
    (a : α → ℝ) (f : ι → α → ℝ) (f₀ : α → ℝ)
    (ha : MemLp a ∞ μ)
    (hft : Filter.Tendsto
      (fun n => eLpNorm (fun x => f n x - f₀ x) (2 : ℝ≥0∞) μ)
      l (𝓝 0)) :
    Filter.Tendsto
      (fun n => eLpNorm
        (fun x => a x * f n x - a x * f₀ x)
        (2 : ℝ≥0∞) μ)
      l (𝓝 0) := by
  let C : ℝ≥0 := (eLpNorm a ∞ μ).toNNReal
  have hC : (C : ℝ≥0∞) = eLpNorm a ∞ μ := by
    exact ENNReal.coe_toNNReal ha.eLpNorm_ne_top
  have haBound : ∀ᵐ x ∂μ, ‖a x‖ₑ ≤ (C : ℝ≥0∞) := by
    rw [hC, eLpNorm_exponent_top ha.aestronglyMeasurable]
    exact enorm_ae_le_eLpNormEssSup a μ
  have hmeas : ∀ᶠ n in l,
      AEStronglyMeasurable (fun x => f n x - f₀ x) μ := by
    filter_upwards [hft.eventually_lt_const (by simp : (0 : ℝ≥0∞) < ∞)] with n hn
    exact aestronglyMeasurable_of_eLpNorm_ne_top hn.ne
  have hle (n : ι)
      (hn : AEStronglyMeasurable (fun x => f n x - f₀ x) μ) :
      eLpNorm (fun x => a x * f n x - a x * f₀ x) (2 : ℝ≥0∞) μ ≤
        C * eLpNorm (fun x => f n x - f₀ x) (2 : ℝ≥0∞) μ := by
    refine eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul' ?_ ?_ _
    · have heq : (fun x => a x * f n x - a x * f₀ x) =
          a * (fun x => f n x - f₀ x) := by
        funext x
        exact (mul_sub _ _ _).symm
      rw [heq]
      exact ha.aestronglyMeasurable.mul hn
    · filter_upwards [haBound] with x hx
      simp only [← mul_sub, enorm_mul]
      gcongr
  have hCt : Tendsto
      (fun n => (C : ℝ≥0∞) *
        eLpNorm (fun x => f n x - f₀ x) (2 : ℝ≥0∞) μ)
      l (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      (ENNReal.continuous_const_mul
        (ENNReal.coe_ne_top : (C : ℝ≥0∞) ≠ ∞)).continuousAt.tendsto.comp hft
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds
    hCt
    (Eventually.of_forall fun _ => bot_le)
    (hmeas.mono fun n hn => hle n hn)

end HypoellipticAleksandrov.Analysis
