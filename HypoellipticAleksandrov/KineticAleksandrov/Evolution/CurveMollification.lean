module

import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.CurveLipschitz

/-!
# Mollification of Lipschitz curves

Used in the proof of Proposition 2.1: a globally `L`-Lipschitz continuous curve
`γ : ℝ → Vec n` (for instance the slab extension of a continuous piecewise `C¹` curve) is
uniformly approximated, within any prescribed `ε > 0`, by smooth curves `g` that are *still*
`L`-Lipschitz for the Euclidean norm.  The approximant is the convolution with a normalised
smooth bump `ρ` supported in `[-δ, δ]`, where `L δ ≤ ε`.

The Euclidean norm of a weighted integral is estimated by the duality argument
`‖v‖² = ∫ ρ ⟨v, f⟩ ≤ ‖v‖ c`.
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov

open Set MeasureTheory
open scoped Convolution

/-- The mollification `∫ ρ(t) γ(s - t) dt` of a curve by a weight `ρ`. -/
noncomputable def curveMollify {n : ℕ} (ρ : ℝ → ℝ) (γ : ℝ → PDE.Vec n) (s : ℝ) : PDE.Vec n :=
  ∫ t, ρ t • γ (s - t)

section Weighted

variable {ρ : ℝ → ℝ} (hρ0 : ∀ t, 0 ≤ ρ t) (hρc : Continuous ρ) (hρs : HasCompactSupport ρ)
  (hρ1 : ∫ t, ρ t = 1)

include hρc hρs in
theorem integrable_weight_smul {n : ℕ} {f : ℝ → PDE.Vec n} (hf : Continuous f) :
    Integrable (fun t => ρ t • f t) :=
  (hρc.smul hf).integrable_of_hasCompactSupport (hρs.smul_right)

include hρc hρs in
theorem integrable_weight_mul {g : ℝ → ℝ} (hg : Continuous g) :
    Integrable (fun t => ρ t * g t) :=
  (hρc.mul hg).integrable_of_hasCompactSupport (hρs.mul_right)

include hρ0 hρc hρs hρ1 in
/-- A weighted average (weight a continuous compactly supported probability density) of a
continuous curve has Euclidean norm at most the bound `c` of the integrand on the support. -/
theorem vecEuclideanNorm_weighted_integral_le {n : ℕ} {f : ℝ → PDE.Vec n}
    (hf : Continuous f) {c : ℝ} (hc : 0 ≤ c)
    (hbd : ∀ t, ρ t ≠ 0 → PDE.vecEuclideanNorm (f t) ≤ c) :
    PDE.vecEuclideanNorm (∫ t, ρ t • f t) ≤ c := by
  set v : PDE.Vec n := ∫ t, ρ t • f t with hv
  have hcoord : ∀ i, v i = ∫ t, ρ t * f t i := by
    intro i
    have := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).integral_comp_comm
      (integrable_weight_smul hρc hρs hf)
    simpa using this.symm
  have hint : ∀ i, Integrable (fun t => ρ t * f t i) := fun i =>
    integrable_weight_mul hρc hρs (continuous_apply i |>.comp hf)
  have hsq : PDE.vecNormSq v = ∫ t, ρ t * PDE.vecDot v (f t) := by
    unfold PDE.vecNormSq PDE.vecDot
    have : ∀ i, v i * v i = ∫ t, ρ t * (v i * f t i) := by
      intro i
      calc v i * v i = v i * ∫ t, ρ t * f t i := by rw [← hcoord i]
        _ = ∫ t, ρ t * (v i * f t i) := by
          rw [← integral_const_mul]
          congr 1; funext t; ring
    simp_rw [this]
    rw [← integral_finsetSum]
    · congr 1; funext t
      rw [Finset.mul_sum]
    · intro i _
      have := (hint i).const_mul (v i)
      refine this.congr (Filter.Eventually.of_forall fun t => ?_)
      simp only; ring
  have hle : PDE.vecNormSq v ≤ PDE.vecEuclideanNorm v * c := by
    rw [hsq]
    have h1 : ∫ t, ρ t * PDE.vecDot v (f t) ≤ ∫ t, ρ t * (PDE.vecEuclideanNorm v * c) := by
      refine integral_mono ?_ ?_ fun t => ?_
      · have : Continuous fun t => PDE.vecDot v (f t) := by
          unfold PDE.vecDot; fun_prop
        exact integrable_weight_mul hρc hρs this
      · exact integrable_weight_mul hρc hρs continuous_const
      · by_cases h : ρ t = 0
        · simp [h]
        · refine mul_le_mul_of_nonneg_left ?_ (hρ0 t)
          exact (le_abs_self _).trans
            ((PDE.abs_vecDot_le_vecEuclideanNorm_mul _ _).trans
              (mul_le_mul_of_nonneg_left (hbd t h) (PDE.vecEuclideanNorm_nonneg _)))
    have h2 : ∫ t, ρ t * (PDE.vecEuclideanNorm v * c) = PDE.vecEuclideanNorm v * c := by
      rw [integral_mul_const, hρ1, one_mul]
    linarith
  by_contra hcon
  push Not at hcon
  have hpos : 0 < PDE.vecEuclideanNorm v := hc.trans_lt hcon
  have : PDE.vecEuclideanNorm v ^ 2 ≤ PDE.vecEuclideanNorm v * c := by
    rwa [PDE.vecEuclideanNorm_sq]
  nlinarith

include hρc hρs in
/-- Difference of two mollifications. -/
theorem curveMollify_sub {n : ℕ} {γ : ℝ → PDE.Vec n} (hγ : Continuous γ) (s s' : ℝ) :
    curveMollify ρ γ s - curveMollify ρ γ s' = ∫ t, ρ t • (γ (s - t) - γ (s' - t)) := by
  unfold curveMollify
  rw [← integral_sub]
  · congr 1; funext t; rw [smul_sub]
  · exact integrable_weight_smul hρc hρs (hγ.comp (continuous_const.sub continuous_id))
  · exact integrable_weight_smul hρc hρs (hγ.comp (continuous_const.sub continuous_id))

include hρc hρs hρ1 in
/-- Difference between the mollification and the curve itself. -/
theorem curveMollify_sub_self {n : ℕ} {γ : ℝ → PDE.Vec n} (hγ : Continuous γ) (s : ℝ) :
    curveMollify ρ γ s - γ s = ∫ t, ρ t • (γ (s - t) - γ s) := by
  unfold curveMollify
  simp_rw [smul_sub]
  rw [integral_sub, integral_smul_const, hρ1, one_smul]
  · exact integrable_weight_smul hρc hρs (hγ.comp (continuous_const.sub continuous_id))
  · exact (hρc.integrable_of_hasCompactSupport hρs).smul_const _

end Weighted

/-- The mollification is the convolution with the weight, for the scalar action. -/
theorem curveMollify_eq_convolution {n : ℕ} (ρ : ℝ → ℝ) (γ : ℝ → PDE.Vec n) :
    curveMollify ρ γ = ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] γ := by
  funext s
  simp [curveMollify, convolution_def]

/-- **Analytic core of the curve approximation.**  A globally `L`-Lipschitz curve is uniformly
`ε`-approximated by a smooth curve which is globally `L`-Lipschitz for the Euclidean norm. -/
theorem exists_smooth_lipschitz_approx {n : ℕ} {γ : ℝ → PDE.Vec n} (hγ : Continuous γ)
    {L : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ s t, PDE.vecEuclideanNorm (γ s - γ t) ≤ L * |s - t|) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ → PDE.Vec n, ContDiff ℝ (⊤ : ℕ∞) g ∧
      (∀ s t, PDE.vecEuclideanNorm (g s - g t) ≤ L * |s - t|) ∧
      ∀ s, PDE.vecEuclideanNorm (g s - γ s) ≤ ε := by
  set δ : ℝ := ε / (L + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  let φ : ContDiffBump (0 : ℝ) := ⟨δ / 2, δ, half_pos hδ0, half_lt_self hδ0⟩
  have hρ0 : ∀ t, 0 ≤ φ.normed volume t := fun t => φ.nonneg_normed t
  have hρc : Continuous (φ.normed volume) := φ.continuous_normed
  have hρs : HasCompactSupport (φ.normed volume) := φ.hasCompactSupport_normed
  have hρ1 : ∫ t, φ.normed volume t = 1 := φ.integral_normed
  have hsupp : ∀ t, φ.normed volume t ≠ 0 → |t| < δ := by
    intro t ht
    have : t ∈ Function.support (φ.normed volume) := ht
    rw [φ.support_normed_eq] at this
    simpa [Metric.mem_ball, Real.dist_eq] using this
  refine ⟨curveMollify (φ.normed volume) γ, ?_, ?_, ?_⟩
  · rw [curveMollify_eq_convolution]
    exact hρs.contDiff_convolution_left _ φ.contDiff_normed (hγ.locallyIntegrable (μ := volume))
  · intro s s'
    rw [curveMollify_sub hρc hρs hγ]
    refine vecEuclideanNorm_weighted_integral_le hρ0 hρc hρs hρ1 ?_ (by positivity) fun t _ => ?_
    · exact (hγ.comp (continuous_const.sub continuous_id)).sub
        (hγ.comp (continuous_const.sub continuous_id))
    · refine (hLip _ _).trans (le_of_eq ?_)
      congr 2; ring
  · intro s
    rw [curveMollify_sub_self hρc hρs hρ1 hγ]
    refine vecEuclideanNorm_weighted_integral_le hρ0 hρc hρs hρ1 ?_ hε.le fun t ht => ?_
    · exact (hγ.comp (continuous_const.sub continuous_id)).sub continuous_const
    · refine (hLip _ _).trans ?_
      have h1 : |s - t - s| < δ := by rw [show s - t - s = -t by ring, abs_neg]; exact hsupp t ht
      calc L * |s - t - s| ≤ L * δ := mul_le_mul_of_nonneg_left h1.le hL
        _ = ε * (L / (L + 1)) := by rw [hδ]; ring
        _ ≤ ε * 1 := mul_le_mul_of_nonneg_left (by rw [div_le_one (by positivity)]; linarith)
            hε.le
        _ = ε := mul_one ε

end HypoellipticAleksandrov.KineticAleksandrov
