module

public import HypoellipticAleksandrov.KineticAleksandrov.Reconstruction.FourierInversion
public import PDEFoundation.Ambient.EuclideanNorm
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Fourier inversion on the native carrier `PDE.Vec d`

This module transports `eq_withDensity_invDensity` from the Euclidean space
`EuclideanSpace ℝ (Fin d)` to the project's coordinate carrier `PDE.Vec d = Fin d → ℝ` with the
product Lebesgue measure and the dot product `PDE.vecDot`.  A finite measure `μ` on `ℝ^d` whose
Fourier transform `ξ ↦ ∫ e^{-i ξ·x} dμ(x)` is integrable has the continuous nonnegative density
`z ↦ (2π)^{-d} Re ∫ e^{i ξ·z} μ̂(ξ) dξ`, bounded by `(2π)^{-d} ‖μ̂‖₁`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Complex Filter Topology
open scoped ENNReal

namespace HypoellipticAleksandrov.KineticAleksandrov.Reconstruction

variable {d : ℕ}

/-- The Fourier transform `ξ ↦ ∫ e^{-i ξ·x} dμ(x)` of a measure on `ℝ^d`. -/
def vecFourier (μ : Measure (PDE.Vec d)) (ξ : PDE.Vec d) : ℂ :=
  ∫ x, cexp (-((PDE.vecDot ξ x : ℝ) * I)) ∂μ

/-- The Fourier-inversion integral `∫ e^{i ξ·z} φ(ξ) dξ` on `ℝ^d`. -/
def vecInvIntegral (φ : PDE.Vec d → ℂ) (z : PDE.Vec d) : ℂ :=
  ∫ ξ, cexp (I * ((PDE.vecDot ξ z : ℝ) : ℂ)) * φ ξ

/-- The inversion density `(2π)^{-d} Re ∫ e^{i ξ·z} μ̂(ξ) dξ` of a measure on `ℝ^d`. -/
def vecInvDensity (μ : Measure (PDE.Vec d)) (z : PDE.Vec d) : ℝ :=
  ((2 * Real.pi) ^ d)⁻¹ * (vecInvIntegral (vecFourier μ) z).re


/-- The coordinate equivalence `ℝ^d ≃ EuclideanSpace ℝ (Fin d)`. -/
abbrev toEuclid (d : ℕ) : PDE.Vec d ≃ᵐ EuclideanSpace ℝ (Fin d) :=
  MeasurableEquiv.toLp 2 (PDE.Vec d)

/-- The Euclidean inner product of coordinate vectors is `PDE.vecDot`. -/
lemma inner_toLp (ξ x : PDE.Vec d) :
    inner ℝ (WithLp.toLp 2 ξ : EuclideanSpace ℝ (Fin d)) (WithLp.toLp 2 x) = PDE.vecDot ξ x := by
  simp only [PiLp.inner_apply, PDE.vecDot, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The Fourier transform on `ℝ^d` agrees with that of the pushforward to Euclidean space. -/
lemma vecFourier_eq (μ : Measure (PDE.Vec d)) (ξ : PDE.Vec d) :
    measureFourier (μ.map (toEuclid d)) (WithLp.toLp 2 ξ) = vecFourier μ ξ := by
  unfold measureFourier vecFourier
  rw [(toEuclid d).measurableEmbedding.integral_map]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [toEuclid, MeasurableEquiv.toLp_apply, inner_toLp]

/-- The inversion integral agrees with that of the pushforward to Euclidean space. -/
lemma invIntegral_eq (μ : Measure (PDE.Vec d)) (z : PDE.Vec d) :
    invIntegral (measureFourier (μ.map (toEuclid d))) (WithLp.toLp 2 z) =
      vecInvIntegral (vecFourier μ) z := by
  unfold invIntegral vecInvIntegral
  rw [← (PiLp.volume_preserving_toLp (Fin d)).integral_comp
    (toEuclid d).measurableEmbedding]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [inner_toLp, vecFourier_eq]

/-- The inversion density agrees with that of the pushforward to Euclidean space. -/
lemma invDensity_eq (μ : Measure (PDE.Vec d)) (z : PDE.Vec d) :
    invDensity (μ.map (toEuclid d)) (WithLp.toLp 2 z) = vecInvDensity μ z := by
  unfold invDensity vecInvDensity
  rw [invIntegral_eq, finrank_euclideanSpace_fin]

/-- Integrability of the Fourier transform is preserved by the coordinate equivalence. -/
lemma integrable_vecFourier_iff (μ : Measure (PDE.Vec d)) :
    Integrable (measureFourier (μ.map (toEuclid d))) ↔ Integrable (vecFourier μ) := by
  rw [← (PiLp.volume_preserving_toLp (Fin d)).integrable_comp_emb
    (toEuclid d).measurableEmbedding]
  refine integrable_congr (Filter.Eventually.of_forall fun ξ => ?_)
  exact vecFourier_eq μ ξ


/-- The `L^1` norm of the Fourier transform is preserved by the coordinate equivalence. -/
lemma integral_norm_vecFourier (μ : Measure (PDE.Vec d)) :
    ∫ ξ, ‖measureFourier (μ.map (toEuclid d)) ξ‖ = ∫ ξ, ‖vecFourier μ ξ‖ := by
  rw [← (PiLp.volume_preserving_toLp (Fin d)).integral_comp (toEuclid d).measurableEmbedding]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ξ => by
    simp only [vecFourier_eq])

section Inversion

variable (μ : Measure (PDE.Vec d)) [IsFiniteMeasure μ] (hφ : Integrable (vecFourier μ))
include hφ

/-- The inversion density of a finite measure with integrable Fourier transform is nonnegative. -/
theorem vecInvDensity_nonneg (z : PDE.Vec d) : 0 ≤ vecInvDensity μ z := by
  rw [← invDensity_eq]
  exact invDensity_nonneg _ ((integrable_vecFourier_iff μ).2 hφ) _

/-- The inversion density is bounded by `(2π)^{-d} ‖μ̂‖₁`. -/
theorem vecInvDensity_le (z : PDE.Vec d) :
    vecInvDensity μ z ≤ ((2 * Real.pi) ^ d)⁻¹ * ∫ ξ, ‖vecFourier μ ξ‖ := by
  have h := invDensity_le (μ.map (toEuclid d)) ((integrable_vecFourier_iff μ).2 hφ)
    (WithLp.toLp 2 z)
  rwa [invDensity_eq, integral_norm_vecFourier, finrank_euclideanSpace_fin] at h

omit [IsFiniteMeasure μ] in
/-- The inversion density is continuous. -/
theorem continuous_vecInvDensity : Continuous (vecInvDensity μ) := by
  have h := continuous_invDensity (μ.map (toEuclid d)) ((integrable_vecFourier_iff μ).2 hφ)
  have : vecInvDensity μ = invDensity (μ.map (toEuclid d)) ∘ (WithLp.toLp 2) :=
    funext fun z => (invDensity_eq μ z).symm
  rw [this]
  exact h.comp (PiLp.continuous_toLp 2 _)

/-- Fourier inversion on `ℝ^d`: a finite measure with integrable Fourier transform has the
density `vecInvDensity μ` with respect to Lebesgue measure. -/
theorem eq_withDensity_vecInvDensity :
    μ = volume.withDensity (fun z => ENNReal.ofReal (vecInvDensity μ z)) := by
  have h := eq_withDensity_invDensity (μ.map (toEuclid d)) ((integrable_vecFourier_iff μ).2 hφ)
  ext S hS
  have he := (toEuclid d).measurableEmbedding
  have h1 : μ S = (μ.map (toEuclid d)) (toEuclid d '' S) := by
    rw [he.map_apply, (toEuclid d).injective.preimage_image]
  rw [h1, h, withDensity_apply _ (he.measurableSet_image.2 hS), withDensity_apply _ hS]
  calc ∫⁻ a in toEuclid d '' S, ENNReal.ofReal (invDensity (μ.map (toEuclid d)) a)
      = ∫⁻ a in S, ENNReal.ofReal (invDensity (μ.map (toEuclid d)) (toEuclid d a)) :=
        ((PiLp.volume_preserving_toLp (Fin d)).setLIntegral_comp_emb he
          (fun a => ENNReal.ofReal (invDensity (μ.map (toEuclid d)) a)) S).symm
    _ = _ := setLIntegral_congr_fun hS fun z _ => by
        simp only [toEuclid, MeasurableEquiv.toLp_apply, invDensity_eq]

end Inversion

end HypoellipticAleksandrov.KineticAleksandrov.Reconstruction
