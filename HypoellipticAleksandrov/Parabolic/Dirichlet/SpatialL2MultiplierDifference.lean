module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialL2Multiplier

/-!
# Differences of bounded scalar multipliers on spatial `L²`

This file proves quotient-safe bounds for the difference of two bounded scalar
multipliers on spatial restricted-volume `L²`.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- An almost-everywhere uniform bound on two scalar coefficients' difference
bounds the difference of their induced spatial `L²` multipliers at each input. -/
theorem norm_scalarL2Multiplier_sub_apply_le_of_ae_norm_sub_le
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (q p : PDE.Vec d → ℝ)
    (hq : AEStronglyMeasurable q (PDE.volumeOn Ω))
    (hp : AEStronglyMeasurable p (PDE.volumeOn Ω))
    (Cq : ℝ) (hCq : 0 ≤ Cq)
    (hqBound : ∀ᵐ y ∂PDE.volumeOn Ω, ‖q y‖ ≤ Cq)
    (Cp : ℝ) (hCp : 0 ≤ Cp)
    (hpBound : ∀ᵐ y ∂PDE.volumeOn Ω, ‖p y‖ ≤ Cp)
    (D : ℝ) (hD : 0 ≤ D)
    (hsub : ∀ᵐ y ∂PDE.volumeOn Ω, ‖q y - p y‖ ≤ D)
    (f : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    ‖(scalarL2Multiplier q hq Cq hCq hqBound -
        scalarL2Multiplier p hp Cp hCp hpBound) f‖ ≤ D * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [
    Lp.coeFn_sub (scalarL2Multiplier q hq Cq hCq hqBound f)
      (scalarL2Multiplier p hp Cp hCp hpBound f),
    scalarL2Multiplier_apply_ae q hq Cq hCq hqBound f,
    scalarL2Multiplier_apply_ae p hp Cp hCp hpBound f,
    hsub] with y hsubApply hqApply hpApply hsubCoeff
  rw [ContinuousLinearMap.sub_apply, hsubApply, Pi.sub_apply, hqApply, hpApply, ← sub_mul,
    norm_mul]
  exact mul_le_mul hsubCoeff le_rfl (norm_nonneg _) hD

/-- An almost-everywhere uniform bound on two scalar coefficients' difference
bounds the operator norm of their induced spatial `L²` multipliers. -/
theorem norm_scalarL2Multiplier_sub_le_of_ae_norm_sub_le
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (q p : PDE.Vec d → ℝ)
    (hq : AEStronglyMeasurable q (PDE.volumeOn Ω))
    (hp : AEStronglyMeasurable p (PDE.volumeOn Ω))
    (Cq : ℝ) (hCq : 0 ≤ Cq)
    (hqBound : ∀ᵐ y ∂PDE.volumeOn Ω, ‖q y‖ ≤ Cq)
    (Cp : ℝ) (hCp : 0 ≤ Cp)
    (hpBound : ∀ᵐ y ∂PDE.volumeOn Ω, ‖p y‖ ≤ Cp)
    (D : ℝ) (hD : 0 ≤ D)
    (hsub : ∀ᵐ y ∂PDE.volumeOn Ω, ‖q y - p y‖ ≤ D) :
    ‖scalarL2Multiplier q hq Cq hCq hqBound -
        scalarL2Multiplier p hp Cp hCp hpBound‖ ≤ D := by
  apply ContinuousLinearMap.opNorm_le_bound _ hD
  intro f
  exact norm_scalarL2Multiplier_sub_apply_le_of_ae_norm_sub_le
    q p hq hp Cq hCq hqBound Cp hCp hpBound D hD hsub f

end HypoellipticAleksandrov.Parabolic.Dirichlet
