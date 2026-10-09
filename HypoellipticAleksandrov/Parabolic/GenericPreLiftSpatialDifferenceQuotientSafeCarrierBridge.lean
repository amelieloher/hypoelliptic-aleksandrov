module

public import HypoellipticAleksandrov.Parabolic.GenericPreLiftSpatialDifferenceQuotientPointwiseCoercivity
public import HypoellipticAleksandrov.Parabolic.WeakJetProduct
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Safe-carrier integrated coercivity

This module integrates the generic pointwise spatial difference-quotient
coercivity estimate on a shift-safe carrier and transports only terms supported
by the cutoff to the surrounding carrier.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory Set
open scoped Convex ENNReal MatrixOrder

private theorem setIntegral_eq_setIntegral_of_subset_of_eq_zero
    {d : ℕ} {V S : Set (TimeVelocity d)} (hS : MeasurableSet S)
    (hV : MeasurableSet V) (hVS : V ⊆ S) (f : TimeVelocity d → ℝ)
    (hoff : ∀ z ∈ S, z ∉ V → f z = 0) :
    ∫ z in S, f z = ∫ z in V, f z := by
  rw [← integral_indicator hS, ← integral_indicator hV]
  apply integral_congr_ae
  exact ae_of_all _ fun z ↦ by
    by_cases hzV : z ∈ V
    · simp only [Set.indicator_of_mem hzV, Set.indicator_of_mem (hVS hzV)]
    · by_cases hzS : z ∈ S
      · simp only [Set.indicator_of_mem hzS, Set.indicator_of_notMem hzV,
          hoff z hzS hzV]
      · simp only [Set.indicator_of_notMem hzS, Set.indicator_of_notMem hzV]

/-- Integrate the fixed-direction coercivity estimate on a shift-safe carrier,
then transport only the cutoff-supported energy and flux terms to the outer
carrier. -/
theorem setIntegral_fixedDirection_fluxPairing_coercive_absorbed_on_safeCarrier
    {d : ℕ} {V S : Set (TimeVelocity d)}
    (hS : MeasurableSet S) (hV : MeasurableSet V) (hVS : V ⊆ S)
    (A : TimeVelocity d → PDE.Mat d)
    (G H : Fin d → TimeVelocity d → ℝ)
    (w Q : TimeVelocity d → ℝ) (k : Fin d)
    (h lam Lam Ma Keta : ℝ)
    (hd : 0 < d) (hlam : 0 < lam)
    (hMa : 0 ≤ Ma) (hKeta : 0 ≤ Keta)
    (hwMeas : AEStronglyMeasurable w (timeVelocityVolumeOn V))
    (hw : ∀ z ∈ V, 0 ≤ w z)
    (hwLe : ∀ z ∈ V, w z ≤ 1)
    (hOff : ∀ z ∈ S, z ∉ V →
      w z = 0 ∧ ∀ i, velocityGradient w z i = 0)
    (hEll : ∀ z ∈ V,
      lam • (1 : PDE.Mat d) ≤ A (spatialShift k h z) ∧
        A (spatialShift k h z) ≤ Lam • (1 : PDE.Mat d))
    (hAquot : ∀ z ∈ V, ∀ i j,
      |spatialDifferenceQuotient k h (fun x ↦ A x i j) z| ≤ Ma)
    (hDwSq : ∀ z ∈ V, ∀ i,
      velocityGradient w z i ^ 2 ≤ 4 * Keta ^ 2 * w z)
    (hQ : ParabolicMemLpOn V 2 Q)
    (hG : ∀ j, ParabolicMemLpOn V 2 (G j))
    (hH : ∀ i, ParabolicMemLpOn V 2 (H i))
    (hDsupport : ∀ i, tsupport (fun z ↦
      velocityGradient w z i * Q z + w z * H i z) ⊆ V)
    (hFlux : ∀ i, Integrable (fun z ↦
      (∑ j : Fin d,
        (spatialTranslate k h (fun x ↦ A x i j) z * H j z +
          spatialDifferenceQuotient k h (fun x ↦ A x i j) z * G j z)) *
        (velocityGradient w z i * Q z + w z * H i z))
      (timeVelocityVolumeOn S)) :
    (lam / 2) * ∫ z in S, w z * ∑ i : Fin d, H i z ^ 2 ≤
      (∑ i : Fin d, ∫ z in S,
        (∑ j : Fin d,
          (spatialTranslate k h (fun x ↦ A x i j) z * H j z +
            spatialDifferenceQuotient k h (fun x ↦ A x i j) z * G j z)) *
          (velocityGradient w z i * Q z + w z * H i z)) +
      (8 * (d : ℝ) ^ 3 / lam * Lam ^ 2 * Keta ^ 2 +
        2 * (d : ℝ) ^ 2 / lam * Ma ^ 2 +
        ((d : ℝ) ^ 2 + (d : ℝ)) * Ma * Keta) *
        ((∫ z in V, Q z ^ 2) +
          ∑ j : Fin d, ∫ z in V, G j z ^ 2) := by
  have _hMa : 0 ≤ Ma := hMa
  let Gamma : ℝ :=
    8 * (d : ℝ) ^ 3 / lam * Lam ^ 2 * Keta ^ 2 +
      2 * (d : ℝ) ^ 2 / lam * Ma ^ 2 +
      ((d : ℝ) ^ 2 + (d : ℝ)) * Ma * Keta
  have hsumHInt : Integrable (fun z ↦ ∑ i : Fin d, H i z ^ 2)
      (timeVelocityVolumeOn V) :=
    integrable_finset_sum _ fun i _ ↦ (hH i).integrable_sq
  have hweightedHInt : Integrable (fun z ↦ w z * ∑ i : Fin d, H i z ^ 2)
      (timeVelocityVolumeOn V) := by
    refine Integrable.mono' hsumHInt (hwMeas.mul hsumHInt.1) ?_
    filter_upwards [ae_restrict_mem hV] with z hz
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw z hz),
      abs_of_nonneg (Finset.sum_nonneg fun i _ ↦ sq_nonneg (H i z))]
    exact mul_le_of_le_one_left
      (Finset.sum_nonneg fun i _ ↦ sq_nonneg (H i z)) (hwLe z hz)
  have hdataInt : Integrable (fun z ↦ Q z ^ 2 + ∑ j : Fin d, G j z ^ 2)
      (timeVelocityVolumeOn V) :=
    hQ.integrable_sq.add (integrable_finset_sum _ fun j _ ↦ (hG j).integrable_sq)
  let flux (i : Fin d) (z : TimeVelocity d) : ℝ :=
    (∑ j : Fin d,
      (spatialTranslate k h (fun x ↦ A x i j) z * H j z +
        spatialDifferenceQuotient k h (fun x ↦ A x i j) z * G j z)) *
      (velocityGradient w z i * Q z + w z * H i z)
  have hFluxV (i : Fin d) : Integrable (flux i) (timeVelocityVolumeOn V) :=
    (hFlux i).mono_measure (Measure.restrict_mono_set volume hVS)
  have hfluxSumInt : Integrable (fun z ↦ ∑ i : Fin d, flux i z)
      (timeVelocityVolumeOn V) :=
    integrable_finset_sum _ fun i _ ↦ hFluxV i
  have hpoint : ∀ z ∈ V,
      (lam / 2) * (w z * ∑ i : Fin d, H i z ^ 2) ≤
        (∑ i : Fin d, flux i z) +
          Gamma * (Q z ^ 2 + ∑ j : Fin d, G j z ^ 2) := by
    intro z hz
    simpa only [Gamma, flux, mul_assoc] using
      fixedDirection_fluxPairing_coercive_absorbed A (fun j ↦ G j z)
        (fun i ↦ H i z) (fun i ↦ velocityGradient w z i) (Q z) k h z
        hd hlam hKeta (hw z hz) (hwLe z hz) (hEll z hz)
        (hAquot z hz) (hDwSq z hz)
  have hmono := integral_mono_ae
    (hweightedHInt.const_mul (lam / 2))
    (hfluxSumInt.add (hdataInt.const_mul Gamma))
    (by
      filter_upwards [ae_restrict_mem hV] with z hz
      simpa only [mul_assoc, Pi.add_apply] using hpoint z hz)
  simp only [Pi.add_apply] at hmono
  rw [integral_const_mul,
    integral_add hfluxSumInt (hdataInt.const_mul Gamma),
    integral_finset_sum _ (fun i _ ↦ hFluxV i), integral_const_mul,
    integral_add hQ.integrable_sq
      (integrable_finset_sum _ fun j _ ↦ (hG j).integrable_sq),
    integral_finset_sum _ (fun j _ ↦ (hG j).integrable_sq)] at hmono
  have henergyEq : (∫ z in S, w z * ∑ i : Fin d, H i z ^ 2) =
      ∫ z in V, w z * ∑ i : Fin d, H i z ^ 2 := by
    apply setIntegral_eq_setIntegral_of_subset_of_eq_zero hS hV hVS
    intro z hzS hzV
    rw [(hOff z hzS hzV).1, zero_mul]
  have hfluxEq (i : Fin d) : (∫ z in S, flux i z) = ∫ z in V, flux i z := by
    apply setIntegral_eq_setIntegral_of_subset_of_eq_zero hS hV hVS
    intro z _ hzV
    have hDzero : velocityGradient w z i * Q z + w z * H i z = 0 := by
      by_contra hne
      exact hzV (hDsupport i (subset_closure hne))
    simp only [flux, hDzero, mul_zero]
  rw [henergyEq]
  change (lam / 2) * ∫ z in V, w z * ∑ i : Fin d, H i z ^ 2 ≤
    (∑ i : Fin d, ∫ z in S, flux i z) + Gamma *
      ((∫ z in V, Q z ^ 2) + ∑ j : Fin d, ∫ z in V, G j z ^ 2)
  simp_rw [hfluxEq]
  exact hmono

end HypoellipticAleksandrov.Parabolic
