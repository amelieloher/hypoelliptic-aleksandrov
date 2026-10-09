module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionUniformExtended
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionUniformTime
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionMollifyBound

/-! # Uniform bounds on the actual spatially mollified operator -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory Set HypoellipticAleksandrov.Parabolic

/-- The actual operator is bounded uniformly over all smoothing radii on a bounded
velocity region and compact time interval. All convolution bounds are essential bounds
of the selected representatives, rather than assumptions on the classical derivatives. -/
theorem construction_smoothedOperator_uniform_bound {d : ℕ} (hd : 1 ≤ d)
    {alpha : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1)
    (h : CounterProfileStatement d alpha) (r mu R m a b S : ℝ)
    (hr : 0 < r) (hmu : 0 < mu) (hR : 0 < R) (hm : m < R ^ 2) (hS : 0 ≤ S)
    (hscale : 2 * Real.rpow r alpha ≤ 1)
    (hmargin : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 < m)
    (A : XV d → PDE.Mat d) (AC : ℝ) (hAC : 0 ≤ AC)
    (hAb : ∀ q i k, |A q i k| ≤ AC) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ phi : ContDiffBump (0 : XV d), ∀ P : KineticPoint d,
      P.time ∈ Icc a b → (∀ i, |P.velocity i| ≤ S) →
      |backwardOperator (fun _t x v => A (x, v))
        (smoothedZeroExtendedProfile h r mu R phi) P| ≤ C := by
  have hg (i : Fin d) := construction_extendedGradient_uniform_ae_bound hd ha ha1 h
    r mu R m a b hr hmu hR hm hscale hmargin (Fin.castAdd d i)
  have hh (i k : Fin d) := construction_extendedHessian_uniform_ae_bound hd ha ha1 h
    r mu R m a b hr hmu hR hm hscale hmargin i k
  choose G hG hbG using hg
  choose H hH hbH using hh
  obtain ⟨CT, hCT, hbCT⟩ := construction_extendedTimeJet_uniform_bound ha h r mu R a b
  let C := CT + (∑ i : Fin d, S * G i) + ∑ i : Fin d, ∑ k : Fin d, AC * H i k
  have hC : 0 ≤ C := add_nonneg
    (add_nonneg hCT (Finset.sum_nonneg (fun i _ => mul_nonneg hS (hG i))))
    (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg
      (fun k _ => mul_nonneg hAC (hH i k))))
  refine ⟨C, hC, fun phi P ht hv => ?_⟩
  have htg := construction_spatialMollify_norm_le_ae phi
    (constructionExtendedTimeJet h r mu R P.time)
    (construction_extendedTimeJet_locallyIntegrable h r mu R P.time).aestronglyMeasurable
    CT hCT (Filter.Eventually.of_forall (hbCT P.time ht)) (P.position, P.velocity)
  have hgg (i : Fin d) := construction_spatialMollify_norm_le_ae phi
    (fun q => constructionExtendedNativeGradient h r mu R m P.time q (Fin.castAdd d i))
    (construction_locallyIntegrable_native _
      (construction_extendedGradient_locallyIntegrable h r hr mu R m P.time
        (Fin.castAdd d i))).aestronglyMeasurable
    (G i) (hG i) (hbG i P.time ht) (P.position, P.velocity)
  have hhh (i k : Fin d) := construction_spatialMollify_norm_le_ae phi
    (fun q => constructionExtendedNativeHessian h r mu R m P.time q i k)
    (construction_locallyIntegrable_native _

        (construction_extendedHessian_locallyIntegrable h r hr mu R
          m P.time i k)).aestronglyMeasurable
    (H i k) (hH i k) (hbH i k P.time ht) (P.position, P.velocity)
  rw [construction_smoothed_operator_eq hd ha ha1 h r mu R m hr hmu hR hm hscale
    (fun q hq => (hmargin q hq).le)]
  apply (abs_sub _ _).trans
  apply add_le_add
  · apply (abs_add_le _ _).trans
    apply add_le_add
    · simpa only [Real.norm_eq_abs] using htg
    · unfold PDE.vecDot
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      exact mul_le_mul (hv i) (by simpa only [Real.norm_eq_abs] using hgg i)
        (abs_nonneg _) hS
  · unfold matrixContraction
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i hi
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro k hk
    rw [abs_mul]
    exact mul_le_mul (hAb _ i k) (by simpa only [Real.norm_eq_abs] using hhh i k)
      (abs_nonneg _) hAC

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
