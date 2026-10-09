module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.RatioNormalizationMeasure
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureJets
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

/-! # Chain rules and the stationary identity under position rescaling -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- The position derivative acquires exactly the position-rescaling factor. -/
theorem bellmanPositionEquiv_fderiv_position (s : ℝ) (hs : 0 < s)
    (φ : ℝ × ℝ → ℝ) (hφ : Differentiable ℝ φ) (q : ℝ × ℝ) :
    fderiv ℝ (fun z => φ (bellmanPositionEquiv s hs z)) q (1, 0) =
      s * fderiv ℝ φ (bellmanPositionEquiv s hs q) (1, 0) := by
  let T := bellmanPositionEquiv s hs
  have h := ((hφ (T q)).hasFDerivAt.comp q T.hasFDerivAt).fderiv
  change fderiv ℝ (φ ∘ T) q (1, 0) = _
  rw [h, ContinuousLinearMap.comp_apply]
  have he : T (1, 0) = s • (1, 0) := by
    change (s * 1, (0 : ℝ)) = (s * 1, s * 0)
    simp
  change fderiv ℝ φ (T q) (T (1, 0)) = _
  rw [he, map_smul, smul_eq_mul]

/-- Velocity differentiation is unchanged by position rescaling. -/
theorem bellmanPositionEquiv_fderiv_velocity (s : ℝ) (hs : 0 < s)
    (φ : ℝ × ℝ → ℝ) (hφ : Differentiable ℝ φ) (q : ℝ × ℝ) :
    fderiv ℝ (fun z => φ (bellmanPositionEquiv s hs z)) q (0, 1) =
      fderiv ℝ φ (bellmanPositionEquiv s hs q) (0, 1) := by
  let T := bellmanPositionEquiv s hs
  have h := ((hφ (T q)).hasFDerivAt.comp q T.hasFDerivAt).fderiv
  change fderiv ℝ (φ ∘ T) q (0, 1) = _
  rw [h, ContinuousLinearMap.comp_apply]
  change fderiv ℝ φ (T q) (s * 0, 1) = _
  simp only [mul_zero]
  rfl

/-- The second velocity derivative is unchanged by position rescaling. -/
theorem bellmanPositionEquiv_fderiv_velocity_twice (s : ℝ) (hs : 0 < s)
    (φ : ℝ × ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (q : ℝ × ℝ) :
    fderiv ℝ (fun z => fderiv ℝ (fun w => φ (bellmanPositionEquiv s hs w)) z (0, 1))
      q (0, 1) =
    fderiv ℝ (fun z => fderiv ℝ φ z (0, 1)) (bellmanPositionEquiv s hs q) (0, 1) := by
  simp only [bellmanPositionEquiv_fderiv_velocity s hs φ (hφ.differentiable (by simp))]
  exact bellmanPositionEquiv_fderiv_velocity s hs _
    ((bellman_contDiff_direction hφ (0, 1)).differentiable (by simp)) q

/-- The adjoint identity is preserved by the literal normalization of both measures. -/
theorem IsBellmanStationaryAdjointPair.map_position {μ η : Measure BellmanPuncturedPlane}
    (hp : IsBellmanStationaryAdjointPair μ η) (s : ℝ) (hs : 0 < s) :
    IsBellmanStationaryAdjointPair (Measure.map (bellmanPositionHomeomorph s hs) μ)
      (ENNReal.ofReal s⁻¹ • Measure.map (bellmanPositionHomeomorph s hs) η) := by
  intro φ hφ hc haway
  let T := bellmanPositionEquiv s hs
  let H := bellmanPositionHomeomorph s hs
  have hcomp : ContDiff ℝ (⊤ : ℕ∞) (fun q => φ (T q)) :=
    hφ.comp T.contDiff
  have hccomp : HasCompactSupport (fun q => φ (T q)) := hc.comp_homeomorph T.toHomeomorph
  have hscomp : tsupport (fun q => φ (T q)) ⊆ {q | q ≠ (0, 0)} := by
    intro q hq hzero
    have h := tsupport_comp_subset_preimage φ T.continuous hq
    have hn := haway h
    apply hn
    rw [hzero]
    exact T.map_zero
  have h := hp (fun q => φ (T q)) hcomp hccomp hscomp
  dsimp only [T] at h
  simp only [bellmanPositionEquiv_fderiv_position s hs φ (hφ.differentiable (by simp)),
    bellmanPositionEquiv_fderiv_velocity_twice s hs φ hφ] at h
  have hfactor : (∫ q : BellmanPuncturedPlane,
      q.val.2 * (s * fderiv ℝ φ (T q.val) (1, 0)) ∂μ) =
      s * ∫ q : BellmanPuncturedPlane, q.val.2 * fderiv ℝ φ (T q.val) (1, 0) ∂μ := by
    rw [← integral_const_mul]
    congr 1
    funext q
    ring
  rw [hfactor] at h
  rw [H.measurableEmbedding.integral_map,
    integral_smul_measure, H.measurableEmbedding.integral_map,
    ENNReal.toReal_ofReal (inv_nonneg.mpr hs.le)]
  change (∫ q : BellmanPuncturedPlane, q.val.2 * fderiv ℝ φ (T q.val) (1, 0) ∂μ) +
    s⁻¹ * (∫ q : BellmanPuncturedPlane,
      fderiv ℝ (fun z => fderiv ℝ φ z (0, 1)) (T q.val) (0, 1) ∂η) = 0
  have hm := congrArg (fun a : ℝ => s⁻¹ * a) h
  simpa only [mul_add, ← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul, mul_zero] using hm

end HypoellipticAleksandrov.KineticAleksandrov
