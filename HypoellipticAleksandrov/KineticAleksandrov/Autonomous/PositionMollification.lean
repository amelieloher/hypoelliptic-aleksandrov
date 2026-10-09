module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionMollificationVelocity
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! # The source position regularization theorem

The operator is displayed as its literal scalar slice derivatives, in the source sign convention.
No coefficient derivative, transport error, or analytic bridge premise occurs.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory BarrierRegularization
open scoped Convolution

/-- The position derivative of the convolution equals the convolved actual source jet. -/
theorem barrier_position_convolution_position_jet {alpha : ℝ} {Phi : (ℝ × ℝ) → ℝ}
    (h : IsBellmanHomogeneous alpha Phi) (ha : 0 < alpha) (ha1 : alpha < 1)
    (eta : ℝ → ℝ) (heta : IsNonnegativeUnitSmoothMollifier eta) (X v : ℝ) :
    HasDerivAt (fun w => positionConvolution eta (bellmanOriginExtension Phi) (w, v))
      (positionConvolution eta (bellmanDx Phi) (X, v)) X := by
  have hf : LocallyIntegrable (fun Y => bellmanOriginExtension Phi (Y, v)) volume :=
    ((h.origin_extension_continuous ha).comp
      (continuous_id.prodMk continuous_const)).locallyIntegrable
  have hd := HasCompactSupport.hasDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    hf heta.2.1 (heta.1.of_le (by norm_cast)) X
  have hs : HasCompactSupport (fun Y => eta (X - Y)) :=
    heta.2.1.comp_homeomorph (Homeomorph.subLeft X)
  have ht : ContDiff ℝ 1 (fun Y => eta (X - Y)) :=
    (heta.1.of_le (by norm_cast)).comp (contDiff_const.sub contDiff_id)
  have hw := barrier_position_fiber_weak_dx h ha ha1 v _ ht hs
  simp only [deriv_comp_const_sub, mul_neg, integral_neg] at hw
  have he : positionConvolution (deriv eta) (bellmanOriginExtension Phi) (X, v) =
      positionConvolution eta (bellmanDx Phi) (X, v) := by
    dsimp only [positionConvolution]
    simpa only [neg_inj, mul_comm] using hw
  have hefun : ((fun Y => bellmanOriginExtension Phi (Y, v))
      ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] eta) =
      (fun w => positionConvolution eta (bellmanOriginExtension Phi) (w, v)) :=
    funext fun w => (positionConvolution_eq eta _ (w, v)).symm
  rw [hefun, ← positionConvolution_eq (deriv eta) _ (X, v), he] at hd
  exact hd

/-- The precise separate regularity asserted for the position-regularized barrier. -/
def IsCInfinityPositionC2Velocity (f : (ℝ × ℝ) → ℝ) : Prop :=
  (∀ v : ℝ, ContDiff ℝ (⊤ : ℕ∞) (fun X => f (X, v))) ∧
    ∀ X : ℝ, ContDiff ℝ 2 (fun v => f (X, v))

/-- Regularity and the scalar forward-operator inequality for any actual source barrier.
The conclusion displays `v ∂X + a(X,v) ∂vv` without introducing another PDE interface. -/
theorem barrier_position_regularization_of_positive_degree
    {lam Lam alpha c : ℝ} {Phi : (ℝ × ℝ) → ℝ}
    (ha : 0 < alpha) (ha1 : alpha < 1) (h : IsBellmanHomogeneous alpha Phi)
    (hbound : ∀ q ∈ bellmanPuncturedSet, ∀ b ∈ Icc lam Lam,
      c * bellmanGauge q ^ (alpha - 2) ≤ bellmanOperator b Phi q)
    (eta : ℝ → ℝ) (heta : IsNonnegativeUnitSmoothMollifier eta) :
    IsCInfinityPositionC2Velocity (positionConvolution eta (bellmanOriginExtension Phi)) ∧
      ∀ (A : SmoothAutonomous lam Lam) (Y : ℝ) (q : ℝ × ℝ),
        c * positionConvolution eta (fun w => bellmanGauge w ^ (alpha - 2))
          (q.1 - Y, q.2) ≤
        q.2 * deriv (fun X =>
          positionConvolution eta (bellmanOriginExtension Phi) (X - Y, q.2)) q.1 +
        A.a q.1 q.2 * deriv (deriv (fun v =>
          positionConvolution eta (bellmanOriginExtension Phi) (q.1 - Y, v))) q.2 := by
  refine ⟨⟨barrier_position_convolution_smooth h ha eta heta,
    barrier_position_convolution_velocity_c2 h ha ha1 eta heta⟩, ?_⟩
  intro A Y q
  have hx := barrier_position_convolution_position_jet h ha ha1 eta heta (q.1 - Y) q.2
  have hxshift := hx.comp q.1 ((hasDerivAt_id q.1).sub_const Y)
  have he : deriv (fun v =>
      positionConvolution eta (bellmanOriginExtension Phi) (q.1 - Y, v)) =
      (fun v => positionConvolution eta (bellmanDv Phi) (q.1 - Y, v)) := by
    funext v
    exact (barrier_position_convolution_velocity_jets h ha ha1 eta heta (q.1 - Y) v).1.deriv
  have hvv := (barrier_position_convolution_velocity_jets h ha ha1 eta heta
    (q.1 - Y) q.2).2.deriv
  rw [he, hvv]
  have hxe : deriv (fun X =>
      positionConvolution eta (bellmanOriginExtension Phi) (X - Y, q.2)) q.1 =
      positionConvolution eta (bellmanDx Phi) (q.1 - Y, q.2) := by
    simpa only [Function.comp_def, id_eq, mul_one] using hxshift.deriv
  rw [hxe]
  exact barrier_convolved_jet_inequality h ha ha1 hbound eta heta A Y q

/-- The position-regularization theorem in the source adjoint-exponent range.
The coefficient field and shift are quantified after the fixed source constant and mollifier. -/
theorem barrier_position_regularization (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (alpha : ℝ)
    (ha : bellmanAdjointExponent (Lam / lam)
      (by apply (le_div_iff₀ hlam).2; simpa only [one_mul] using hLam) - 2 < alpha ∧ alpha < 1)
    (Phi : (ℝ × ℝ) → ℝ) (c : ℝ) (hPhi : IsBellmanHomogeneous alpha Phi)
    (hbound : ∀ q ∈ bellmanPuncturedSet, ∀ b ∈ Icc lam Lam,
      c * bellmanGauge q ^ (alpha - 2) ≤ bellmanOperator b Phi q)
    (eta : ℝ → ℝ) (heta : IsNonnegativeUnitSmoothMollifier eta) :
    IsCInfinityPositionC2Velocity (positionConvolution eta (bellmanOriginExtension Phi)) ∧
      ∀ (A : SmoothAutonomous lam Lam) (Y : ℝ) (q : ℝ × ℝ),
        c * positionConvolution eta (fun w => bellmanGauge w ^ (alpha - 2))
          (q.1 - Y, q.2) ≤
        q.2 * deriv (fun X =>
          positionConvolution eta (bellmanOriginExtension Phi) (X - Y, q.2)) q.1 +
        A.a q.1 q.2 * deriv (deriv (fun v =>
          positionConvolution eta (bellmanOriginExtension Phi) (q.1 - Y, v))) q.2 := by
  have hlo := (exists_bellman_barrier lam Lam hlam hLam).1
  have ha0 : 0 < alpha := lt_of_le_of_lt (sub_nonneg.mpr hlo) ha.1
  exact barrier_position_regularization_of_positive_degree ha0 ha.2 hPhi hbound eta heta

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
