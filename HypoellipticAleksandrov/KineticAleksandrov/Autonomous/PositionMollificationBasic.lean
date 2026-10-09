module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BarrierModulus
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionMollificationLineWeak
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.Setting
public import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-! # Position convolution and the Bellman inequality with coefficients held fixed -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory BarrierRegularization
open scoped Convolution

/-- Position-only convolution, leaving the velocity coordinate fixed. -/
def positionConvolution (eta : ℝ → ℝ) (Phi : (ℝ × ℝ) → ℝ) (q : ℝ × ℝ) : ℝ :=
  ∫ X, eta (q.1 - X) * Phi (X, q.2)

/-- A compact smooth approximate-identity kernel at any fixed positive scale. -/
def IsNonnegativeUnitSmoothMollifier (eta : ℝ → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) eta ∧ HasCompactSupport eta ∧
    (∀ X, 0 ≤ eta X) ∧ (∫ X, eta X) = 1

/-- The convolution is the ordinary scalar convolution of each position fiber. -/
theorem positionConvolution_eq (eta : ℝ → ℝ) (Phi : (ℝ × ℝ) → ℝ) (q : ℝ × ℝ) :
    positionConvolution eta Phi q =
      ((fun X => Phi (X, q.2)) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] eta) q.1 := by
  unfold positionConvolution convolution
  congr 1
  funext X
  exact mul_comm _ _

/-- Smoothing in position gives C∞ position fibers even on the zero-velocity line. -/
theorem barrier_position_convolution_smooth {alpha : ℝ} {Phi : (ℝ × ℝ) → ℝ}
    (h : IsBellmanHomogeneous alpha Phi) (ha : 0 < alpha)
    (eta : ℝ → ℝ) (heta : IsNonnegativeUnitSmoothMollifier eta) (v : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun X => positionConvolution eta (bellmanOriginExtension Phi) (X, v)) := by
  have hf : LocallyIntegrable (fun X => bellmanOriginExtension Phi (X, v)) volume :=
    ((h.origin_extension_continuous ha).comp
    (continuous_id.prodMk continuous_const)).locallyIntegrable
  simpa only [positionConvolution_eq] using
    heta.2.1.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hf heta.1

/-- Any locally integrable fiber can be tested against a translated compact smooth kernel. -/
theorem position_kernel_integrable (eta f : ℝ → ℝ) (heta : Continuous eta)
    (hc : HasCompactSupport eta) (hf : LocallyIntegrable f volume) (X : ℝ) :
    Integrable (fun Y => eta (X - Y) * f Y) volume := by
  have hh := hc.convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ) hf heta X
  simpa only [ConvolutionExistsAt, ContinuousLinearMap.mul_apply', mul_comm] using hh

/-- All source velocity fibers are locally integrable, including at velocity zero. -/
theorem barrier_velocity_fibers_locallyIntegrable {alpha : ℝ} {Phi : (ℝ × ℝ) → ℝ}
    (h : IsBellmanHomogeneous alpha Phi) (ha : 0 < alpha) (ha1 : alpha < 1) (v : ℝ) :
    LocallyIntegrable (fun X => bellmanDv Phi (X, v)) volume ∧
      LocallyIntegrable (fun X => bellmanDvv Phi (X, v)) volume := by
  have hi (f : ℝ → ℝ) (hf : ∀ a b, IntegrableOn f (Icc a b) volume) :
      LocallyIntegrable f volume := by
    rw [locallyIntegrable_iff]
    intro K hK
    obtain ⟨R, _, hR⟩ := hK.isBounded.exists_pos_norm_lt
    apply (hf (-R) R).mono_set
    intro x hx
    exact abs_le.mp (by simpa only [Real.norm_eq_abs] using (hR x hx).le)
  exact ⟨hi _ (fun a b => (barrier_jet_fiber_integrable h ha ha1 v a b).2.1),
    hi _ (fun a b => (barrier_jet_fiber_integrable h ha ha1 v a b).2.2)⟩

/-- The convolved source weight is a genuine integrable position fiber. -/
theorem barrier_weight_fiber_locallyIntegrable (alpha : ℝ) (ha : 0 < alpha)
    (ha1 : alpha < 1) (v : ℝ) :
    LocallyIntegrable (fun X => bellmanGauge (X, v) ^ (alpha - 2)) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  have hm : Measurable (fun X => bellmanGauge (X, v) ^ (alpha - 2)) :=
    ((bellmanGauge_continuous.comp (continuous_id.prodMk continuous_const)).measurable).pow_const _
  have hb := ((bellman_abs_rpow_locallyIntegrable ((alpha - 2) / 3)
    (by linarith)).integrableOn_isCompact hK)
  apply hb.mono' hm.aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with X hX
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (bellmanGauge_nonneg _) _)]
  have hh := barrier_position_fiber_bound (alpha - 2) (by linarith)
    (fun q => bellmanGauge q ^ (alpha - 2)) 1 zero_le_one
    (fun q _ => by rw [abs_of_nonneg (Real.rpow_nonneg (bellmanGauge_nonneg _) _), one_mul])
    X v hX
  simpa only [one_mul, abs_of_nonneg (Real.rpow_nonneg (bellmanGauge_nonneg _) _)] using hh

/-- The coefficient is held at the evaluation point while integrating the source inequality.
This is an inequality for the convolved actual source jets, without any derivative of `a`. -/
theorem barrier_convolved_jet_inequality {lam Lam alpha c : ℝ}
    {Phi : (ℝ × ℝ) → ℝ} (h : IsBellmanHomogeneous alpha Phi)
    (ha : 0 < alpha) (ha1 : alpha < 1)
    (hbound : ∀ q ∈ bellmanPuncturedSet, ∀ b ∈ Icc lam Lam,
      c * bellmanGauge q ^ (alpha - 2) ≤ bellmanOperator b Phi q)
    (eta : ℝ → ℝ) (heta : IsNonnegativeUnitSmoothMollifier eta)
    (A : SmoothAutonomous lam Lam) (Y : ℝ) (q : ℝ × ℝ) :
    c * positionConvolution eta (fun w => bellmanGauge w ^ (alpha - 2))
      (q.1 - Y, q.2) ≤
      q.2 * positionConvolution eta (bellmanDx Phi) (q.1 - Y, q.2) +
        A.a q.1 q.2 * positionConvolution eta (bellmanDvv Phi) (q.1 - Y, q.2) := by
  have hiX := position_kernel_integrable eta _ heta.1.continuous heta.2.1
    (barrier_dx_fiber_locallyIntegrable h ha ha1 q.2) (q.1 - Y)
  have hivv := position_kernel_integrable eta _ heta.1.continuous heta.2.1
    (barrier_velocity_fibers_locallyIntegrable h ha ha1 q.2).2 (q.1 - Y)
  have hiw := position_kernel_integrable eta _ heta.1.continuous heta.2.1
    (barrier_weight_fiber_locallyIntegrable alpha ha ha1 q.2) (q.1 - Y)
  have hh := integral_mono_ae (hiw.const_mul c)
    ((hiX.const_mul q.2).add (hivv.const_mul (A.a q.1 q.2))) ?_
  · simpa only [positionConvolution, Pi.add_apply, integral_add (hiX.const_mul q.2)
      (hivv.const_mul (A.a q.1 q.2)), integral_const_mul] using hh
  · filter_upwards [volume.ae_ne (0 : ℝ)] with X hX
    have hq : (X, q.2) ∈ bellmanPuncturedSet := fun he => hX (congrArg Prod.fst he)
    have hb := hbound (X, q.2) hq (A.a q.1 q.2) (A.bounds q.1 q.2)
    have hi := mul_le_mul_of_nonneg_left hb (heta.2.2.1 (q.1 - Y - X))
    dsimp only [bellmanOperator] at hi
    simpa only [Pi.add_apply, mul_add, mul_left_comm, mul_assoc] using hi

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
