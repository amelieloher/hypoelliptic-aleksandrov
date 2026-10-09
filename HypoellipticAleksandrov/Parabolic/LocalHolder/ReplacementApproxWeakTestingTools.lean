module

public import HypoellipticAleksandrov.Parabolic.WeakDerivativesUnique
public import HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamily
public import Mathlib.MeasureTheory.Function.L2Space

/-! # Testing bounded-coefficient weak families on open collars

The tools retain the literal restricted-volume convention when using compact tests and
convert a tested equation into an almost-everywhere equation.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Filter MeasureTheory Set

/-- An actual bounded continuous multiplier preserves restricted L2 membership. -/
theorem memLp_two_mul_of_bound {d : ℕ} {U : Set (TimeVelocity d)}
    (hU : MeasurableSet U) (a f : TimeVelocity d → ℝ) (ha : Continuous a)
    (hf : ParabolicMemLpOn U 2 f) (M : ℝ) (hb : ∀ z ∈ U, |a z| ≤ M) :
    ParabolicMemLpOn U 2 (fun z => a z * f z) := by
  apply MemLp.of_le_mul (c := M) hf
    (ha.aestronglyMeasurable.restrict.mul hf.aestronglyMeasurable)
  apply ae_restrict_of_forall_mem hU
  intro z hz
  simp only [Pi.mul_apply]
  rw [norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hb z hz) (norm_nonneg _)

/-- A restricted L2 field pairs integrably with every ambient smooth compact test. -/
theorem integrableOn_weak_pairing {d : ℕ} {U : Set (TimeVelocity d)}
    (f φ : TimeVelocity d → ℝ) (hf : ParabolicMemLpOn U 2 f)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    IntegrableOn (fun z => f z * φ z) U := by
  have ht : MemLp φ 2 (timeVelocityVolumeOn U) :=
    hφ.continuous.memLp_of_hasCompactSupport hc
  have hi := hf.integrable_mul ht
  have he : f * φ = (fun z => f z * φ z) := by
    funext z
    simp only [Pi.mul_apply]
  rw [he] at hi
  simpa only [timeVelocityVolumeOn, IntegrableOn] using hi

/-- Restricted pairings with compact interior tests equal their ambient integrals. -/
theorem setIntegral_weak_pairing_eq_integral {d : ℕ}
    {U : Set (TimeVelocity d)} (f φ : TimeVelocity d → ℝ)
    (hsub : tsupport φ ⊆ U) :
    (∫ z in U, f z * φ z) = ∫ z, f z * φ z := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  have hzout : z ∉ tsupport φ := fun h => hz (hsub h)
  rw [image_eq_zero_of_notMem_tsupport hzout, mul_zero]

/-- Vanishing compact-test pairings give the actual almost-everywhere equation. -/
theorem ae_eq_zero_of_weak_pairings {d : ℕ} {U : Set (TimeVelocity d)}
    (hU : IsOpen U) (f : TimeVelocity d → ℝ) (hf : ParabolicMemLpOn U 2 f)
    (hpair : ∀ φ : TimeVelocity d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ U → (∫ z in U, f z * φ z) = 0) :
    f =ᵐ[timeVelocityVolumeOn U] 0 := by
  have hz : ∀ᵐ z ∂volume, z ∈ U → f z = 0 := by
    apply hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hf.locallyIntegrableOn (by norm_num))
    intro φ hφ hc hs
    rw [show (fun z => φ z • f z) = (fun z => f z * φ z) by
      funext z; simp only [smul_eq_mul]; exact mul_comm _ _]
    rw [← setIntegral_weak_pairing_eq_integral f φ hs]
    exact hpair φ hφ hc hs
  rw [timeVelocityVolumeOn]
  filter_upwards [hz.filter_mono (ae_mono Measure.restrict_le_self),
    ae_restrict_mem hU.measurableSet] with z hz hzU
  exact hz hzU

end HypoellipticAleksandrov.Parabolic.LocalHolder
