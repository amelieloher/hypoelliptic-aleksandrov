module

public import HypoellipticAleksandrov.Parabolic.WeakDerivatives
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Raw algebra for parabolic weak derivatives

This module records coefficient-free algebraic closure properties of the raw
time and velocity weak-derivative predicates.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter MeasureTheory
open scoped ENNReal Topology

private theorem integrable_restrict_mul_of_locallyIntegrableOn
    {d : ℕ} {U : Set (TimeVelocity d)} {f g : TimeVelocity d → ℝ}
    (hf : LocallyIntegrableOn f U volume) (hg : Continuous g)
    (hgCompact : HasCompactSupport g) (hgSub : tsupport g ⊆ U) :
    Integrable (fun z => f z * g z) (timeVelocityVolumeOn U) := by
  have hfK : IntegrableOn f (tsupport g) volume :=
    hf.integrableOn_compact_subset hgSub hgCompact.isCompact
  have hfgK : IntegrableOn (fun z => f z * g z) (tsupport g) volume := by
    simpa only [smul_eq_mul] using
      hfK.smul_continuousOn hg.continuousOn hgCompact.isCompact
  have hsupport : Function.support (fun z => f z * g z) ⊆ tsupport g := by
    intro z hz
    exact tsupport_mul_subset_right (subset_closure hz)
  exact (integrableOn_iff_integrable_of_support_subset hsupport).mp hfgK |>.restrict

private theorem timeDerivative_continuous {d : ℕ} {f : TimeVelocity d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : Continuous (timeDerivative f) := by
  unfold timeDerivative
  simpa using (hf.continuous_fderiv (by simp)).clm_apply continuous_const

private theorem timeDerivative_compact {d : ℕ} {f : TimeVelocity d → ℝ}
    (hf : HasCompactSupport f) : HasCompactSupport (timeDerivative f) := by
  unfold timeDerivative
  simpa using hf.fderiv_apply (𝕜 := ℝ) ((1, 0) : TimeVelocity d)

private theorem timeDerivative_tsupport {d : ℕ} (f : TimeVelocity d → ℝ) :
    tsupport (timeDerivative f) ⊆ tsupport f := by
  unfold timeDerivative
  change closure (Function.support (fun z => fderiv ℝ f z (1, 0))) ⊆ tsupport f
  refine (closure_mono ?_).trans (tsupport_fderiv_subset ℝ)
  intro z hz
  rw [Function.mem_support] at hz ⊢
  intro hzero
  apply hz
  simp [hzero]

private theorem velocityGradient_continuous {d : ℕ} {f : TimeVelocity d → ℝ} {i : Fin d}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : Continuous (fun z => velocityGradient f z i) := by
  unfold velocityGradient
  simpa using (hf.continuous_fderiv (by simp)).clm_apply continuous_const

private theorem velocityGradient_compact {d : ℕ} {f : TimeVelocity d → ℝ} {i : Fin d}
    (hf : HasCompactSupport f) : HasCompactSupport (fun z => velocityGradient f z i) := by
  unfold velocityGradient
  simpa using hf.fderiv_apply (𝕜 := ℝ) ((0, Pi.single i 1) : TimeVelocity d)

private theorem velocityGradient_tsupport {d : ℕ} {i : Fin d} (f : TimeVelocity d → ℝ) :
    tsupport (fun z => velocityGradient f z i) ⊆ tsupport f := by
  unfold velocityGradient
  change closure (Function.support (fun z => fderiv ℝ f z (0, Pi.single i 1))) ⊆ tsupport f
  refine (closure_mono ?_).trans (tsupport_fderiv_subset ℝ)
  intro z hz
  rw [Function.mem_support] at hz ⊢
  intro hzero
  apply hz
  simp [hzero]

namespace HasWeakTimeDerivOn

/-- Zero has zero weak time derivative. -/
theorem zero {d : ℕ} {U : Set (TimeVelocity d)} :
    HasWeakTimeDerivOn U (0 : TimeVelocity d → ℝ) 0 := by
  intro φ hφ hφCompact hφSub
  simp only [Pi.zero_apply, zero_mul, integral_zero, neg_zero]

/-- Weak time differentiation commutes with constant scalar multiplication. -/
theorem smul {d : ℕ} {U : Set (TimeVelocity d)}
    {u du : TimeVelocity d → ℝ}
    (hu : HasWeakTimeDerivOn U u du) (c : ℝ) :
    HasWeakTimeDerivOn U (c • u) (c • du) := by
  intro φ hφ hφCompact hφSub
  calc
    (∫ z in U, (c • u) z * timeDerivative φ z ∂volume) =
        c * ∫ z in U, u z * timeDerivative φ z ∂volume := by
      rw [show (fun z => (c • u) z * timeDerivative φ z) =
          fun z => c * (u z * timeDerivative φ z) by
        funext z
        simp only [Pi.smul_apply, smul_eq_mul]
        ring,
        integral_const_mul]
    _ = c * (-(∫ z in U, du z * φ z ∂volume)) := by
      rw [hu φ hφ hφCompact hφSub]
    _ = -∫ z in U, (c • du) z * φ z ∂volume := by
      rw [show (fun z => (c • du) z * φ z) = fun z => c * (du z * φ z) by
        funext z
        simp only [Pi.smul_apply, smul_eq_mul]
        ring,
        integral_const_mul]
      ring

/-- Weak time differentiation commutes with negation. -/
theorem neg {d : ℕ} {U : Set (TimeVelocity d)}
    {u du : TimeVelocity d → ℝ}
    (hu : HasWeakTimeDerivOn U u du) :
    HasWeakTimeDerivOn U (-u) (-du) := by
  intro φ hφ hφCompact hφSub
  calc
    (∫ z in U, (-u) z * timeDerivative φ z ∂volume) =
        -(∫ z in U, u z * timeDerivative φ z ∂volume) := by
      rw [show (fun z => (-u) z * timeDerivative φ z) =
          fun z => -(u z * timeDerivative φ z) by
        funext z
        simp only [Pi.neg_apply, neg_mul],
        integral_neg]
    _ = -(-(∫ z in U, du z * φ z ∂volume)) := by
      rw [hu φ hφ hφCompact hφSub]
    _ = -∫ z in U, (-du) z * φ z ∂volume := by
      rw [show (fun z => (-du) z * φ z) = fun z => -(du z * φ z) by
        funext z
        simp only [Pi.neg_apply, neg_mul],
        integral_neg]

/-- Raw weak time derivatives are additive when all representatives are
locally integrable. -/
theorem add {d : ℕ} {U : Set (TimeVelocity d)}
    {u du v dv : TimeVelocity d → ℝ}
    (hu : HasWeakTimeDerivOn U u du)
    (hv : HasWeakTimeDerivOn U v dv)
    (huLoc : LocallyIntegrableOn u U volume)
    (hduLoc : LocallyIntegrableOn du U volume)
    (hvLoc : LocallyIntegrableOn v U volume)
    (hdvLoc : LocallyIntegrableOn dv U volume) :
    HasWeakTimeDerivOn U (fun z => u z + v z) (fun z => du z + dv z) := by
  intro φ hφ hφCompact hφSub
  let μU : Measure (TimeVelocity d) := timeVelocityVolumeOn U
  let dφ : TimeVelocity d → ℝ := timeDerivative φ
  have hφCont : Continuous φ := hφ.continuous
  have hdφCont : Continuous dφ := timeDerivative_continuous hφ
  have hdφCompact : HasCompactSupport dφ := timeDerivative_compact hφCompact
  have hdφSub : tsupport dφ ⊆ U := timeDerivative_tsupport φ |>.trans hφSub
  have huPair : Integrable (fun z => u z * dφ z) μU := by
    simpa only [μU] using
      integrable_restrict_mul_of_locallyIntegrableOn huLoc hdφCont hdφCompact hdφSub
  have hvPair : Integrable (fun z => v z * dφ z) μU := by
    simpa only [μU] using
      integrable_restrict_mul_of_locallyIntegrableOn hvLoc hdφCont hdφCompact hdφSub
  have hduPair : Integrable (fun z => du z * φ z) μU := by
    simpa only [μU] using
      integrable_restrict_mul_of_locallyIntegrableOn hduLoc hφCont hφCompact hφSub
  have hdvPair : Integrable (fun z => dv z * φ z) μU := by
    simpa only [μU] using
      integrable_restrict_mul_of_locallyIntegrableOn hdvLoc hφCont hφCompact hφSub
  change (∫ z, (u z + v z) * dφ z ∂μU) =
    -∫ z, (du z + dv z) * φ z ∂μU
  calc
    (∫ z, (u z + v z) * dφ z ∂μU) =
        (∫ z, u z * dφ z ∂μU) + ∫ z, v z * dφ z ∂μU := by
      rw [← integral_add huPair hvPair]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by ring
    _ = -∫ z, du z * φ z ∂μU + -∫ z, dv z * φ z ∂μU := by
      rw [show (∫ z, u z * dφ z ∂μU) = -∫ z, du z * φ z ∂μU by
        simpa only [μU, dφ] using hu φ hφ hφCompact hφSub,
        show (∫ z, v z * dφ z ∂μU) = -∫ z, dv z * φ z ∂μU by
        simpa only [μU, dφ] using hv φ hφ hφCompact hφSub]
    _ = -(∫ z, du z * φ z ∂μU + ∫ z, dv z * φ z ∂μU) := by ring
    _ = -∫ z, (du z + dv z) * φ z ∂μU := by
      rw [← integral_add hduPair hdvPair]
      apply congrArg Neg.neg
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by ring

/-- Raw weak time derivatives commute with subtraction when all
representatives are locally integrable. -/
theorem sub {d : ℕ} {U : Set (TimeVelocity d)}
    {u du v dv : TimeVelocity d → ℝ}
    (hu : HasWeakTimeDerivOn U u du)
    (hv : HasWeakTimeDerivOn U v dv)
    (huLoc : LocallyIntegrableOn u U volume)
    (hduLoc : LocallyIntegrableOn du U volume)
    (hvLoc : LocallyIntegrableOn v U volume)
    (hdvLoc : LocallyIntegrableOn dv U volume) :
    HasWeakTimeDerivOn U (fun z => u z - v z) (fun z => du z - dv z) := by
  intro φ hφ hφCompact hφSub
  let μU : Measure (TimeVelocity d) := timeVelocityVolumeOn U
  let dφ : TimeVelocity d → ℝ := timeDerivative φ
  have hφCont : Continuous φ := hφ.continuous
  have hdφCont : Continuous dφ := timeDerivative_continuous hφ
  have hdφCompact : HasCompactSupport dφ := timeDerivative_compact hφCompact
  have hdφSub : tsupport dφ ⊆ U := timeDerivative_tsupport φ |>.trans hφSub
  have huPair : Integrable (fun z => u z * dφ z) μU := by
    simpa only [μU] using
      integrable_restrict_mul_of_locallyIntegrableOn huLoc hdφCont hdφCompact hdφSub
  have hvPair : Integrable (fun z => v z * dφ z) μU := by
    simpa only [μU] using
      integrable_restrict_mul_of_locallyIntegrableOn hvLoc hdφCont hdφCompact hdφSub
  have hduPair : Integrable (fun z => du z * φ z) μU := by
    simpa only [μU] using
      integrable_restrict_mul_of_locallyIntegrableOn hduLoc hφCont hφCompact hφSub
  have hdvPair : Integrable (fun z => dv z * φ z) μU := by
    simpa only [μU] using
      integrable_restrict_mul_of_locallyIntegrableOn hdvLoc hφCont hφCompact hφSub
  change (∫ z, (u z - v z) * dφ z ∂μU) =
    -∫ z, (du z - dv z) * φ z ∂μU
  calc
    (∫ z, (u z - v z) * dφ z ∂μU) =
        (∫ z, u z * dφ z ∂μU) - ∫ z, v z * dφ z ∂μU := by
      rw [← integral_sub huPair hvPair]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by ring
    _ = -∫ z, du z * φ z ∂μU - -∫ z, dv z * φ z ∂μU := by
      rw [show (∫ z, u z * dφ z ∂μU) = -∫ z, du z * φ z ∂μU by
        simpa only [μU, dφ] using hu φ hφ hφCompact hφSub,
        show (∫ z, v z * dφ z ∂μU) = -∫ z, dv z * φ z ∂μU by
        simpa only [μU, dφ] using hv φ hφ hφCompact hφSub]
    _ = -(∫ z, du z * φ z ∂μU - ∫ z, dv z * φ z ∂μU) := by ring
    _ = -∫ z, (du z - dv z) * φ z ∂μU := by
      rw [← integral_sub hduPair hdvPair]
      apply congrArg Neg.neg
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by ring

/-- Weak time differentiation commutes with finite sums when every value and
derivative representative is locally integrable. -/
theorem fin_sum
    {d n : ℕ} {U : Set (TimeVelocity d)}
    {u du : Fin n → TimeVelocity d → ℝ}
    (hu : ∀ j, HasWeakTimeDerivOn U (u j) (du j))
    (huLoc : ∀ j, LocallyIntegrableOn (u j) U volume)
    (hduLoc : ∀ j, LocallyIntegrableOn (du j) U volume) :
    HasWeakTimeDerivOn U
      (fun z => ∑ j, u j z) (fun z => ∑ j, du j z) := by
  classical
  have huSumLoc : ∀ s : Finset (Fin n),
      LocallyIntegrableOn (fun z => ∑ j ∈ s, u j z) U volume := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using
        (locallyIntegrableOn_zero (X := TimeVelocity d) (s := U)
          (μ := volume) (ε'' := ℝ))
    | @insert j s hj ih =>
        simpa [Finset.sum_insert hj, Pi.add_def] using (huLoc j).add ih
  have hduSumLoc : ∀ s : Finset (Fin n),
      LocallyIntegrableOn (fun z => ∑ j ∈ s, du j z) U volume := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using
        (locallyIntegrableOn_zero (X := TimeVelocity d) (s := U)
          (μ := volume) (ε'' := ℝ))
    | @insert j s hj ih =>
        simpa [Finset.sum_insert hj, Pi.add_def] using (hduLoc j).add ih
  have hweak : ∀ s : Finset (Fin n),
      HasWeakTimeDerivOn U
        (fun z => ∑ j ∈ s, u j z) (fun z => ∑ j ∈ s, du j z) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty, HasWeakTimeDerivOn, Pi.zero_apply] using
        (HasWeakTimeDerivOn.zero (d := d) (U := U))
    | @insert j s hj ih =>
        have hadd := HasWeakTimeDerivOn.add (hu j) ih
          (huLoc j) (hduLoc j) (huSumLoc s) (hduSumLoc s)
        simpa [Finset.sum_insert hj] using hadd
  simpa using hweak Finset.univ

end HasWeakTimeDerivOn

namespace HasWeakVelocityPartialDerivOn

/-- Zero has zero weak velocity derivative. -/
theorem zero {d : ℕ} {U : Set (TimeVelocity d)} {i : Fin d} :
    HasWeakVelocityPartialDerivOn U i (0 : TimeVelocity d → ℝ) 0 := by
  intro φ hφ hφCompact hφSub
  simp only [Pi.zero_apply, zero_mul, integral_zero, neg_zero]

/-- Weak velocity differentiation commutes with constant scalar multiplication. -/
theorem smul {d : ℕ} {U : Set (TimeVelocity d)} {i : Fin d}
    {u dui : TimeVelocity d → ℝ}
    (hu : HasWeakVelocityPartialDerivOn U i u dui) (c : ℝ) :
    HasWeakVelocityPartialDerivOn U i (c • u) (c • dui) := by
  intro φ hφ hφCompact hφSub
  calc
    (∫ z in U, (c • u) z * velocityGradient φ z i ∂volume) =
        c * ∫ z in U, u z * velocityGradient φ z i ∂volume := by
      rw [show (fun z => (c • u) z * velocityGradient φ z i) =
          fun z => c * (u z * velocityGradient φ z i) by
        funext z
        simp only [Pi.smul_apply, smul_eq_mul]
        ring,
        integral_const_mul]
    _ = c * (-(∫ z in U, dui z * φ z ∂volume)) := by
      rw [hu φ hφ hφCompact hφSub]
    _ = -∫ z in U, (c • dui) z * φ z ∂volume := by
      rw [show (fun z => (c • dui) z * φ z) = fun z => c * (dui z * φ z) by
        funext z
        simp only [Pi.smul_apply, smul_eq_mul]
        ring,
        integral_const_mul]
      ring

/-- Weak velocity differentiation commutes with negation. -/
theorem neg {d : ℕ} {U : Set (TimeVelocity d)} {i : Fin d}
    {u dui : TimeVelocity d → ℝ}
    (hu : HasWeakVelocityPartialDerivOn U i u dui) :
    HasWeakVelocityPartialDerivOn U i (-u) (-dui) := by
  intro φ hφ hφCompact hφSub
  calc
    (∫ z in U, (-u) z * velocityGradient φ z i ∂volume) =
        -(∫ z in U, u z * velocityGradient φ z i ∂volume) := by
      rw [show (fun z => (-u) z * velocityGradient φ z i) =
          fun z => -(u z * velocityGradient φ z i) by
        funext z
        simp only [Pi.neg_apply, neg_mul],
        integral_neg]
    _ = -(-(∫ z in U, dui z * φ z ∂volume)) := by
      rw [hu φ hφ hφCompact hφSub]
    _ = -∫ z in U, (-dui) z * φ z ∂volume := by
      rw [show (fun z => (-dui) z * φ z) = fun z => -(dui z * φ z) by
        funext z
        simp only [Pi.neg_apply, neg_mul],
        integral_neg]

/-- Raw weak velocity derivatives are additive when all representatives are
locally integrable. -/
theorem add {d : ℕ} {U : Set (TimeVelocity d)} {i : Fin d}
    {u du v dv : TimeVelocity d → ℝ}
    (hu : HasWeakVelocityPartialDerivOn U i u du)
    (hv : HasWeakVelocityPartialDerivOn U i v dv)
    (huLoc : LocallyIntegrableOn u U volume)
    (hduLoc : LocallyIntegrableOn du U volume)
    (hvLoc : LocallyIntegrableOn v U volume)
    (hdvLoc : LocallyIntegrableOn dv U volume) :
    HasWeakVelocityPartialDerivOn U i (fun z => u z + v z) (fun z => du z + dv z) := by
  intro φ hφ hφCompact hφSub
  let μU : Measure (TimeVelocity d) := timeVelocityVolumeOn U
  let dφ : TimeVelocity d → ℝ := fun z => velocityGradient φ z i
  have hφCont : Continuous φ := hφ.continuous
  have hdφCont : Continuous dφ := velocityGradient_continuous hφ
  have hdφCompact : HasCompactSupport dφ := velocityGradient_compact hφCompact
  have hdφSub : tsupport dφ ⊆ U := velocityGradient_tsupport φ |>.trans hφSub
  have huPair : Integrable (fun z => u z * dφ z) μU := by
    simpa only [μU] using
      integrable_restrict_mul_of_locallyIntegrableOn huLoc hdφCont hdφCompact hdφSub
  have hvPair : Integrable (fun z => v z * dφ z) μU := by
    simpa only [μU] using
      integrable_restrict_mul_of_locallyIntegrableOn hvLoc hdφCont hdφCompact hdφSub
  have hduPair : Integrable (fun z => du z * φ z) μU := by
    simpa only [μU] using
      integrable_restrict_mul_of_locallyIntegrableOn hduLoc hφCont hφCompact hφSub
  have hdvPair : Integrable (fun z => dv z * φ z) μU := by
    simpa only [μU] using
      integrable_restrict_mul_of_locallyIntegrableOn hdvLoc hφCont hφCompact hφSub
  change (∫ z, (u z + v z) * dφ z ∂μU) =
    -∫ z, (du z + dv z) * φ z ∂μU
  calc
    (∫ z, (u z + v z) * dφ z ∂μU) =
        (∫ z, u z * dφ z ∂μU) + ∫ z, v z * dφ z ∂μU := by
      rw [← integral_add huPair hvPair]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by ring
    _ = -∫ z, du z * φ z ∂μU + -∫ z, dv z * φ z ∂μU := by
      rw [show (∫ z, u z * dφ z ∂μU) = -∫ z, du z * φ z ∂μU by
        simpa only [μU, dφ] using hu φ hφ hφCompact hφSub,
        show (∫ z, v z * dφ z ∂μU) = -∫ z, dv z * φ z ∂μU by
        simpa only [μU, dφ] using hv φ hφ hφCompact hφSub]
    _ = -(∫ z, du z * φ z ∂μU + ∫ z, dv z * φ z ∂μU) := by ring
    _ = -∫ z, (du z + dv z) * φ z ∂μU := by
      rw [← integral_add hduPair hdvPair]
      apply congrArg Neg.neg
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by ring

/-- Raw weak velocity derivatives commute with subtraction when all
representatives are locally integrable. -/
theorem sub {d : ℕ} {U : Set (TimeVelocity d)} {i : Fin d}
    {u du v dv : TimeVelocity d → ℝ}
    (hu : HasWeakVelocityPartialDerivOn U i u du)
    (hv : HasWeakVelocityPartialDerivOn U i v dv)
    (huLoc : LocallyIntegrableOn u U volume)
    (hduLoc : LocallyIntegrableOn du U volume)
    (hvLoc : LocallyIntegrableOn v U volume)
    (hdvLoc : LocallyIntegrableOn dv U volume) :
    HasWeakVelocityPartialDerivOn U i
      (fun z => u z - v z) (fun z => du z - dv z) := by
  intro φ hφ hφCompact hφSub
  let μU : Measure (TimeVelocity d) := timeVelocityVolumeOn U
  let dφ : TimeVelocity d → ℝ := fun z => velocityGradient φ z i
  have hφCont : Continuous φ := hφ.continuous
  have hdφCont : Continuous dφ := velocityGradient_continuous hφ
  have hdφCompact : HasCompactSupport dφ := velocityGradient_compact hφCompact
  have hdφSub : tsupport dφ ⊆ U := velocityGradient_tsupport φ |>.trans hφSub
  have huPair : Integrable (fun z => u z * dφ z) μU := by
    simpa only [μU] using
      integrable_restrict_mul_of_locallyIntegrableOn huLoc hdφCont hdφCompact hdφSub
  have hvPair : Integrable (fun z => v z * dφ z) μU := by
    simpa only [μU] using
      integrable_restrict_mul_of_locallyIntegrableOn hvLoc hdφCont hdφCompact hdφSub
  have hduPair : Integrable (fun z => du z * φ z) μU := by
    simpa only [μU] using
      integrable_restrict_mul_of_locallyIntegrableOn hduLoc hφCont hφCompact hφSub
  have hdvPair : Integrable (fun z => dv z * φ z) μU := by
    simpa only [μU] using
      integrable_restrict_mul_of_locallyIntegrableOn hdvLoc hφCont hφCompact hφSub
  change (∫ z, (u z - v z) * dφ z ∂μU) =
    -∫ z, (du z - dv z) * φ z ∂μU
  calc
    (∫ z, (u z - v z) * dφ z ∂μU) =
        (∫ z, u z * dφ z ∂μU) - ∫ z, v z * dφ z ∂μU := by
      rw [← integral_sub huPair hvPair]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by ring
    _ = -∫ z, du z * φ z ∂μU - -∫ z, dv z * φ z ∂μU := by
      rw [show (∫ z, u z * dφ z ∂μU) = -∫ z, du z * φ z ∂μU by
        simpa only [μU, dφ] using hu φ hφ hφCompact hφSub,
        show (∫ z, v z * dφ z ∂μU) = -∫ z, dv z * φ z ∂μU by
        simpa only [μU, dφ] using hv φ hφ hφCompact hφSub]
    _ = -(∫ z, du z * φ z ∂μU - ∫ z, dv z * φ z ∂μU) := by ring
    _ = -∫ z, (du z - dv z) * φ z ∂μU := by
      rw [← integral_sub hduPair hdvPair]
      apply congrArg Neg.neg
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by ring

/-- Weak velocity differentiation commutes with finite sums when every value
and derivative representative is locally integrable. -/
theorem fin_sum
    {d n : ℕ} {U : Set (TimeVelocity d)} {i : Fin d}
    {u du : Fin n → TimeVelocity d → ℝ}
    (hu : ∀ j, HasWeakVelocityPartialDerivOn U i (u j) (du j))
    (huLoc : ∀ j, LocallyIntegrableOn (u j) U volume)
    (hduLoc : ∀ j, LocallyIntegrableOn (du j) U volume) :
    HasWeakVelocityPartialDerivOn U i
      (fun z => ∑ j, u j z) (fun z => ∑ j, du j z) := by
  classical
  have huSumLoc : ∀ s : Finset (Fin n),
      LocallyIntegrableOn (fun z => ∑ j ∈ s, u j z) U volume := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using
        (locallyIntegrableOn_zero (X := TimeVelocity d) (s := U) (μ := volume) (ε'' := ℝ))
    | @insert j s hj ih =>
        simpa [Finset.sum_insert hj, Pi.add_def] using (huLoc j).add ih
  have hduSumLoc : ∀ s : Finset (Fin n),
      LocallyIntegrableOn (fun z => ∑ j ∈ s, du j z) U volume := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using
        (locallyIntegrableOn_zero (X := TimeVelocity d) (s := U) (μ := volume) (ε'' := ℝ))
    | @insert j s hj ih =>
        simpa [Finset.sum_insert hj, Pi.add_def] using (hduLoc j).add ih
  have hweak : ∀ s : Finset (Fin n),
      HasWeakVelocityPartialDerivOn U i
        (fun z => ∑ j ∈ s, u j z) (fun z => ∑ j ∈ s, du j z) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty,
          HasWeakVelocityPartialDerivOn, Pi.zero_apply] using
        (HasWeakVelocityPartialDerivOn.zero (d := d) (U := U) (i := i))
    | @insert j s hj ih =>
        have hadd := HasWeakVelocityPartialDerivOn.add (hu j) ih
          (huLoc j) (hduLoc j) (huSumLoc s) (hduSumLoc s)
        simpa [Finset.sum_insert hj] using hadd
  simpa using hweak Finset.univ

end HasWeakVelocityPartialDerivOn

end HypoellipticAleksandrov.Parabolic
