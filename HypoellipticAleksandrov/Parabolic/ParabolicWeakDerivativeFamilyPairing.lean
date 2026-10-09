module

public import HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamily
public import HypoellipticAleksandrov.Parabolic.TimeVelocityMultiIndexSplitSuccessor

/-!
# Compact-test pairing for weak derivative families

This file identifies every selected representative in a bounded parabolic weak
derivative family by repeated distributional integration by parts.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped Topology

private theorem coordinateIteratedFDeriv_contDiff
    {d : ℕ} (gamma : TimeVelocityMultiIndex d)
    (f : TimeVelocity d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞)
      (TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma f) := by
  rw [contDiff_infty]
  intro m
  unfold TimeVelocityMultiIndex.coordinateIteratedFDeriv
  have hi := (contDiff_infty.mp hf (m + gamma.order)).iteratedFDeriv_right
    (m := m) (i := gamma.coordinateList.length) (by simp)
  exact (contDiff_const (c := ContinuousMultilinearMap.apply ℝ _ _
    (fun i ↦ timeVelocityBasis (gamma.coordinateList.get i)))).clm_apply hi

private theorem coordinateIteratedFDeriv_tsupport_subset
    {d : ℕ} (gamma : TimeVelocityMultiIndex d) (f : TimeVelocity d → ℝ) :
    tsupport (TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma f) ⊆ tsupport f := by
  apply closure_minimal _ isClosed_closure
  intro z hz
  apply support_iteratedFDeriv_subset (f := f) (𝕜 := ℝ) gamma.coordinateList.length
  intro hzero
  exact hz (by
    unfold TimeVelocityMultiIndex.coordinateIteratedFDeriv
    rw [hzero]
    exact ContinuousMultilinearMap.zero_apply _)

private theorem coordinateIteratedFDeriv_hasCompactSupport
    {d : ℕ} (gamma : TimeVelocityMultiIndex d)
    (f : TimeVelocity d → ℝ) (hf : HasCompactSupport f) :
    HasCompactSupport
      (TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma f) :=
  hf.of_isClosed_subset isClosed_closure
    (coordinateIteratedFDeriv_tsupport_subset gamma f)

private theorem timeDerivative_coordinateIteratedFDeriv
    {d : ℕ} (gamma : TimeVelocityMultiIndex d)
    (f : TimeVelocity d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (z : TimeVelocity d) :
    timeDerivative (TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma f) z =
      TimeVelocityMultiIndex.coordinateIteratedFDeriv
        (gamma + Pi.single (timeCoord d) 1) f z := by
  rw [TimeVelocityMultiIndex.coordinateIteratedFDeriv_add_single]
  · simp [timeDerivative, timeVelocityBasis, timeCoord]
  · exact contDiff_infty.mp hf _

private theorem velocityGradient_coordinateIteratedFDeriv
    {d : ℕ} (gamma : TimeVelocityMultiIndex d)
    (f : TimeVelocity d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (i : Fin d) (z : TimeVelocity d) :
    velocityGradient (TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma f) z i =
      TimeVelocityMultiIndex.coordinateIteratedFDeriv
        (gamma + Pi.single (velocityCoord i) 1) f z := by
  rw [TimeVelocityMultiIndex.coordinateIteratedFDeriv_add_single]
  · rfl
  · exact contDiff_infty.mp hf _

private theorem integral_mul_congr_ae
    {d : ℕ} {U : Set (TimeVelocity d)}
    {f g ψ : TimeVelocity d → ℝ}
    (hfg : f =ᵐ[timeVelocityVolumeOn U] g) :
    (∫ z in U, f z * ψ z ∂(volume : Measure (TimeVelocity d))) =
      ∫ z in U, g z * ψ z ∂(volume : Measure (TimeVelocity d)) := by
  apply integral_congr_ae
  filter_upwards [hfg] with z hz
  rw [hz]

/-- Distributional compact-test characterization of every selected bounded
time--velocity weak derivative. -/
theorem ParabolicWeakDerivativeFamily.integral_representative_mul_test
    {d L : ℕ} {U : Set (TimeVelocity d)}
    {u : TimeVelocity d → ℝ}
    (D : ParabolicWeakDerivativeFamily d L U u)
    (alpha : ParabolicDerivativeIndex d L)
    (φ : TimeVelocity d → ℝ)
    (hφSmooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφCompact : HasCompactSupport φ)
    (hφSupport : tsupport φ ⊆ U) :
    (∫ z in U, D.representative alpha z * φ z
      ∂(volume : Measure (TimeVelocity d))) =
      ((-1 : ℝ) ^ alpha.1.order) *
        ∫ z in U, u z *
          TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 φ z
          ∂(volume : Measure (TimeVelocity d)) := by
  let P := fun beta : ParabolicDerivativeIndex d L =>
    ∀ (gamma : TimeVelocityMultiIndex d) (ψ : TimeVelocity d → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      (∫ z in U, D.representative beta z *
          TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma ψ z
        ∂(volume : Measure (TimeVelocity d))) =
        ((-1 : ℝ) ^ beta.1.order) *
          ∫ z in U, u z *
            TimeVelocityMultiIndex.coordinateIteratedFDeriv (beta.1 + gamma) ψ z
            ∂(volume : Measure (TimeVelocity d))
  have hmain := ParabolicDerivativeIndex.inductionOn alpha (P := P) ?_ ?_ ?_
  simpa using hmain (0 : TimeVelocityMultiIndex d) φ
    hφSmooth hφCompact hφSupport
  · intro gamma ψ _ _ _
    rw [integral_mul_congr_ae D.zero_ae]
    simp [ParabolicDerivativeIndex.coe_zero, TimeVelocityMultiIndex.order,
      TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity,
      VelocityMultiIndex.order]
  · intro beta h ih gamma ψ hψSmooth hψCompact hψSupport
    let θ := TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma ψ
    have hθSmooth := coordinateIteratedFDeriv_contDiff gamma ψ hψSmooth
    have hθCompact := coordinateIteratedFDeriv_hasCompactSupport gamma ψ hψCompact
    have hθSupport :=
      (coordinateIteratedFDeriv_tsupport_subset gamma ψ).trans hψSupport
    have hweak := D.hasWeakTimeSucc beta h θ hθSmooth hθCompact hθSupport
    have hind := ih (gamma + Pi.single (timeCoord d) 1) ψ
      hψSmooth hψCompact hψSupport
    rw [ParabolicDerivativeIndex.coe_timeSucc_eq_add_single]
    rw [show (∫ z in U, D.representative
        (ParabolicDerivativeIndex.timeSucc beta h) z * θ z
        ∂(volume : Measure (TimeVelocity d))) =
        -∫ z in U, D.representative beta z * timeDerivative θ z
          ∂(volume : Measure (TimeVelocity d)) by linarith only [hweak]]
    dsimp only [θ]
    simp_rw [timeDerivative_coordinateIteratedFDeriv gamma ψ hψSmooth]
    rw [hind]
    simp only [TimeVelocityMultiIndex.order_add,
      TimeVelocityMultiIndex.order_single, pow_add, pow_one]
    ring_nf
  · intro beta i h ih gamma ψ hψSmooth hψCompact hψSupport
    let θ := TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma ψ
    have hθSmooth := coordinateIteratedFDeriv_contDiff gamma ψ hψSmooth
    have hθCompact := coordinateIteratedFDeriv_hasCompactSupport gamma ψ hψCompact
    have hθSupport :=
      (coordinateIteratedFDeriv_tsupport_subset gamma ψ).trans hψSupport
    have hweak := D.hasWeakVelocitySucc beta i h θ hθSmooth hθCompact hθSupport
    have hind := ih (gamma + Pi.single (velocityCoord i) 1) ψ
      hψSmooth hψCompact hψSupport
    rw [ParabolicDerivativeIndex.coe_velocitySucc_eq_add_single]
    rw [show (∫ z in U, D.representative
        (ParabolicDerivativeIndex.velocitySucc beta i h) z * θ z
        ∂(volume : Measure (TimeVelocity d))) =
        -∫ z in U, D.representative beta z * velocityGradient θ z i
          ∂(volume : Measure (TimeVelocity d)) by linarith only [hweak]]
    dsimp only [θ]
    simp_rw [velocityGradient_coordinateIteratedFDeriv gamma ψ hψSmooth i]
    rw [hind]
    simp only [TimeVelocityMultiIndex.order_add,
      TimeVelocityMultiIndex.order_single, pow_add, pow_one]
    ring_nf

end HypoellipticAleksandrov.Parabolic
