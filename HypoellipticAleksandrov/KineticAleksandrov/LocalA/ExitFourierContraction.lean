module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ExitFourierComposition
import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic

/-! # Total variation contraction through the actual later boundary operator -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory SectionTwo Parabolic
open scoped ENNReal

variable (hH : HormanderHypoellipticityStatement)
  (hLE : LiebermanEllipsoidDirichletStatement)
  {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ}
  (hlam : 0 < lam) (hLam : lam ≤ Lam)
  (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
  (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)

/-- Composing with actual later exits contracts the killed Fourier total variation. -/
theorem ballExitRestart_fourier_variation_le
    (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t})
    (H : {t : ℝ // P.1.time < t ∧ t < T.1}) (ξ : PDE.Vec d) :
    (exitFourier ((ballExitRestart hH hLE hd hlam hLam B hB v₀ hR P T H).map
      (exitCoordinates P.1 v₀)) ξ).variation univ ≤
      (fourierProjection (localBallKernel hH hLE hd hlam hLam B hB v₀ hR)
        (ballEvolutionQuery P ⟨H.1, H.2.1⟩) ξ).variation univ := by
  let ν := fourierProjection (localBallKernel hH hLE hd hlam hLam B hB v₀ hR)
    (ballEvolutionQuery P ⟨H.1, H.2.1⟩) ξ
  let η := exitFourier ((ballExitRestart hH hLE hd hlam hLam B hB v₀ hR P T H).map
    (exitCoordinates P.1 v₀)) ξ
  let f (E : Set (TimeVelocity d)) :=
    ballLaterExitFourierTest hH hLE hd hlam hLam B hB v₀ hR H.1 T.1 H.2.2 ξ E
  have hmulNorm : ‖ContinuousLinearMap.mul ℝ ℂ‖ₑ ≤ 1 := by
    rw [← ofReal_norm]
    exact (ENNReal.ofReal_le_ofReal
      (LinearMap.mkContinuous₂_norm_le (LinearMap.mul ℝ ℂ) zero_le_one
        (fun x y => by simpa only [LinearMap.mul_apply', one_mul] using norm_mul_le x y))).trans_eq
      ENNReal.ofReal_one
  by_contra hn
  have hlt : ν.variation univ < η.variation univ := lt_of_not_ge hn
  obtain ⟨partition, _, hpartitiond, hpartitionm, hpartitiongt⟩ :=
    VectorMeasure.exists_lt_sum_of_lt_variation η MeasurableSet.univ hlt
  have hsum : ∑ E ∈ partition, ‖η E‖ₑ ≤ ν.variation univ := by
    calc
      _ ≤ ∑ E ∈ partition, ∫⁻ v, ‖f E v‖ₑ ∂ν.variation := by
        apply Finset.sum_le_sum
        intro E hE
        dsimp only [η]
        rw [ballExitRestart_fourier_apply hH hLE hd hlam hLam B hB v₀ hR P T H ξ E
          (hpartitionm E hE), enorm_mul, ← ofReal_norm, norm_exitFourierStepPhase,
          ENNReal.ofReal_one, one_mul]
        exact VectorMeasure.enorm_integral_le_lintegral_enorm |>.trans
          (by simpa only [one_mul] using
            (mul_le_mul' hmulNorm (le_refl (∫⁻ v, ‖f E v‖ₑ ∂ν.variation))))
      _ = ∫⁻ v, ∑ E ∈ partition, ‖f E v‖ₑ ∂ν.variation := by
        rw [lintegral_finsetSum partition (fun E hE =>
          (measurable_ballLaterExitFourierTest hH hLE hd hlam hLam B hB v₀ hR
            H.1 T.1 H.2.2 ξ E (hpartitionm E hE)).enorm)]
      _ ≤ ∫⁻ _v, (1 : ℝ≥0∞) ∂ν.variation := by
        apply lintegral_mono
        intro v
        dsimp only
        by_cases hv : v ∈ movingDomain (PDE.euclideanBall v₀ R) (fun _ => 0) H.1
        · have heq : (∑ E ∈ partition, ‖f E v‖ₑ) =
              ∑ E ∈ partition, ‖ballLaterExitFourier hH hLE hd hlam hLam B hB v₀ hR
                H.1 T.1 H.2.2 ξ ⟨v, hv⟩ E‖ₑ := by
            apply Finset.sum_congr rfl
            intro E _
            dsimp only [f]
            rw [ballLaterExitFourierTest_valid hH hLE hd hlam hLam B hB v₀ hR
              H.1 T.1 H.2.2 ξ E ⟨v, hv⟩]
          rw [heq]
          exact (VectorMeasure.le_variation _ MeasurableSet.univ
            (fun E _ => subset_univ E) hpartitiond).trans
            (ballLaterExitFourier_variation_le_one hH hLE hd hlam hLam B hB v₀ hR
              H.1 T.1 H.2.2 ξ ⟨v, hv⟩)
        · have heq : (∑ E ∈ partition, ‖f E v‖ₑ) = 0 := by
            apply Finset.sum_eq_zero
            intro E _
            dsimp only [f]
            rw [ballLaterExitFourierTest_invalid hH hLE hd hlam hLam B hB v₀ hR
              H.1 T.1 H.2.2 ξ E v hv, enorm_zero]
          rw [heq]
          exact zero_le
      _ = ν.variation univ := by simp only [lintegral_const, one_mul]
  exact (not_lt_of_ge hsum) hpartitiongt

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
