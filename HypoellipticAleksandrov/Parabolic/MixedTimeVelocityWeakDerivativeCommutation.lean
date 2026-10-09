module

public import HypoellipticAleksandrov.Parabolic.WeakDerivativesAlgebra

/-!
# Commutation of mixed time and velocity weak derivatives

This module derives a selected weak time derivative of a selected velocity
derivative from the corresponding velocity derivative of the selected weak
time derivative.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory Set

private theorem timeDerivative_contDiff_infty
    {d : ℕ} {f : TimeVelocity d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (timeDerivative f) := by
  unfold timeDerivative
  exact (contDiff_infty_iff_fderiv.mp hf).2.clm_apply contDiff_const

private theorem velocityGradient_contDiff_infty
    {d : ℕ} {f : TimeVelocity d → ℝ} (k : Fin d)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => velocityGradient f z k) := by
  unfold velocityGradient
  exact (contDiff_infty_iff_fderiv.mp hf).2.clm_apply contDiff_const

private theorem timeDerivative_hasCompactSupport
    {d : ℕ} {f : TimeVelocity d → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (timeDerivative f) := by
  unfold timeDerivative
  simpa using hf.fderiv_apply (𝕜 := ℝ) ((1, 0) : TimeVelocity d)

private theorem velocityGradient_hasCompactSupport
    {d : ℕ} {f : TimeVelocity d → ℝ} (k : Fin d)
    (hf : HasCompactSupport f) :
    HasCompactSupport (fun z => velocityGradient f z k) := by
  unfold velocityGradient
  simpa using hf.fderiv_apply (𝕜 := ℝ)
    ((0, Pi.single k 1) : TimeVelocity d)

private theorem timeDerivative_tsupport_subset
    {d : ℕ} (f : TimeVelocity d → ℝ) :
    tsupport (timeDerivative f) ⊆ tsupport f := by
  unfold timeDerivative
  change closure (Function.support (fun z => fderiv ℝ f z (1, 0))) ⊆ tsupport f
  refine (closure_mono ?_).trans (tsupport_fderiv_subset ℝ)
  intro z hz
  rw [Function.mem_support] at hz ⊢
  intro hzero
  apply hz
  simp [hzero]

private theorem velocityGradient_tsupport_subset
    {d : ℕ} (f : TimeVelocity d → ℝ) (k : Fin d) :
    tsupport (fun z => velocityGradient f z k) ⊆ tsupport f := by
  unfold velocityGradient
  change closure (Function.support
    (fun z => fderiv ℝ f z (0, Pi.single k 1))) ⊆ tsupport f
  refine (closure_mono ?_).trans (tsupport_fderiv_subset ℝ)
  intro z hz
  rw [Function.mem_support] at hz ⊢
  intro hzero
  apply hz
  simp [hzero]

private theorem time_velocity_derivative_commute
    {d : ℕ} (f : TimeVelocity d → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (k : Fin d) (z : TimeVelocity d) :
    velocityGradient (timeDerivative f) z k =
      timeDerivative (fun w => velocityGradient f w k) z := by
  have hgrad : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) :=
    (contDiff_infty_iff_fderiv.mp hf).2
  have heval (a b : TimeVelocity d) :
      fderiv ℝ (fun x => fderiv ℝ f x a) z b =
        fderiv ℝ (fderiv ℝ f) z b a := by
    rw [fderiv_clm_apply (hgrad.differentiable (by simp) z)
      (differentiableAt_const (c := a))]
    rw [fderiv_const_apply]
    simp
  unfold timeDerivative velocityGradient
  rw [heval (1, 0) (0, Pi.single k 1),
    heval (0, Pi.single k 1) (1, 0)]
  have hfTwo : ContDiffAt ℝ 2 f z :=
    hf.contDiffAt.of_le (WithTop.coe_le_coe.mpr
      (show (2 : ℕ∞) ≤ ⊤ from le_top))
  exact (hfTwo.isSymmSndFDerivAt (by norm_num)).eq
    (0, Pi.single k 1) (1, 0)

/-- Weak time and velocity derivatives commute when all three selected
distributional relations are available. -/
theorem hasWeakTimeDerivOn_of_hasWeakVelocityPartialDerivOn_timeDeriv
    {d : ℕ} {U : Set (TimeVelocity d)} (k : Fin d)
    {u ut uk r : TimeVelocity d → ℝ}
    (hut : HasWeakTimeDerivOn U u ut)
    (huk : HasWeakVelocityPartialDerivOn U k u uk)
    (hutk : HasWeakVelocityPartialDerivOn U k ut r) :
    HasWeakTimeDerivOn U uk r := by
  intro φ hφ hφcompact hφU
  have htφ := huk (timeDerivative φ)
    (timeDerivative_contDiff_infty hφ)
    (timeDerivative_hasCompactSupport hφcompact)
    ((timeDerivative_tsupport_subset φ).trans hφU)
  have hkφ := hut (fun z => velocityGradient φ z k)
    (velocityGradient_contDiff_infty k hφ)
    (velocityGradient_hasCompactSupport k hφcompact)
    ((velocityGradient_tsupport_subset φ k).trans hφU)
  have hutkφ := hutk φ hφ hφcompact hφU
  have hmixed : (∫ z in U, u z * velocityGradient (timeDerivative φ) z k
      ∂(volume : Measure (TimeVelocity d))) =
      ∫ z in U, u z * timeDerivative (fun w => velocityGradient φ w k) z
        ∂(volume : Measure (TimeVelocity d)) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => by
      dsimp only
      rw [time_velocity_derivative_commute φ hφ k z]
  rw [hmixed, hkφ] at htφ
  linarith

/-- A selected weak time derivative of a selected velocity derivative is
also the corresponding weak velocity derivative of the selected time
derivative. -/
theorem hasWeakVelocityPartialDerivOn_of_hasWeakTimeDerivOn_velocityDeriv
    {d : ℕ} {U : Set (TimeVelocity d)} (k : Fin d)
    {u ut uk r : TimeVelocity d → ℝ}
    (hut : HasWeakTimeDerivOn U u ut)
    (huk : HasWeakVelocityPartialDerivOn U k u uk)
    (hukt : HasWeakTimeDerivOn U uk r) :
    HasWeakVelocityPartialDerivOn U k ut r := by
  intro φ hφ hφcompact hφU
  have htφ := huk (timeDerivative φ)
    (timeDerivative_contDiff_infty hφ)
    (timeDerivative_hasCompactSupport hφcompact)
    ((timeDerivative_tsupport_subset φ).trans hφU)
  have hkφ := hut (fun z => velocityGradient φ z k)
    (velocityGradient_contDiff_infty k hφ)
    (velocityGradient_hasCompactSupport k hφcompact)
    ((velocityGradient_tsupport_subset φ k).trans hφU)
  have huktφ := hukt φ hφ hφcompact hφU
  have hmixed : (∫ z in U, u z * velocityGradient (timeDerivative φ) z k
      ∂(volume : Measure (TimeVelocity d))) =
      ∫ z in U, u z * timeDerivative (fun w => velocityGradient φ w k) z
        ∂(volume : Measure (TimeVelocity d)) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => by
      dsimp only
      rw [time_velocity_derivative_commute φ hφ k z]
  rw [hmixed, hkφ] at htφ
  linarith

end HypoellipticAleksandrov.Parabolic
