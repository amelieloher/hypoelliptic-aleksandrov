module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.IntegratedVelocity
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoxConcentrationAveraging

/-! # Averaging the velocity-band comparison over the later time window -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov MeasureTheory Set

/-- The later window has length `t`; its occupation is bounded by occupation through `3t`. -/
theorem velocity_return_time_average {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E) (z : Z) (r t C : ℝ)
    (ht : 0 < t) (hC : 0 ≤ C)
    (hcomp : ∀ s ∈ Ioc (2 * t) (3 * t),
      velocityBandAction E r t z ≤ C * velocityBandAction E r s z) :
    t * velocityBandAction E r t z ≤
      C * ∫ s in Ioc 0 (3 * t), velocityBandAction E r s z := by
  let f := fun s => velocityBandAction E r s z
  have hi : IntegrableOn (fun s => velocityBandAction E r s z) (Ioc 0 (3 * t)) :=
    velocityBandAction_integrable A E hE r (3 * t) z
  have hs : Ioc (2 * t) (3 * t) ⊆ Ioc 0 (3 * t) :=
    fun s hs => ⟨by linarith [hs.1], hs.2⟩
  have hsmall := hi.mono_set hs
  have hmono := setIntegral_mono_on
    (integrableOn_const (C := f t) (by simp : volume (Ioc (2 * t) (3 * t)) ≠ ⊤))
    (hsmall.const_mul C) measurableSet_Ioc hcomp
  have hvol : volume.real (Ioc (2 * t) (3 * t)) = t := by
    rw [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
    ring
  rw [setIntegral_const, hvol, smul_eq_mul, integral_const_mul] at hmono
  have hnonneg : ∀ s, 0 ≤ velocityBandAction E r s z := fun s => by
    rw [velocityBandAction_eq_probability A E hE]
    exact ENNReal.toReal_nonneg
  exact hmono.trans (mul_le_mul_of_nonneg_left
    (setIntegral_mono_set hi (Filter.Eventually.of_forall hnonneg)
      (Filter.Eventually.of_forall hs)) hC)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
