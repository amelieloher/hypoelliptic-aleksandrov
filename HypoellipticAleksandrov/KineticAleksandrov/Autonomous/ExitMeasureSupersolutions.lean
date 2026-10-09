module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitMeasureProbability

/-! # Actual exit-mass estimates from classical supersolutions -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Filter
open SectionTwo TheoremA Evolution
open scoped ENNReal

/-- A nonnegative smooth supersolution bounds the actual exit mass of any boundary set
on which it is at least one. The identity used here is proved for the actual measures. -/
theorem stripExitOfRealization_le_supersolution
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ))
    (phi : Point → ℝ)
    (hphi : ContDiff ℝ (⊤ : ℕ∞) (phi ∘ reconstructionPhysicalHomeomorph))
    (hb : ∃ M : ℝ, ∀ p, e.1.time ≤ p.time → p.time ≤ T →
      p.velocity 0 ∈ H.carrier → |phi p| ≤ M ∧ |forwardScalarOperator A.a phi p| ≤ M)
    (hop : ∀ p, e.1.time ≤ p.time → p ∈ stripPast H T →
      forwardScalarOperator A.a phi p ≤ 0)
    (hn : ∀ p, e.1.time ≤ p.time → p.time ≤ T →
      p.velocity 0 ∈ Icc H.lo H.hi → 0 ≤ phi p)
    (B : Set Point) (hB : MeasurableSet B)
    (hbd : ∀ p ∈ B, e.1.time ≤ p.time → p.time ≤ T →
      p.velocity 0 ∈ Icc H.lo H.hi → 1 ≤ phi p) :
    stripExitOfRealization hH hlam hLam A H E hE T e B ≤ ENNReal.ofReal (phi e.1) := by
  let Ω := stripExitOfRealization hH hlam hLam A H E hE T e
  let Γ := stripGreenOfKernel H E.2 T e
  have hi := strip_identity_bounded_smooth_future_of_realization hH hlam hLam A H E hE T e
    phi hphi hb
  have hnonpos : (∫ p, forwardScalarOperator A.a phi p ∂Γ) ≤ 0 := by
    apply integral_nonpos_of_ae
    filter_upwards [stripGreenOfKernel_ae_mem_stripPast H E.2 T e,
      reconstruction_green_ae_time_gt H E.2 T e] with p hp ht
    exact hop p ht.le hp
  have hΩ := stripExitOfRealization_ae_closed_future hH hlam hLam A H E hE T e
  have hc := reconstruction_smooth_physical_continuous phi hphi
  obtain ⟨M, hM⟩ := hb
  have hint : Integrable phi Ω := by
    apply Integrable.mono' (integrable_const (max M 0)) hc.measurable.aestronglyMeasurable
    filter_upwards [hΩ] with p hp
    rw [Real.norm_eq_abs]
    exact (reconstruction_closed_velocity_slice_bound H phi hc M p hp.2.2
      (fun v hv => (hM ⟨p.time, p.position, fun _ => v⟩ hp.1 hp.2.1 hv).1)).trans
        (le_max_left _ _)
  have hnn : 0 ≤ᵐ[Ω] phi := by
    filter_upwards [hΩ] with p hp
    exact hn p hp.1 hp.2.1 hp.2.2
  calc Ω B = ∫⁻ p, B.indicator 1 p ∂Ω := (lintegral_indicator_one hB).symm
    _ ≤ ∫⁻ p, ENNReal.ofReal (phi p) ∂Ω := by
      apply lintegral_mono_ae
      filter_upwards [hΩ] with p hp
      by_cases hpb : p ∈ B
      · rw [indicator_of_mem hpb, Pi.one_apply]
        exact ENNReal.one_le_ofReal.mpr (hbd p hpb hp.1 hp.2.1 hp.2.2)
      · simp only [indicator_of_notMem hpb, zero_le]
    _ = ENNReal.ofReal (∫ p, phi p ∂Ω) :=
      (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
    _ ≤ ENNReal.ofReal (phi e.1) := ENNReal.ofReal_le_ofReal (by
      change phi e.1 = (∫ p, phi p ∂Ω) - (∫ p, forwardScalarOperator A.a phi p ∂Γ) at hi
      linarith)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
