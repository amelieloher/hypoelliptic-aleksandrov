module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GreenTestExtensionBounds

/-! # Removing the compact position cutoff in the actual Green identity -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Filter
open SectionTwo TheoremA Evolution
open scoped Topology

/-- The actual identity holds for every globally smooth test bounded, together with its
operator, on the open velocity strip. No derivative of the coefficient enters the bound. -/
theorem strip_identity_bounded_smooth_future_of_realization
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ))
    (phi : Point → ℝ)
    (hphi : ContDiff ℝ (⊤ : ℕ∞) (phi ∘ reconstructionPhysicalHomeomorph))
    (hb : ∃ M : ℝ, ∀ p, e.1.time ≤ p.time → p.time ≤ T →
      p.velocity 0 ∈ H.carrier →
      |phi p| ≤ M ∧ |forwardScalarOperator A.a phi p| ≤ M) :
    phi e.1 = (∫ p, phi p ∂stripExitOfRealization hH hlam hLam A H E hE T e) -
      ∫ p, forwardScalarOperator A.a phi p ∂stripGreenOfKernel H E.2 T e := by
  obtain ⟨M, hM⟩ := hb
  have hMn : 0 ≤ M := (abs_nonneg (phi e.1)).trans (hM e.1 le_rfl (WithTop.coe_lt_coe.mp
    e.2.1).le e.2.2).1
  have hpc := reconstruction_smooth_physical_continuous phi hphi
  let bx (n : ℕ) := reconstructionPositionBump ((n : ℝ) + 1) (by positivity)
  choose F hF hK using fun n => exists_reconstruction_position_probe A H e.1.time T phi hphi
    (bx n)
  let Ω := stripExitOfRealization hH hlam hLam A H E hE T e
  let Γ := stripGreenOfKernel H E.2 T e
  have hΩ := stripExitOfRealization_ae_closed_future hH hlam hLam A H E hE T e
  have hΓ : ∀ᵐ p ∂Γ, e.1.time ≤ p.time ∧ p.time ≤ T ∧ p.velocity 0 ∈ Icc H.lo H.hi := by
    filter_upwards [stripGreenOfKernel_ae_mem_stripPast H E.2 T e,
      reconstruction_green_ae_time_gt H E.2 T e] with p hp ht
    exact ⟨ht.le, hp.1.le, hp.2.1.le, hp.2.2.le⟩
  have hval (n : ℕ) : (fun p => exitProbePhysical (F n) p) =ᵐ[Ω]
      fun p => bx n (p.position 0) * phi p := by
    filter_upwards [hΩ] with p hp
    exact hF n p hp.1 hp.2.1 hp.2.2
  have hsrc (n : ℕ) : (fun p => forwardScalarOperator A.a (exitProbePhysical (F n)) p) =ᵐ[Γ]
      fun p => bx n (p.position 0) * forwardScalarOperator A.a phi p +
        p.velocity 0 * deriv (bx n) (p.position 0) * phi p := by
    filter_upwards [hΓ] with p hp
    exact hK n p hp.1 hp.2.1 hp.2.2
  have hvlim : Tendsto (fun n => ∫ p, exitProbePhysical (F n) p ∂Ω) atTop
      (𝓝 (∫ p, phi p ∂Ω)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => M)
    · intro n
      exact (exitProbePhysical_continuous_compact (F n)).1.measurable.aestronglyMeasurable
    · exact integrable_const M
    · intro n
      filter_upwards [hval n, hΩ] with p hp hs
      rw [Real.norm_eq_abs, hp, abs_mul, abs_of_nonneg (bx n).nonneg]
      exact (mul_le_of_le_one_left (abs_nonneg _) (bx n).le_one).trans
        (reconstruction_closed_velocity_slice_bound H phi hpc M p hs.2.2
          (fun v hv => (hM ⟨p.time, p.position, fun _ => v⟩ hs.1 hs.2.1 hv).1))
    · filter_upwards [hΩ] with p hp
      have hq := (reconstructionPositionBump_tendsto (p.position 0)).mul_const (phi p)
      simp only [one_mul] at hq
      exact hq.congr (fun n => (hF n p hp.1 hp.2.1 hp.2.2).symm)
  obtain ⟨D, hDn, hD⟩ := reconstructionUnitBump_properties.2.2.2
  let V := max |H.lo| |H.hi|
  have hV : 0 ≤ V := (abs_nonneg H.lo).trans (le_max_left _ _)
  have hvbd (p : Point) (hp : p.velocity 0 ∈ Icc H.lo H.hi) : |p.velocity 0| ≤ V := by
    apply abs_le.mpr
    constructor
    · exact ((neg_le_neg (le_max_left |H.lo| |H.hi|)).trans
        (neg_abs_le H.lo)).trans hp.1
    · exact hp.2.trans ((le_abs_self H.hi).trans (le_max_right _ _))
  have hsmeas (n : ℕ) : AEStronglyMeasurable
      (forwardScalarOperator A.a (exitProbePhysical (F n))) Γ :=
    (exitProbeOperatorDatum A (F n)).measurable.aestronglyMeasurable
  have hslim : Tendsto
      (fun n => ∫ p, forwardScalarOperator A.a (exitProbePhysical (F n)) p ∂Γ) atTop
      (𝓝 (∫ p, forwardScalarOperator A.a phi p ∂Γ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => M + V * D * M)
    · exact hsmeas
    · exact integrable_const _
    · intro n
      filter_upwards [hsrc n, stripGreenOfKernel_ae_mem_stripPast H E.2 T e, hΓ]
        with p hp hs ht
      have hv := hvbd p ⟨hs.2.1.le, hs.2.2.le⟩
      have hd : |deriv (bx n) (p.position 0)| ≤ D :=
        (reconstructionPositionBump_deriv_bound _ (by positivity) D hD _).trans (by
          apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mpr
          nlinarith [Nat.cast_nonneg (α := ℝ) n])
      have hh := hM p ht.1 ht.2.1 hs.2
      rw [Real.norm_eq_abs, hp]
      calc
        _ ≤ |bx n (p.position 0) * forwardScalarOperator A.a phi p| +
            |p.velocity 0 * deriv (bx n) (p.position 0) * phi p| := abs_add_le _ _
        _ ≤ M + V * D * M := by
          simp only [abs_mul, abs_of_nonneg (bx n).nonneg]
          apply add_le_add
          · exact (mul_le_of_le_one_left (abs_nonneg _) (bx n).le_one).trans hh.2
          · exact mul_le_mul
              (mul_le_mul hv hd (abs_nonneg _) hV) hh.1 (abs_nonneg _)
              (mul_nonneg hV hDn)
    · filter_upwards [hΓ] with p hp
      have hq := ((reconstructionPositionBump_tendsto (p.position 0)).mul_const
        (forwardScalarOperator A.a phi p)).add
        (((reconstructionPositionBump_deriv_tendsto (p.position 0)).const_mul
          (p.velocity 0)).mul_const (phi p))
      simp only [one_mul, mul_zero, zero_mul, add_zero] at hq
      exact hq.congr (fun n => (hK n p hp.1 hp.2.1 hp.2.2).symm)
  have hpole : Tendsto (fun n => exitProbePhysical (F n) e.1) atTop (𝓝 (phi e.1)) := by
    have ht := (WithTop.coe_lt_coe.mp e.2.1).le
    have hv : e.1.velocity 0 ∈ Icc H.lo H.hi := ⟨e.2.2.1.le, e.2.2.2.le⟩
    have hh := (reconstructionPositionBump_tendsto (e.1.position 0)).mul_const (phi e.1)
    simp only [one_mul] at hh
    exact hh.congr (fun n => (hF n e.1 le_rfl ht hv).symm)
  have hi (n : ℕ) : exitProbePhysical (F n) e.1 =
      (∫ p, exitProbePhysical (F n) p ∂Ω) -
        ∫ p, forwardScalarOperator A.a (exitProbePhysical (F n)) p ∂Γ := by
    have hh := stripExitOfRealization_probe_integral hH hlam hLam A H E hE T e (F n)
    change (∫ p, exitProbePhysical (F n) p ∂Ω) =
      exitProbePhysical (F n) e.1 +
        ∫ p, forwardScalarOperator A.a (exitProbePhysical (F n)) p ∂Γ at hh
    linarith
  exact tendsto_nhds_unique hpole ((hvlim.sub hslim).congr (fun n => (hi n).symm))

/-- The bounded smooth identity under the source's time-uniform open-velocity bounds. -/
theorem strip_identity_bounded_smooth_of_realization
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ))
    (phi : Point → ℝ)
    (hphi : ContDiff ℝ (⊤ : ℕ∞) (phi ∘ reconstructionPhysicalHomeomorph))
    (hb : ∃ M : ℝ, ∀ p, p.velocity 0 ∈ H.carrier →
      |phi p| ≤ M ∧ |forwardScalarOperator A.a phi p| ≤ M) :
    phi e.1 = (∫ p, phi p ∂stripExitOfRealization hH hlam hLam A H E hE T e) -
      ∫ p, forwardScalarOperator A.a phi p ∂stripGreenOfKernel H E.2 T e := by
  apply strip_identity_bounded_smooth_future_of_realization hH hlam hLam A H E hE T e phi hphi
  obtain ⟨M, hM⟩ := hb
  exact ⟨M, fun p _ _ hp => hM p hp⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
