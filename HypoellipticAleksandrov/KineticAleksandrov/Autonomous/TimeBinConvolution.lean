module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TimeBinConvolutionKernel
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PoleDensityStatement

/-! # The source one-index exponential time-bin convolution

Source: companion paper, Lemma 8.6. No spatial grid or centre-to-radius equality is used.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory Filter
open scoped ENNReal Classical

/-- The causal time-bin kernel, including the adjacent-bin delay. -/
def entranceBinWeight (c₀ : ℝ) (j k : ℤ) : ℝ≥0∞ :=
  if k ≤ j then ENNReal.ofReal (Real.exp (-c₀ * entranceBinDelay j k)) else 0

/-- Each source-bin mixture inherits its mass times the proved restarted-tail norm. -/
theorem entrance_source_bin_norm (hpush : PushforwardStatement)
    (htail : RestartTailStatement)
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (q : ℝ) (hq : 1 < q ∧ q < 3 / 2) :
    ∃ C c₀ : ℝ, 0 < C ∧ 0 < c₀ ∧ ∀ (A : SmoothAutonomous lam Lam)
      (c : Clock) (nu : Measure Point) [IsFiniteMeasure nu],
      (∀ᵐ e ∂nu, e.velocity 0 ∈ c.active) → ∀ j k : ℤ,
      positionPositiveNorm (volume.restrict (entranceOutputBin c j)) q
        (positionMixtureDensity hH hLE hlam hLam A c (nu.restrict (entranceTimeBin c.r k))) ≤
        ENNReal.ofReal (C * c.r ^ (6 / q - 4)) * entranceBinWeight c₀ j k *
          nu (entranceTimeBin c.r k) := by
  have : SigmaFinite (volume : Measure Point) := density_volume_sigmaFinite
  obtain ⟨C, c₀, hC, hc₀, hd⟩ := positionActiveDensity_tail hpush htail hH hLE hlam hLam q hq
  refine ⟨C, c₀, hC, hc₀, ?_⟩
  intro A c nu hfinite hnu j k
  let E := entranceOutputBin c j
  let B := entranceTimeBin c.r k
  let F := positionActiveDensity hH hLE hlam hLam A c
  have hF := measurable_positionActiveDensity hH hLE hlam hLam A c
  have hq0 : 0 < q := by linarith [hq.1]
  by_cases hkj : k ≤ j
  · let K := ENNReal.ofReal (C * Real.exp (-c₀ * entranceBinDelay j k) *
      c.r ^ (6 / q - 4))
    have hpole : ∀ᵐ e ∂nu.restrict B, positionPositiveNorm (volume.restrict E) q (F e) ≤ K := by
      filter_upwards [ae_restrict_of_ae hnu,
        ae_restrict_mem (measurableSet_entranceTimeBin c.r k)] with e hv he
      have hdelay : 0 ≤ entranceBinDelay j k * c.r ^ 2 :=
        mul_nonneg (le_max_right _ _) (sq_nonneg _)
      have h := hd A c e hv (entranceBinDelay j k * c.r ^ 2) hdelay
      have hexp : -c₀ * (entranceBinDelay j k * c.r ^ 2) / c.r ^ 2 =
          -c₀ * entranceBinDelay j k := by field_simp [c.positive.ne']
      rw [hexp] at h
      exact timeActiveDensity_output_tail hpush hH hLE hlam hLam A c e j k he hv q hq0 K h
    have hn := positionPositiveNorm_mixture_le (nu.restrict B) (volume.restrict E)
      F hF q hq.1 K hpole
    change positionPositiveNorm (volume.restrict E) q
      (positionMixtureDensity hH hLE hlam hLam A c (nu.restrict B)) ≤
        (nu.restrict B) univ * K at hn
    apply hn.trans_eq
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
    unfold K entranceBinWeight
    rw [ite_eq_left hkj]
    rw [show C * Real.exp (-c₀ * entranceBinDelay j k) * c.r ^ (6 / q - 4) =
      (C * c.r ^ (6 / q - 4)) * Real.exp (-c₀ * entranceBinDelay j k) by ring,
      ENNReal.ofReal_mul (mul_nonneg hC.le (Real.rpow_nonneg c.positive.le _))]
    exact mul_comm _ _
  · have hpole : ∀ᵐ e ∂nu.restrict B, positionPositiveNorm (volume.restrict E) q (F e) ≤ 0 := by
      filter_upwards [ae_restrict_of_ae hnu,
        ae_restrict_mem (measurableSet_entranceTimeBin c.r k)] with e hv he
      have hz := timeActiveDensity_output_zero hpush hH hLE hlam hLam A c e j k
        he hv (lt_of_not_ge hkj)
      unfold positionPositiveNorm
      have hi : (∫⁻ z, F e z ^ q ∂volume.restrict E) = 0 := by
        rw [← lintegral_zero]
        apply lintegral_congr_ae
        filter_upwards [hz] with z hz
        simp only [F, hz, ENNReal.zero_rpow_of_pos hq0]
      rw [hi, ENNReal.zero_rpow_of_pos (one_div_pos.mpr hq0)]
    have hn := positionPositiveNorm_mixture_le (nu.restrict B) (volume.restrict E)
      F hF q hq.1 0 hpole
    change positionPositiveNorm (volume.restrict E) q
      (positionMixtureDensity hH hLE hlam hLam A c (nu.restrict B)) ≤
        (nu.restrict B) univ * 0 at hn
    simpa only [entranceBinWeight, ite_eq_right hkj, mul_zero, zero_mul] using hn

/-- The actual positive mixture decomposes into its full-grid source-bin mixtures. -/
theorem entranceMixtureDensity_sum_bins
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (nu : Measure Point) :
    positionMixtureDensity hH hLE hlam hLam A c nu =
      fun z => ∑' k : ℤ, positionMixtureDensity hH hLE hlam hLam A c
        (nu.restrict (entranceTimeBin c.r k)) z := by
  have he : nu = Measure.sum (fun k : ℤ => nu.restrict (entranceTimeBin c.r k)) := by
    have hh := Measure.restrict_iUnion (μ := nu) (entranceTimeBin_pairwise c.r)
      (measurableSet_entranceTimeBin c.r)
    rw [iUnion_entranceTimeBin c.r c.positive, Measure.restrict_univ] at hh
    exact hh
  calc
    _ = positionMixtureDensity hH hLE hlam hLam A c
        (Measure.sum (fun k : ℤ => nu.restrict (entranceTimeBin c.r k))) :=
      congrArg (positionMixtureDensity hH hLE hlam hLam A c) he
    _ = _ := by funext z; exact lintegral_sum_measure _ _

/-- The literal source time-bin convolution holds for the actual all-time active mixture. -/
theorem entrance_time_bin_convolution
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (q : ℝ) (hq : 1 < q ∧ q < 3 / 2) :
    ∃ C c₀ : ℝ, 0 < C ∧ 0 < c₀ ∧ ∀ (A : SmoothAutonomous lam Lam)
      (c : Clock) (nu : Measure Point) [IsFiniteMeasure nu],
      (∀ᵐ e ∂nu, e.velocity 0 ∈ c.active) → ∀ j : ℤ,
      positionPositiveNorm (volume.restrict (entranceOutputBin c j)) q
        (positionMixtureDensity hH hLE hlam hLam A c nu) ≤
        ENNReal.ofReal (C * c.r ^ (6 / q - 4)) *
          ∑' k : ℤ, entranceBinWeight c₀ j k * nu (entranceTimeBin c.r k) := by
  obtain ⟨C, c₀, hC, hc₀, hd⟩ := entrance_source_bin_norm
    (pushforwardStatement_holds) (restartTailStatement_holds)
      hH hLE hlam hLam q hq
  refine ⟨C, c₀, hC, hc₀, ?_⟩
  intro A c nu hfinite hnu j
  rw [entranceMixtureDensity_sum_bins hH hLE hlam hLam A c nu]
  apply (positionPositiveNorm_tsum (volume.restrict (entranceOutputBin c j)) q hq.1.le
    (fun k : ℤ => positionMixtureDensity hH hLE hlam hLam A c
      (nu.restrict (entranceTimeBin c.r k)))
    (fun k => measurable_positionMixtureDensity hH hLE hlam hLam A c
      (nu.restrict (entranceTimeBin c.r k)))).trans
  calc
    _ ≤ ∑' k : ℤ, ENNReal.ofReal (C * c.r ^ (6 / q - 4)) *
        entranceBinWeight c₀ j k * nu (entranceTimeBin c.r k) :=
      ENNReal.tsum_le_tsum (fun k => hd A c nu hnu j k)
    _ = _ := by simp_rw [mul_assoc]; rw [ENNReal.tsum_mul_left]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
