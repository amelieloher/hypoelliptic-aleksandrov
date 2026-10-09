module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionOverlapRestriction
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionOverlapPartition

/-! # Source time-position overlap convolution for canonical active Green mixtures

Source: companion paper, Section 8. Constants are selected before coefficients, clocks,
starting measures, translated grids, and output cells.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory Filter
open scoped ENNReal Classical

/-- The literal exponential delay and finite-speed position overlap kernel. -/
def positionOverlapWeight (c₀ : ℝ) (i j : ℕ) (ell k : ℤ) : ℝ≥0∞ :=
  if j ≤ i ∧ |((ell - k : ℤ) : ℝ)| ≤ 5 * ((i : ℝ) - (j : ℝ) + 1) then
    ENNReal.ofReal (Real.exp (-c₀ * positionOverlapDelay i j)) else 0

/-- Each starting cell has its mass times the source exponential tail on an output cell. -/
theorem position_source_cell_norm (hpush : PushforwardStatement)
    (htail : RestartTailStatement)
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (q : ℝ) (hq : 1 < q ∧ q < 3 / 2) :
    ∃ C c₀ : ℝ, 0 < C ∧ 0 < c₀ ∧ ∀ (A : SmoothAutonomous lam Lam)
      (c : Clock) (_hc : |c.vbar| = 2 * c.r) (s x : ℝ)
      (nu : Measure Point) [IsFiniteMeasure nu],
      (∀ᵐ e ∂nu, e.velocity 0 ∈ c.active) →
      ∀ (i j : ℕ) (ell k : ℤ),
      positionPositiveNorm (volume.restrict (enlargedOutputCell c s x i ell)) q
        (positionMixtureDensity hH hLE hlam hLam A c
          (nu.restrict (enlargedStartCell c s x j k))) ≤
        ENNReal.ofReal (C * c.r ^ (6 / q - 4)) *
          positionOverlapWeight c₀ i j ell k * nu (enlargedStartCell c s x j k) := by
  have : SigmaFinite (volume : Measure Point) := density_volume_sigmaFinite
  obtain ⟨C, c₀, hC, hc₀, hd⟩ := positionActiveDensity_tail hpush htail hH hLE hlam hLam q hq
  refine ⟨C, c₀, hC, hc₀, ?_⟩
  intro A c hc s x nu hfinite hnu i j ell k
  let E := enlargedOutputCell c s x i ell
  let B := enlargedStartCell c s x j k
  let F := positionActiveDensity hH hLE hlam hLam A c
  have hF := measurable_positionActiveDensity hH hLE hlam hLam A c
  have hq0 : 0 < q := by linarith [hq.1]
  by_cases hover : j ≤ i ∧ |((ell - k : ℤ) : ℝ)| ≤ 5 * ((i : ℝ) - (j : ℝ) + 1)
  · let K := ENNReal.ofReal (C * Real.exp (-c₀ * positionOverlapDelay i j) *
      c.r ^ (6 / q - 4))
    have hpole : ∀ᵐ e ∂nu.restrict B, positionPositiveNorm (volume.restrict E) q (F e) ≤ K := by
      filter_upwards [ae_restrict_of_ae hnu,
        ae_restrict_mem (measurableSet_enlargedStartCell c s x j k)] with e hv he
      have hdelay : 0 ≤ positionOverlapDelay i j * c.r ^ 2 :=
        mul_nonneg (le_max_right _ _) (sq_nonneg _)
      have h := hd A c e hv (positionOverlapDelay i j * c.r ^ 2) hdelay
      have hexp : -c₀ * (positionOverlapDelay i j * c.r ^ 2) / c.r ^ 2 =
          -c₀ * positionOverlapDelay i j := by field_simp [c.positive.ne']
      rw [hexp] at h
      exact positionActiveDensity_output_tail hpush hH hLE hlam hLam A c hc s x j i k ell
        e he hv q hq0 K h
    have hn := positionPositiveNorm_mixture_le (nu.restrict B) (volume.restrict E)
      F hF q hq.1 K hpole
    change positionPositiveNorm (volume.restrict E) q
      (positionMixtureDensity hH hLE hlam hLam A c (nu.restrict B)) ≤
        (nu.restrict B) univ * K at hn
    apply hn.trans_eq
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
    unfold K positionOverlapWeight
    rw [ite_eq_left hover]
    rw [show C * Real.exp (-c₀ * positionOverlapDelay i j) * c.r ^ (6 / q - 4) =
      (C * c.r ^ (6 / q - 4)) * Real.exp (-c₀ * positionOverlapDelay i j) by ring,
      ENNReal.ofReal_mul (mul_nonneg hC.le (Real.rpow_nonneg c.positive.le _))]
    exact mul_comm _ _
  · have hpole : ∀ᵐ e ∂nu.restrict B, positionPositiveNorm (volume.restrict E) q (F e) ≤ 0 := by
      filter_upwards [ae_restrict_of_ae hnu,
        ae_restrict_mem (measurableSet_enlargedStartCell c s x j k)] with e hv he
      have hz := positionActiveDensity_output_zero hpush hH hLE hlam hLam A c hc s x j i k ell
        e he hv hover
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
    simpa only [positionOverlapWeight, ite_eq_right hover, mul_zero, zero_mul] using hn

/-- The canonical mixture satisfies the source exponential two-index overlap convolution. -/
theorem position_density_convolution_positive (hpush : PushforwardStatement)
    (htail : RestartTailStatement)
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (q : ℝ) (hq : 1 < q ∧ q < 3 / 2) :
    ∃ C c₀ : ℝ, 0 < C ∧ 0 < c₀ ∧ ∀ (A : SmoothAutonomous lam Lam)
      (c : Clock) (_hc : |c.vbar| = 2 * c.r) (s x : ℝ)
      (nu : Measure Point) [IsFiniteMeasure nu],
      (∀ᵐ e ∂nu, s ≤ e.time ∧ e.velocity 0 ∈ c.active) →
      ∀ (i : ℕ) (ell : ℤ),
      positionPositiveNorm (volume.restrict (enlargedOutputCell c s x i ell)) q
        (positionMixtureDensity hH hLE hlam hLam A c nu) ≤
        ENNReal.ofReal (C * c.r ^ (6 / q - 4)) *
          ∑' a : ℕ × ℤ, positionOverlapWeight c₀ i a.1 ell a.2 *
            nu (enlargedStartCell c s x a.1 a.2) := by
  have : SigmaFinite (volume : Measure Point) := density_volume_sigmaFinite
  obtain ⟨C, c₀, hC, hc₀, hd⟩ := position_source_cell_norm hpush htail hH hLE hlam hLam q hq
  refine ⟨C, c₀, hC, hc₀, ?_⟩
  intro A c hc s x nu hfinite hnu i ell
  have ht := hnu.mono (fun _ h => h.1)
  have hv := hnu.mono (fun _ h => h.2)
  rw [positionMixtureDensity_sum_cells hH hLE hlam hLam A c nu s x ht]
  apply (positionPositiveNorm_tsum (volume.restrict (enlargedOutputCell c s x i ell))
    q hq.1.le
    (fun a : ℕ × ℤ => positionMixtureDensity hH hLE hlam hLam A c
      (nu.restrict (enlargedStartCell c s x a.1 a.2)))
    (fun a : ℕ × ℤ => measurable_positionMixtureDensity hH hLE hlam hLam A c
      (nu.restrict (enlargedStartCell c s x a.1 a.2)))).trans
  calc
    _ ≤ ∑' a : ℕ × ℤ, ENNReal.ofReal (C * c.r ^ (6 / q - 4)) *
        positionOverlapWeight c₀ i a.1 ell a.2 * nu (enlargedStartCell c s x a.1 a.2) :=
      ENNReal.tsum_le_tsum (fun a => hd A c hc s x nu hv i a.1 ell a.2)
    _ = _ := by simp_rw [mul_assoc]; rw [ENNReal.tsum_mul_left]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
