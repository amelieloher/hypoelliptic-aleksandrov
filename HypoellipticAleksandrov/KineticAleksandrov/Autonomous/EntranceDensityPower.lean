module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TimeBinConvolutionYoung
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionDensitySumPartition

/-! # The source integrated time-bin density q-power estimate -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory Filter
open scoped ENNReal

/-- Full-position output bins partition the entire active observation region. -/
theorem entranceOutputBin_iUnion (c : Clock) :
    (⋃ j : ℤ, entranceOutputBin c j) = {p | p.velocity 0 ∈ c.active} := by
  unfold entranceOutputBin
  rw [← iUnion_inter, iUnion_entranceTimeBin c.r c.positive, univ_inter]

/-- Full-position output bins remain pairwise disjoint. -/
theorem entranceOutputBin_pairwise (c : Clock) :
    Pairwise (fun i j => Disjoint (entranceOutputBin c i) (entranceOutputBin c j)) := by
  intro i j hij
  exact (entranceTimeBin_pairwise c.r hij).mono inter_subset_left inter_subset_left

/-- The actual positive mixture density vanishes away from the whole active interval. -/
theorem entranceMixtureDensity_support (hpush : PushforwardStatement)
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (nu : Measure Point) [SFinite nu]
    (hnu : ∀ᵐ e ∂nu, e.velocity 0 ∈ c.active) :
    ∀ᵐ z ∂(volume : Measure Point),
      positionMixtureDensity hH hLE hlam hLam A c nu z ≠ 0 → z.velocity 0 ∈ c.active := by
  have hm := measurable_positionMixtureDensity hH hLE hlam hLam A c nu
  apply (ae_withDensity_iff hm).mp
  rw [withDensity_positionMixtureDensity hpush hH hLE hlam hLam]
  have hS : MeasurableSet {z : Point | z.velocity 0 ∈ c.active} :=
    isOpen_Ioo.measurableSet.preimage ((continuous_apply 0).comp continuous_velocity).measurable
  apply Measure.ae_comp_of_ae_ae hS
  filter_upwards [hnu] with e he
  rw [← withDensity_positionActiveDensity hpush hH hLE hlam hLam]
  apply (ae_withDensity_iff ((measurable_positionActiveDensity hH hLE hlam hLam A c).comp
    (measurable_const.prodMk measurable_id))).mpr
  filter_upwards [timeActiveDensity_support hpush hH hLE hlam hLam A c e he]
    with z hz hn
  exact (hz hn).2

/-- Summing output-bin q-power norms gives exactly the whole density power integral. -/
theorem entranceMixtureDensity_power_partition (hpush : PushforwardStatement)
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (nu : Measure Point) [SFinite nu]
    (q : ℝ) (hq : 0 < q) (hnu : ∀ᵐ e ∂nu, e.velocity 0 ∈ c.active) :
    (∫⁻ z, positionMixtureDensity hH hLE hlam hLam A c nu z ^ q ∂volume) =
      ∑' j : ℤ, positionPositiveNorm (volume.restrict (entranceOutputBin c j)) q
        (positionMixtureDensity hH hLE hlam hLam A c nu) ^ q := by
  let F := positionMixtureDensity hH hLE hlam hLam A c nu
  let U := {z : Point | z.velocity 0 ∈ c.active}
  have hU : MeasurableSet U :=
    isOpen_Ioo.measurableSet.preimage ((continuous_apply 0).comp continuous_velocity).measurable
  have he : (∫⁻ z, F z ^ q ∂volume) = ∫⁻ z in U, F z ^ q ∂volume := by
    rw [← lintegral_indicator hU]
    apply lintegral_congr_ae
    filter_upwards [entranceMixtureDensity_support hpush hH hLE hlam hLam A c nu hnu]
      with z hz
    by_cases h : z ∈ U
    · simp only [indicator_of_mem h]
    · have hf : F z = 0 := by by_contra hn; exact h (hz hn)
      simp only [indicator_of_notMem h, hf, ENNReal.zero_rpow_of_pos hq]
  rw [he]
  change (∫⁻ z in {p | p.velocity 0 ∈ c.active}, F z ^ q ∂volume) = _
  rw [← entranceOutputBin_iUnion c,
    lintegral_iUnion (measurableSet_entranceOutputBin c) (entranceOutputBin_pairwise c)]
  apply tsum_congr
  intro j
  exact (positionPositiveNorm_rpow _ q hq F).symm

/-- The genuine time-bin convolution gives the source global q-power density estimate. -/
theorem entrance_density_power_sum
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (q : ℝ) (hq : 1 < q ∧ q < 3 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam)
      (c : Clock) (nu : Measure Point) [IsFiniteMeasure nu],
      (∀ᵐ e ∂nu, e.velocity 0 ∈ c.active) →
      (∫⁻ z, positionMixtureDensity hH hLE hlam hLam A c nu z ^ q ∂volume) ≤
        ENNReal.ofReal (C * c.r ^ (6 - 4 * q)) *
          ∑' k : ℤ, nu (entranceTimeBin c.r k) ^ q := by
  obtain ⟨C, c₀, hC, hc₀, hd⟩ := entrance_time_bin_convolution hH hLE hlam hLam q hq
  let W := ∑' k : ℤ, Real.exp (-c₀ * |(k : ℝ)|)
  have hs := position_exp_abs_summable c₀ hc₀
  have hw (k : ℤ) : 0 ≤ Real.exp (-c₀ * |(k : ℝ)|) := (Real.exp_pos _).le
  have hW : 0 < W := hs.tsum_pos hw 0 (Real.exp_pos _)
  have hWe : (∑' k : ℤ, ENNReal.ofReal (Real.exp (-c₀ * |(k : ℝ)|))) =
      ENNReal.ofReal W := (ENNReal.ofReal_tsum_of_nonneg hw hs).symm
  let D := C * Real.exp c₀ * W
  have hD : 0 < D := mul_pos (mul_pos hC (Real.exp_pos _)) hW
  refine ⟨D ^ q, Real.rpow_pos_of_pos hD q, ?_⟩
  intro A c nu hfinite hnu
  have hq0 : 0 < q := by linarith [hq.1]
  rw [entranceMixtureDensity_power_partition (pushforwardStatement_holds)
    hH hLE hlam hLam A c nu q hq0 hnu]
  calc
    _ ≤ ∑' j : ℤ, (ENNReal.ofReal (C * c.r ^ (6 / q - 4)) *
        ∑' k : ℤ, entranceBinWeight c₀ j k * nu (entranceTimeBin c.r k)) ^ q :=
      ENNReal.tsum_le_tsum (fun j => ENNReal.rpow_le_rpow (hd A c nu hnu j) hq0.le)
    _ = ENNReal.ofReal (C * c.r ^ (6 / q - 4)) ^ q *
        ∑' j : ℤ, (∑' k : ℤ, entranceBinWeight c₀ j k * nu (entranceTimeBin c.r k)) ^ q := by
      simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le]
      rw [ENNReal.tsum_mul_left]
    _ ≤ ENNReal.ofReal (C * c.r ^ (6 / q - 4)) ^ q *
        ((ENNReal.ofReal (Real.exp c₀) * ENNReal.ofReal W) ^ q *
          ∑' k : ℤ, nu (entranceTimeBin c.r k) ^ q) := by
      rw [← hWe]
      exact mul_le_mul_right (entrance_convolution_power_sum c₀ hc₀
        (fun k => nu (entranceTimeBin c.r k)) q hq.1) _
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.mul_rpow_of_nonneg _ _ hq0.le,
        ← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← ENNReal.ofReal_mul (mul_nonneg hC.le (Real.rpow_nonneg c.positive.le _)),
        ENNReal.ofReal_rpow_of_pos
          (mul_pos (mul_pos hC (Real.rpow_pos_of_pos c.positive _))
            (mul_pos (Real.exp_pos _) hW))]
      congr 2
      have hbase : C * c.r ^ (6 / q - 4) * (Real.exp c₀ * W) =
          D * c.r ^ (6 / q - 4) := by dsimp [D]; ring
      rw [hbase, Real.mul_rpow hD.le (Real.rpow_nonneg c.positive.le _),
        ← Real.rpow_mul c.positive.le]
      congr 2
      field_simp

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
