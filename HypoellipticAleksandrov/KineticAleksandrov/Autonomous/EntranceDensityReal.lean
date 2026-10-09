module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EntranceDensityPower
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionDensitySumReal

/-! # Real density representatives and the integrated entrance estimate -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory
open scoped ENNReal

/-- The actual all-time mixture has the source real density and q-power bin estimate. -/
theorem entrance_density_sum
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (q : ℝ) (hq : 1 < q ∧ q < 3 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam)
      (c : Clock) (nu : Measure Point) [IsFiniteMeasure nu],
      (∀ᵐ e ∂nu, e.velocity 0 ∈ c.active) →
      ∃ G : Point → ℝ, Measurable G ∧ (∀ z, 0 ≤ G z) ∧
        enlargedActiveGreen hH hLE hlam hLam A c nu =
          volume.withDensity (fun z => ENNReal.ofReal (G z)) ∧
        MemLp G (ENNReal.ofReal q) volume ∧
        (∫⁻ z, ‖G z‖ₑ ^ q ∂volume) ≤ ENNReal.ofReal (C * c.r ^ (6 - 4 * q)) *
          ∑' k : ℤ, nu (entranceTimeBin c.r k) ^ q := by
  obtain ⟨C, hC, hd⟩ := entrance_density_power_sum hH hLE hlam hLam q hq
  refine ⟨C, hC, ?_⟩
  intro A c nu hfinite hnu
  have hq0 : 0 < q := by linarith [hq.1]
  let F := positionMixtureDensity hH hLE hlam hLam A c nu
  have hF := measurable_positionMixtureDensity hH hLE hlam hLam A c nu
  have hm := withDensity_positionMixtureDensity (pushforwardStatement_holds)
    hH hLE hlam hLam A c nu
  have : IsFiniteMeasure (enlargedActiveGreen hH hLE hlam hLam A c nu) :=
    enlargedActiveGreen_isFiniteMeasure hH hLE hlam hLam A c nu
  obtain ⟨hG, hG0, hGd, hGi⟩ := position_density_real volume
    (enlargedActiveGreen hH hLE hlam hLam A c nu) F hF hm q
  have hbound := hd A c nu hnu
  have hsum := entranceTimeBin_mass_rpow_sum nu c.r c.positive q hq.1.le (nu univ)
    (fun _ => measure_mono (subset_univ _))
  have hsumfinite : (∑' k : ℤ, nu (entranceTimeBin c.r k) ^ q) < ⊤ :=
    hsum.trans_lt (ENNReal.mul_lt_top (measure_lt_top _ _)
      (ENNReal.rpow_lt_top_of_nonneg (by linarith [hq.1]) (measure_ne_top _ _)))
  have hi : (∫⁻ z, ‖(F z).toReal‖ₑ ^ q ∂volume) < ⊤ := by
    rw [hGi]
    exact hbound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hsumfinite)
  refine ⟨fun z => (F z).toReal, hG, hG0, hGd, ?_, ?_⟩
  · change eLpNorm (fun z => (F z).toReal) (ENNReal.ofReal q) volume < ⊤
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (ne_of_gt (ENNReal.ofReal_pos.mpr hq0)) ENNReal.ofReal_ne_top
      hG.aestronglyMeasurable, ENNReal.toReal_ofReal hq0.le]
    exact ENNReal.rpow_lt_top_of_nonneg (one_div_nonneg.mpr hq0.le) hi.ne
  · rwa [hGi]

/-- Total and short-window starting masses yield the exact source integrated norm scaling. -/
theorem entrance_density_from_counts
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (q : ℝ) (hq : 1 < q ∧ q < 3 / 2) (B M : ℝ) (hB : 0 < B) (hM : 0 < M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock)
      (nu : Measure Point) [IsFiniteMeasure nu] (b : ℝ), 0 ≤ b →
      (∀ᵐ e ∂nu, e.velocity 0 ∈ c.active) →
      nu univ ≤ ENNReal.ofReal (B * b) →
      (∀ k : ℤ, nu (entranceTimeBin c.r k) ≤ ENNReal.ofReal M) →
      ∃ G : Point → ℝ, Measurable G ∧ (∀ z, 0 ≤ G z) ∧
        enlargedActiveGreen hH hLE hlam hLam A c nu =
          volume.withDensity (fun z => ENNReal.ofReal (G z)) ∧
        MemLp G (ENNReal.ofReal q) volume ∧
        (eLpNorm G (ENNReal.ofReal q) volume).toReal ≤
          C * c.r ^ (6 / q - 4) * b ^ (1 / q) := by
  obtain ⟨D, hD, hd⟩ := entrance_density_sum hH hLE hlam hLam q hq
  let C := (D * B * M ^ (q - 1)) ^ (1 / q)
  have hbase : 0 < D * B * M ^ (q - 1) :=
    mul_pos (mul_pos hD hB) (Real.rpow_pos_of_pos hM _)
  refine ⟨C, Real.rpow_pos_of_pos hbase _, ?_⟩
  intro A c nu hfinite b hb hnu htotal hshort
  obtain ⟨G, hGm, hG0, hGd, hGp, hGi⟩ := hd A c nu hnu
  have hq0 : 0 < q := by linarith [hq.1]
  have hsum := entranceTimeBin_mass_rpow_sum nu c.r c.positive q hq.1.le _ hshort
  have hp : (∫⁻ z, ‖G z‖ₑ ^ q ∂volume) ≤
      ENNReal.ofReal (D * c.r ^ (6 - 4 * q) * (B * b) * M ^ (q - 1)) := by
    calc
      _ ≤ ENNReal.ofReal (D * c.r ^ (6 - 4 * q)) *
          (nu univ * ENNReal.ofReal M ^ (q - 1)) := by
        exact hGi.trans (mul_le_mul_right hsum _)
      _ ≤ ENNReal.ofReal (D * c.r ^ (6 - 4 * q)) *
          (ENNReal.ofReal (B * b) * ENNReal.ofReal M ^ (q - 1)) := by gcongr
      _ = _ := by
        rw [ENNReal.ofReal_rpow_of_pos hM, ← mul_assoc,
          ← ENNReal.ofReal_mul (mul_nonneg hD.le (Real.rpow_nonneg c.positive.le _)),
          ← ENNReal.ofReal_mul (mul_nonneg
            (mul_nonneg hD.le (Real.rpow_nonneg c.positive.le _)) (mul_nonneg hB.le hb))]
  have hn : eLpNorm G (ENNReal.ofReal q) volume ≤
      ENNReal.ofReal (C * c.r ^ (6 / q - 4) * b ^ (1 / q)) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (ne_of_gt (ENNReal.ofReal_pos.mpr hq0)) ENNReal.ofReal_ne_top
      hGm.aestronglyMeasurable, ENNReal.toReal_ofReal hq0.le]
    apply (ENNReal.rpow_le_rpow hp (one_div_nonneg.mpr hq0.le)).trans_eq
    rw [ENNReal.ofReal_rpow_of_nonneg
      (mul_nonneg (mul_nonneg
        (mul_nonneg hD.le (Real.rpow_nonneg c.positive.le _)) (mul_nonneg hB.le hb))
          (Real.rpow_nonneg hM.le _)) (one_div_nonneg.mpr hq0.le)]
    congr 1
    have he : D * c.r ^ (6 - 4 * q) * (B * b) * M ^ (q - 1) =
        (D * B * M ^ (q - 1)) * c.r ^ (6 - 4 * q) * b := by ring
    rw [he, Real.mul_rpow (mul_nonneg hbase.le (Real.rpow_nonneg c.positive.le _)) hb,
      Real.mul_rpow hbase.le (Real.rpow_nonneg c.positive.le _),
      ← Real.rpow_mul c.positive.le]
    have hex : (6 - 4 * q) * (1 / q) = 6 / q - 4 := by field_simp
    rw [hex]
  refine ⟨G, hGm, hG0, hGd, hGp, ?_⟩
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hn).trans_eq
    (ENNReal.toReal_ofReal (mul_nonneg
      (mul_nonneg (Real.rpow_nonneg hbase.le _) (Real.rpow_nonneg c.positive.le _))
        (Real.rpow_nonneg hb _)))

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
