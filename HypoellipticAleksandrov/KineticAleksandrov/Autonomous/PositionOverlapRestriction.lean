module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionOverlapSupport

/-! # Localized positive norms with actual support and restarted tails -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory Filter
open scoped ENNReal

/-- Support inside a larger observation set transfers the positive Lq norm bound. -/
theorem positionPositiveNorm_restrict_le {X : Type*} [MeasurableSpace X]
    (m : Measure X) (F : X → ℝ≥0∞) (q : ℝ) (hq : 0 < q)
    (E T : Set X) (hE : MeasurableSet E) (hT : MeasurableSet T)
    (hs : ∀ᵐ x ∂m, x ∈ E → F x ≠ 0 → x ∈ T) :
    positionPositiveNorm (m.restrict E) q F ≤ positionPositiveNorm (m.restrict T) q F := by
  unfold positionPositiveNorm
  apply ENNReal.rpow_le_rpow _ (one_div_nonneg.mpr hq.le)
  rw [← lintegral_indicator hE, ← lintegral_indicator hT]
  apply lintegral_mono_ae
  filter_upwards [hs] with x hx
  by_cases he : x ∈ E
  · rw [indicator_of_mem he]
    by_cases hf : F x = 0
    · rw [hf, ENNReal.zero_rpow_of_pos hq]
      exact zero_le
    · rw [indicator_of_mem (hx he hf)]
  · rw [indicator_of_notMem he]
    exact zero_le

/-- The elapsed tail used on output bin `i` after source bin `j`. -/
def positionOverlapDelay (i j : ℕ) : ℝ := max ((i : ℝ) - (j : ℝ) - 1) 0

/-- Strict future support converts the grid delay to an elapsed-time lower bound. -/
theorem positionOverlapDelay_le (c : Clock) (s x : ℝ) (j i : ℕ) (k ell : ℤ)
    (e z : Point) (he : e ∈ enlargedStartCell c s x j k)
    (hz : z ∈ enlargedStartCell c s x i ell) (ht : e.time < z.time) :
    e.time + positionOverlapDelay i j * c.r ^ 2 ≤ z.time := by
  unfold positionOverlapDelay
  by_cases h : 0 ≤ (i : ℝ) - (j : ℝ) - 1
  · rw [max_eq_left h]
    have heup := (enlargedTimeBin_bounds c.r s e.time j he.1).2
    have hzlo := (enlargedTimeBin_bounds c.r s z.time i hz.1).1
    nlinarith only [heup, hzlo]
  · rw [max_eq_right (le_of_not_ge h), zero_mul, add_zero]
    exact ht.le

/-- A source pole obeys the restarted-tail norm bound on any output cell. -/
theorem positionActiveDensity_output_tail (hpush : PushforwardStatement)
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (hc : |c.vbar| = 2 * c.r)
    (s x : ℝ) (j i : ℕ) (k ell : ℤ) (e : Point)
    (he : e ∈ enlargedStartCell c s x j k) (hv : e.velocity 0 ∈ c.active)
    (q : ℝ) (hq : 0 < q) (K : ℝ≥0∞)
    (htail : positionPositiveNorm
      (volume.restrict {z | e.time + positionOverlapDelay i j * c.r ^ 2 ≤ z.time ∧
        z.velocity 0 ∈ c.active}) q
      (positionActiveDensity hH hLE hlam hLam A c e) ≤ K) :
    positionPositiveNorm (volume.restrict (enlargedOutputCell c s x i ell)) q
      (positionActiveDensity hH hLE hlam hLam A c e) ≤ K := by
  apply LE.le.trans _ htail
  apply positionPositiveNorm_restrict_le volume _ q hq _ _
    (measurableSet_enlargedOutputCell c s x i ell)
    ((isClosed_le continuous_const continuous_time).measurableSet.inter
      (isOpen_Ioo.measurableSet.preimage
        ((continuous_apply 0).comp continuous_velocity).measurable))
  filter_upwards [positionActiveDensity_support hpush hH hLE hlam hLam A c hc e hv]
    with z hz hcell hnonzero
  have hs := hz hnonzero
  exact ⟨positionOverlapDelay_le c s x j i k ell e z he hcell.1 hs.1, hs.2.1⟩

/-- Cells outside the finite-speed overlap region receive no density contribution. -/
theorem positionActiveDensity_output_zero (hpush : PushforwardStatement)
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (hc : |c.vbar| = 2 * c.r)
    (s x : ℝ) (j i : ℕ) (k ell : ℤ) (e : Point)
    (he : e ∈ enlargedStartCell c s x j k) (hv : e.velocity 0 ∈ c.active)
    (hno : ¬(j ≤ i ∧ |((ell - k : ℤ) : ℝ)| ≤ 5 * ((i : ℝ) - (j : ℝ) + 1))) :
    ∀ᵐ z ∂volume.restrict (enlargedOutputCell c s x i ell),
      positionActiveDensity hH hLE hlam hLam A c e z = 0 := by
  filter_upwards [ae_restrict_of_ae
    (positionActiveDensity_support hpush hH hLE hlam hLam A c hc e hv),
    ae_restrict_mem (measurableSet_enlargedOutputCell c s x i ell)] with z hz hcell
  by_contra hnonzero
  have hs := hz hnonzero
  apply hno
  exact ⟨positionOverlap_time_index c s x j i k ell e z he hcell.1 hs.1,
    positionOverlap_position_index c s x j i k ell e z he hcell.1 hs.1 hs.2.2⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
