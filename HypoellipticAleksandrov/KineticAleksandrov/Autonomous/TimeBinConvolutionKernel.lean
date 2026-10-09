module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TimeBinConvolutionMass
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionOverlapRestriction
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TailRestartDensity
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockPushforward

/-! # One-index time-bin localization of the canonical active density -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory Filter
open scoped ENNReal

/-- The observation bin includes every position and the entire active velocity interval. -/
def entranceOutputBin (c : Clock) (j : ℤ) : Set Point :=
  entranceTimeBin c.r j ∩ {p | p.velocity 0 ∈ c.active}

/-- Full-position observation bins are Borel. -/
theorem measurableSet_entranceOutputBin (c : Clock) (j : ℤ) :
    MeasurableSet (entranceOutputBin c j) :=
  (measurableSet_entranceTimeBin c.r j).inter
    (isOpen_Ioo.measurableSet.preimage
      ((continuous_apply 0).comp continuous_velocity).measurable)

/-- The canonical positive pole density retains its exact strict future support. -/
theorem timeActiveDensity_support (hpush : PushforwardStatement)
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) (he : e.velocity 0 ∈ c.active) :
    ∀ᵐ z ∂(volume : Measure Point),
      positionActiveDensity hH hLE hlam hLam A c e z ≠ 0 →
        e.time < z.time ∧ z.velocity 0 ∈ c.active := by
  have hm : Measurable (positionActiveDensity hH hLE hlam hLam A c e) :=
    (measurable_positionActiveDensity hH hLE hlam hLam A c).comp
    (measurable_const.prodMk measurable_id)
  apply (ae_withDensity_iff hm).mp
  rw [withDensity_positionActiveDensity hpush hH hLE hlam hLam,
    enlargedActiveGreenKernel_apply hH hLE hlam hLam A c e he]
  obtain ⟨_, _, hd⟩ := (hpush hH hLE lam Lam hlam hLam).2 (5 / 4) (by norm_num)
  obtain ⟨G, _, _, hG, _, _⟩ := hd A c e he
  have hS : MeasurableSet (densityClockStrip c e) :=
    (continuous_time.measurable measurableSet_Ioi).inter
      (isOpen_Ioo.measurableSet.preimage
        ((continuous_apply 0).comp continuous_velocity).measurable)
  rw [hG]
  exact (ae_restrict_mem hS).filter_mono (withDensity_absolutelyContinuous _ _).ae_le

/-- Source and output bins determine the nonnegative elapsed restart delay. -/
def entranceBinDelay (j k : ℤ) : ℝ := max ((j : ℝ) - (k : ℝ) - 1) 0

/-- A valid pole obeys its exponential tail on a whole-position output bin. -/
theorem timeActiveDensity_output_tail (hpush : PushforwardStatement)
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) (j k : ℤ)
    (he : e ∈ entranceTimeBin c.r k) (hv : e.velocity 0 ∈ c.active)
    (q : ℝ) (hq : 0 < q) (K : ℝ≥0∞)
    (htail : positionPositiveNorm
      (volume.restrict {z | e.time + entranceBinDelay j k * c.r ^ 2 ≤ z.time ∧
        z.velocity 0 ∈ c.active}) q
      (positionActiveDensity hH hLE hlam hLam A c e) ≤ K) :
    positionPositiveNorm (volume.restrict (entranceOutputBin c j)) q
      (positionActiveDensity hH hLE hlam hLam A c e) ≤ K := by
  apply LE.le.trans _ htail
  apply positionPositiveNorm_restrict_le volume _ q hq _ _
    (measurableSet_entranceOutputBin c j)
    ((continuous_time.measurable measurableSet_Ici).inter
      (isOpen_Ioo.measurableSet.preimage
        ((continuous_apply 0).comp continuous_velocity).measurable))
  filter_upwards [timeActiveDensity_support hpush hH hLE hlam hLam A c e hv]
    with z hz hcell hnonzero
  have hs := hz hnonzero
  refine ⟨?_, hs.2⟩
  have heup := he.2
  have hzlo := hcell.1.1
  unfold entranceBinDelay
  by_cases h : 0 ≤ (j : ℝ) - (k : ℝ) - 1
  · rw [max_eq_left h]
    calc
      _ ≤ ((k : ℝ) + 1) * c.r ^ 2 + ((j : ℝ) - (k : ℝ) - 1) * c.r ^ 2 :=
        add_le_add heup le_rfl
      _ = (j : ℝ) * c.r ^ 2 := by ring
      _ ≤ z.time := hzlo.le
  · rw [max_eq_right (le_of_not_ge h), zero_mul, add_zero]
    exact hs.1.le

/-- Later starting bins cannot contribute to an earlier output bin. -/
theorem timeActiveDensity_output_zero (hpush : PushforwardStatement)
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) (j k : ℤ)
    (he : e ∈ entranceTimeBin c.r k) (hv : e.velocity 0 ∈ c.active) (hjk : j < k) :
    ∀ᵐ z ∂volume.restrict (entranceOutputBin c j),
      positionActiveDensity hH hLE hlam hLam A c e z = 0 := by
  filter_upwards [ae_restrict_of_ae
    (timeActiveDensity_support hpush hH hLE hlam hLam A c e hv),
    ae_restrict_mem (measurableSet_entranceOutputBin c j)] with z hz hcell
  by_contra hn
  have hs := (hz hn).1
  have hcast : (j : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hjk
  have hh := mul_le_mul_of_nonneg_right hcast (sq_nonneg c.r)
  have helo := he.1
  have hzup := hcell.1.2
  linarith

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
