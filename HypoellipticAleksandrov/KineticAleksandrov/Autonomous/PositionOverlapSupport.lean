module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionOverlapBounds
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionOverlapGeometry

/-! # Canonical positive densities retain the actual physical finite-speed support -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory Filter
open scoped ENNReal

/-- The source centred active interval has speed bounded by `3r`. -/
theorem positionActive_speed (c : Clock) (hc : |c.vbar| = 2 * c.r) :
    max |c.activeInterval.lo| |c.activeInterval.hi| ≤ 3 * c.r := by
  apply max_le
  · have h := abs_sub c.vbar (3 * c.r / 4)
    rw [hc, abs_of_nonneg (by linarith [c.positive] : 0 ≤ 3 * c.r / 4)] at h
    change |c.vbar - 3 * c.r / 4| ≤ 3 * c.r
    linarith only [h, c.positive]
  · have h := abs_add_le c.vbar (3 * c.r / 4)
    rw [hc, abs_of_nonneg (by linarith [c.positive] : 0 ≤ 3 * c.r / 4)] at h
    change |c.vbar + 3 * c.r / 4| ≤ 3 * c.r
    linarith only [h, c.positive]

/-- Every nonzero canonical active density value lies in its strict future finite-speed cone. -/
theorem positionActiveDensity_support (hpush : PushforwardStatement)
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (hc : |c.vbar| = 2 * c.r)
    (e : Point) (he : e.velocity 0 ∈ c.active) :
    ∀ᵐ z ∂(volume : Measure Point),
      positionActiveDensity hH hLE hlam hLam A c e z ≠ 0 →
        e.time < z.time ∧ z.velocity 0 ∈ c.active ∧
          |z.position 0 - e.position 0| ≤ 3 * c.r * (z.time - e.time) := by
  have hm : Measurable (positionActiveDensity hH hLE hlam hLam A c e) :=
    (measurable_positionActiveDensity hH hLE hlam hLam A c).comp
      (measurable_const.prodMk measurable_id)
  apply (ae_withDensity_iff hm).mp
  rw [withDensity_positionActiveDensity hpush hH hLE hlam hLam,
    enlargedActiveGreenKernel_apply hH hLE hlam hLam A c e he]
  obtain ⟨C, _, hd⟩ := (hpush hH hLE lam Lam hlam hLam).2 (5 / 4) (by norm_num)
  obtain ⟨G, _, _, hG, _, _⟩ := hd A c e he
  have hS : MeasurableSet (densityClockStrip c e) :=
    (isOpen_lt continuous_const continuous_time).measurableSet.inter
      (isOpen_Ioo.measurableSet.preimage
        ((continuous_apply 0).comp continuous_velocity).measurable)
  have hmem : ∀ᵐ z ∂stripGreen hH hLE hlam hLam A c.activeInterval ⊤
      (densityClockPole c e he), z ∈ densityClockStrip c e := by
    rw [hG]
    exact (ae_restrict_mem hS).filter_mono (withDensity_absolutelyContinuous _ _).ae_le
  have hcone : ∀ᵐ z ∂stripGreen hH hLE hlam hLam A c.activeInterval ⊤
      (densityClockPole c e he),
      |z.position 0 - e.position 0| ≤
        max |c.activeInterval.lo| |c.activeInterval.hi| * (z.time - e.time) := by
    rw [ae_iff]
    simpa only [not_le, densityClockPole] using strip_cone hH hLE hlam hLam A c.activeInterval ⊤
      (densityClockPole c e he)
  filter_upwards [hmem, hcone] with z hz hcZ
  exact ⟨hz.1, hz.2, hcZ.trans
    (mul_le_mul_of_nonneg_right (positionActive_speed c hc) (sub_nonneg.mpr hz.1.le))⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
