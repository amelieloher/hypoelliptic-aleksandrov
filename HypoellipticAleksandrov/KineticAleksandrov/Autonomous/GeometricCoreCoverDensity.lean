module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GeometricCoreCoverSeries
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonGeometry
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoundedSourceLimitsInfinite
import Mathlib.Tactic

/-! # Improved density in cylinders whose velocities meet the region near zero -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open scoped ENNReal

/-- The source geometric-cover density theorem from the band estimate and zero capacity. -/
theorem below_four_near_velocity_density (hband : BelowFourBandStatement)
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) (alpha q : ℝ)
    (ha : bellmanAdjointExponent (Lam / lam) ((le_div_iff₀ hlam).2
      (by simpa only [one_mul] using hLam)) - 2 < alpha ∧ alpha < 1)
    (hq : 1 < q ∧ q < (4 - (1 - alpha)) / (3 - (1 - alpha))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam)
      (Z₀ : Point) (R : ℝ) (hR : 0 < R) (P : Point)
      (hP : P ∈ forwardCylinder Z₀ R hR),
      |Z₀.velocity 0| ≤ 8 * R →
      ∃ G : Point → ℝ, Measurable G ∧ (∀ z, 0 ≤ G z) ∧
        (stripGreen hH hLE hlam hLam A (capacityCylinderInterval Z₀ R hR)
          (Z₀.time + R ^ 2) (capacityCylinderPole Z₀ P R hR hP)).restrict
            (forwardCylinder Z₀ R hR) =
          (volume.restrict (forwardCylinder Z₀ R hR)).withDensity
            (fun z => ENNReal.ofReal (G z)) ∧
        MemLp G (ENNReal.ofReal q) (volume.restrict (forwardCylinder Z₀ R hR)) ∧
        (eLpNorm G (ENNReal.ofReal q)
          (volume.restrict (forwardCylinder Z₀ R hR))).toReal ≤ C * R ^ (6 / q - 4) := by
  have hx := belowFour_exponent_range lam Lam hlam hLam alpha q ha hq
  let delta := 4 - 3 * q + (1 - alpha) * (q - 1)
  have hd : 0 < delta := hx.2.2
  have hq0 : 0 < q := zero_lt_one.trans hq.1
  obtain ⟨C, hC, hc⟩ := hband hH hLE lam Lam hlam hLam alpha q ha ⟨hq.1, hx.2.1⟩
  let total := ∑' j, geometricBandPower delta j
  have ht : 0 < total := geometricBandPower_tsum_pos delta hd
  refine ⟨(2 * C * total) ^ (1 / q), by positivity, ?_⟩
  intro A Z₀ R hR P hP hnear
  let Q := forwardCylinder Z₀ R hR
  let D := densityObservationStrip Z₀ R hR
  let ν := stripGreen hH hLE hlam hLam A (capacityCylinderInterval Z₀ R hR)
    (Z₀.time + R ^ 2) (capacityCylinderPole Z₀ P R hR hP)
  let S : Bool × ℕ → Set Point := fun i =>
    {z | z.velocity 0 ∈ (geometricCoreClock R hR i.2 i.1).core}
  have hS (i : Bool × ℕ) : MeasurableSet (S i) :=
    (isClosed_Icc.preimage ((continuous_apply 0).comp continuous_velocity)).measurableSet
  have hQ : MeasurableSet Q := (isOpen_forwardCylinder Z₀ R hR).measurableSet
  have hQD : Q ⊆ D := cylinder_subset_density_strip Z₀ R hR
  have hmeasure : volume.restrict Q ≤ volume.restrict D := Measure.restrict_mono_set _ hQD
  have hlocal (i : Bool × ℕ) : ∃ f : Point → ℝ, Measurable f ∧ (∀ z, 0 ≤ f z) ∧
      ν.restrict (S i) = (volume.restrict D).withDensity (fun z => ENNReal.ofReal (f z)) ∧
      MemLp f (ENNReal.ofReal q) (volume.restrict D) ∧
      (eLpNorm f (ENNReal.ofReal q) (volume.restrict D)).toReal ≤
        (C * R ^ (6 - 4 * q) * geometricBandPower delta i.2) ^ (1 / q) := by
    have hb := hc A (geometricCoreClock R hR i.2 i.1) Z₀ R hR P hP
      (geometricCoreClock_center R hR i.2 i.1)
      (geometricCoreClock_radius R hR i.2 i.1)
    have hr : (geometricCoreClock R hR i.2 i.1).r / R = 4 * (7 / 8 : ℝ) ^ i.2 := by
      dsimp [geometricCoreClock, geometricCoreScale]
      field_simp [ne_of_gt hR]
      ring
    simpa only [hr, geometricBandPower] using hb
  choose f hfm hf0 hfd hfp hfn using hlocal
  have hle (i : Bool × ℕ) : (ν.restrict Q).restrict (S i) ≤
      (volume.restrict Q).withDensity (fun z => ENNReal.ofReal (f i z)) := by
    have he : (ν.restrict Q).restrict (S i) =
        (volume.restrict Q).withDensity (fun z => ENNReal.ofReal (f i z)) := by
      rw [Measure.restrict_comm (hS i), hfd i, restrict_withDensity hQ,
        Measure.restrict_restrict hQ, inter_eq_left.mpr hQD]
    exact he.le
  have hcover : (ν.restrict Q) (⋃ i, S i)ᶜ = 0 := by
    rw [Measure.restrict_apply (MeasurableSet.iUnion hS).compl]
    apply measure_mono_null (t := {z | z.velocity 0 = 0})
    · intro z hz
      by_contra hv
      have hvQ := (capacityCylinderPole Z₀ z R hR hz.2).2.2
      have hab : |z.velocity 0| ≤ 9 * R := by
        have h := abs_le.mp hnear
        change Z₀.velocity 0 - R < z.velocity 0 ∧
          z.velocity 0 < Z₀.velocity 0 + R at hvQ
        apply abs_le.mpr
        constructor <;> linarith [h.1, h.2, hvQ.1, hvQ.2]
      obtain ⟨j, s, hs⟩ := geometricCoreClock_covers R (z.velocity 0) hR hv hab
      exact hz.1 (mem_iUnion.mpr ⟨(s, j), hs⟩)
    · exact cylinder_strip_velocity_slice_zero hH hLE hlam hLam A Z₀ P R hR hP 0
  have : IsFiniteMeasure ν := stripGreen_isFiniteMeasure hH hLE hlam hLam A
    (capacityCylinderInterval Z₀ R hR) (Z₀.time + R ^ 2)
    (capacityCylinderPole Z₀ P R hR hP)
  have := density_volume_sigmaFinite
  obtain ⟨g, hgm, hg0, hgd, hgi⟩ := density_of_countable_cover
    (volume.restrict Q) (ν.restrict Q) S hS hcover f hfm hf0 q hq0 hle
  have hi : ∫⁻ z, ‖g z‖ₑ ^ q ∂volume.restrict Q ≤
      ENNReal.ofReal (2 * C * total * R ^ (6 - 4 * q)) := by
    apply hgi.trans
    calc
      (∑' i, ∫⁻ z, ‖f i z‖ₑ ^ q ∂volume.restrict Q) ≤
          ∑' i : Bool × ℕ,
            ENNReal.ofReal (C * R ^ (6 - 4 * q) * geometricBandPower delta i.2) := by
        apply ENNReal.tsum_le_tsum
        intro i
        exact (lintegral_mono' hmeasure le_rfl).trans
          (density_power_integral_le (volume.restrict D) (f i) q
            (C * R ^ (6 - 4 * q) * geometricBandPower delta i.2) hq0
            (by unfold geometricBandPower; positivity) (hfp i) (hfn i))
      _ = _ := geometricBandPower_sum C R delta (6 - 4 * q) hC.le hR hd
  obtain ⟨hgp, hgn⟩ := density_norm_of_power_bound (volume.restrict Q) g hgm q
    (2 * C * total * R ^ (6 - 4 * q)) hq0 (by positivity) hi
  refine ⟨g, hgm, hg0, hgd, hgp, ?_⟩
  exact hgn.trans_eq (geometricBandPower_root C R delta q hC.le hR hd hq0)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
