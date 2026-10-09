module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDensity
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDensityArithmetic
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonGeometry
import Mathlib.Tactic

/-! # Preliminary cylinder density near zero velocity

A countable subcover of the closed cores supplies the same summable positive
power as the continuous logarithmic covering. No return estimate is used.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open scoped ENNReal

/-- The preliminary sixth-fifths density in cylinders near zero velocity. -/
theorem preliminary_near_density_of_entrance (hentrance : EntranceStatement)
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam)
      (Z₀ : Point) (R : ℝ) (hR : 0 < R) (P : Point)
      (hP : P ∈ forwardCylinder Z₀ R hR),
      |Z₀.velocity 0| ≤ 8 * R →
      enlargedDensityBound
        ((stripGreen hH hLE hlam hLam A (capacityCylinderInterval Z₀ R hR)
          (Z₀.time + R ^ 2) (capacityCylinderPole Z₀ P R hR hP)).restrict
            (forwardCylinder Z₀ R hR)) (forwardCylinder Z₀ R hR) (6 / 5) (C * R) := by
  obtain ⟨C, hC, hc⟩ := preliminary_core_density_of_entrance hentrance
    hH hLE lam Lam hlam hLam
  let total := ∑' j, geometricBandPower (1 / 5) j
  have ht : 0 < total := geometricBandPower_tsum_pos _ (by norm_num)
  let B := 7 * C ^ (6 / 5 : ℝ)
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨(2 * B * total) ^ (5 / 6 : ℝ), by positivity, ?_⟩
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
  have hlocal (i : Bool × ℕ) : ∃ f : Point → ℝ, Measurable f ∧ (∀ z, 0 ≤ f z) ∧
      (ν.restrict Q).restrict (S i) =
        (volume.restrict Q).withDensity (fun z => ENNReal.ofReal (f z)) ∧
      MemLp f (ENNReal.ofReal (6 / 5)) (volume.restrict Q) ∧
      (∫⁻ z, ‖f z‖ₑ ^ (6 / 5 : ℝ) ∂volume.restrict Q) ≤
        ENNReal.ofReal (B * R ^ (6 / 5 : ℝ) * geometricBandPower (1 / 5) i.2) := by
    classical
    by_cases hm : (Q ∩ S i).Nonempty
    · obtain ⟨z, hzQ, hzS⟩ := hm
      have hmeet : ((geometricCoreClock R hR i.2 i.1).core ∩
          (capacityCylinderInterval Z₀ R hR).carrier).Nonempty :=
        ⟨z.velocity 0, hzS, (capacityCylinderPole Z₀ z R hR hzQ).2.2⟩
      obtain ⟨f, ⟨hfm, hf0, hfd⟩, hfp, hfn⟩ := hc A
        (geometricCoreClock R hR i.2 i.1) Z₀ R hR P hP hmeet
      have heq : (ν.restrict Q).restrict (S i) =
          (volume.restrict Q).withDensity (fun z => ENNReal.ofReal (f z)) := by
        rw [Measure.restrict_comm (hS i), hfd, restrict_withDensity hQ,
          Measure.restrict_restrict hQ, inter_eq_left.mpr hQD]
      have hfpQ := hfp.mono_measure (Measure.restrict_mono_set volume hQD)
      have hfnQ := (ENNReal.toReal_mono hfp.ne
        (eLpNorm_mono_measure f (Measure.restrict_mono_set volume hQD))).trans hfn
      refine ⟨f, hfm, hf0, heq, hfpQ, ?_⟩
      have hi := preliminary_density_power_le (volume.restrict Q) f (6 / 5)
        (C * (geometricCoreClock R hR i.2 i.1).r *
          (1 + R / (geometricCoreClock R hR i.2 i.1).r) ^ (5 / 6 : ℝ))
        (by norm_num) (by
          have hr := (geometricCoreClock R hR i.2 i.1).positive
          positivity) hfpQ hfnQ
      have hb := preliminary_core_power_le C R (geometricCoreClock R hR i.2 i.1).r
        hC hR (geometricCoreClock R hR i.2 i.1).positive
        (geometricCoreClock_radius R hR i.2 i.1)
      have hr : (geometricCoreClock R hR i.2 i.1).r / R =
          4 * (7 / 8 : ℝ) ^ i.2 := by
        dsimp [geometricCoreClock, geometricCoreScale]
        field_simp [ne_of_gt hR]
        ring
      rw [hr] at hb
      exact hi.trans (ENNReal.ofReal_le_ofReal (by
        simpa only [B, geometricBandPower] using hb))
    · have he : Q ∩ S i = ∅ := not_nonempty_iff_eq_empty.mp hm
      refine ⟨0, measurable_const, fun _ => le_rfl, ?_, MemLp.zero, ?_⟩
      · rw [Measure.restrict_restrict (hS i), inter_comm, he, Measure.restrict_empty]
        simp only [Pi.zero_apply, ENNReal.ofReal_zero]
        change 0 = (volume.restrict Q).withDensity 0
        exact withDensity_zero.symm
      · simp only [Pi.zero_apply, enorm_zero, ENNReal.zero_rpow_of_pos (by norm_num :
          (0 : ℝ) < 6 / 5), lintegral_zero, zero_le]
  choose f hfm hf0 hfd hfp hfi using hlocal
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
    (volume.restrict Q) (ν.restrict Q) S hS hcover f hfm hf0 (6 / 5)
    (by norm_num) (fun i => (hfd i).le)
  have hi : (∫⁻ z, ‖g z‖ₑ ^ (6 / 5 : ℝ) ∂volume.restrict Q) ≤
      ENNReal.ofReal (2 * B * total * R ^ (6 / 5 : ℝ)) := by
    apply hgi.trans
    calc
      _ ≤ ∑' i : Bool × ℕ,
          ENNReal.ofReal (B * R ^ (6 / 5 : ℝ) * geometricBandPower (1 / 5) i.2) :=
        ENNReal.tsum_le_tsum hfi
      _ = _ := geometricBandPower_sum B R (1 / 5) (6 / 5) hB.le hR (by norm_num)
  obtain ⟨hgp, hgn⟩ := density_norm_of_power_bound (volume.restrict Q) g hgm
    (6 / 5) (2 * B * total * R ^ (6 / 5 : ℝ)) (by norm_num) (by positivity) hi
  refine ⟨g, ⟨hgm, hg0, hgd⟩, hgp, hgn.trans_eq ?_⟩
  rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hR.le]
  norm_num

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
