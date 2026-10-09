module

public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyBoxCoefficientBound
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyGeometry
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Tactic

/-!
# Shrinking-box recovery for parabolic Morrey affine projections

This module proves that the physical affine moment projection on arbitrary
literal forward boxes recovers a continuous value when their radii shrink and
their literal closed boxes contain the evaluation point.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

private theorem isProbabilityMeasure_parabolicNormalizedVolumeOn
    {d : Nat} {Q : Set (TimeVelocity d)}
    (hQpos : 0 < volume Q) (hQtop : volume Q < ∞) :
    IsProbabilityMeasure (parabolicNormalizedVolumeOn Q) := by
  refine ⟨?_⟩
  rw [parabolicNormalizedVolumeOn, Measure.smul_apply,
    Measure.restrict_apply_univ]
  exact ENNReal.inv_mul_cancel hQpos.ne' hQtop.ne

private theorem parabolicExponent_one_le (d : Nat) :
    (1 : ENNReal) ≤ parabolicExponent d := by
  unfold parabolicExponent
  exact le_add_of_nonneg_left bot_le

/-- The parabolic-coordinate diameter of a literal closed unit-height forward
box is at most twice its radius. -/
theorem parabolicCoordinateDist_le_two_mul_radius_of_mem_parabolicClosedBox
    {d : Nat} (t₀ : Real) (v₀ : PDE.Vec d) {r : Real} (hr : 0 < r)
    {z w : TimeVelocity d}
    (hz : z ∈ parabolicClosedBox 1 r t₀ v₀)
    (hw : w ∈ parabolicClosedBox 1 r t₀ v₀) :
    parabolicCoordinateDist z w ≤ 2 * r := by
  have hzBox : t₀ ≤ z.1 ∧ z.1 ≤ t₀ + r ^ 2 ∧ z.2 ∈ velocityClosedCube v₀ r := by
    simpa only [one_mul] using (mem_parabolicClosedBox_iff.mp hz)
  have hwBox : t₀ ≤ w.1 ∧ w.1 ≤ t₀ + r ^ 2 ∧ w.2 ∈ velocityClosedCube v₀ r := by
    simpa only [one_mul] using (mem_parabolicClosedBox_iff.mp hw)
  have htimeAbs : |z.1 - w.1| ≤ r ^ 2 := by
    rw [abs_le]
    constructor <;> linarith [hzBox.1, hzBox.2.1, hwBox.1, hwBox.2.1]
  have htime : Real.sqrt |z.1 - w.1| ≤ r := by
    rw [Real.sqrt_le_iff]
    exact ⟨hr.le, htimeAbs⟩
  have hvelocity : ‖z.2 - w.2‖ ≤ 2 * r := by
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    simp only [Pi.sub_apply, Real.norm_eq_abs]
    rw [abs_le]
    have hzi := (mem_velocityClosedCube_iff.mp hzBox.2.2) i
    have hwi := (mem_velocityClosedCube_iff.mp hwBox.2.2) i
    exact abs_le.mp (calc
      |z.2 i - w.2 i| = |(z.2 i - v₀ i) - (w.2 i - v₀ i)| := by ring_nf
      _ ≤ |z.2 i - v₀ i| + |w.2 i - v₀ i| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          (abs_sub_le (z.2 i - v₀ i) (0 : Real) (w.2 i - v₀ i))
      _ ≤ r + r := add_le_add hzi hwi
      _ = 2 * r := by ring)
  unfold parabolicCoordinateDist
  apply max_le
  · linarith
  · exact hvelocity

private theorem parabolicLpMeanNormOn_le_of_memLp_of_forall_mem_parabolicClosedBox
    {d : Nat} (t₀ : Real) (v₀ : PDE.Vec d) {r : Real} (hr : 0 < r)
    (f : TimeVelocity d → Real)
    (hf : MemLp f (parabolicExponent d)
      (parabolicNormalizedVolumeOn (parabolicBox 1 r t₀ v₀)))
    (z : TimeVelocity d) (hz : z ∈ parabolicClosedBox 1 r t₀ v₀)
    (δ : Real)
    (hbound : ∀ w : TimeVelocity d, w ∈ parabolicClosedBox 1 r t₀ v₀ →
      |f w| ≤ δ) :
    parabolicLpMeanNormOn d f (parabolicBox 1 r t₀ v₀) hf ≤ δ := by
  have hδ : 0 ≤ δ := by
    exact (abs_nonneg (f z)).trans (hbound z hz)
  let Q : Set (TimeVelocity d) := parabolicBox 1 r t₀ v₀
  let μ : Measure (TimeVelocity d) := parabolicNormalizedVolumeOn Q
  have hQpos : 0 < volume Q := by
    exact volume_parabolicMorreyBox_pos t₀ v₀ hr
  have hQtop : volume Q < ∞ := by
    exact volume_parabolicMorreyBox_lt_top t₀ v₀ hr
  letI : IsProbabilityMeasure μ :=
    isProbabilityMeasure_parabolicNormalizedVolumeOn hQpos hQtop
  have hQae : ∀ᵐ w ∂μ, w ∈ Q := by
    change ∀ᵐ w ∂((volume Q)⁻¹ • volume.restrict Q), w ∈ Q
    exact Measure.ae_smul_measure
      (ae_restrict_mem (measurableSet_parabolicBox 1 r t₀ v₀)) _
  have hae : ∀ᵐ w ∂μ, ‖f w‖ ≤ δ := by
    filter_upwards [hQae] with w hw
    have hwClosed : w ∈ parabolicClosedBox 1 r t₀ v₀ := by
      rcases mem_parabolicBox_iff.mp hw with ⟨hwLeft, hwRight, hwv⟩
      exact mem_parabolicClosedBox_iff.mpr
        ⟨hwLeft.le, hwRight.le, fun i => (hwv i).le⟩
    simpa only [Real.norm_eq_abs] using hbound w hwClosed
  have hnormμ : eLpNorm f (parabolicExponent d) μ ≤ ENNReal.ofReal δ := by
    calc
      eLpNorm f (parabolicExponent d) μ ≤
          μ univ ^ (parabolicExponent d).toReal⁻¹ * ENNReal.ofReal δ :=
        eLpNorm_le_of_ae_bound hf.aestronglyMeasurable hae
      _ = ENNReal.ofReal δ := by simp
  have hnorm : eLpNorm f (parabolicExponent d)
      (parabolicNormalizedVolumeOn (parabolicBox 1 r t₀ v₀)) ≤ ENNReal.ofReal δ := by
    simpa only [μ, Q] using hnormμ
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hnorm
  simpa only [parabolicLpMeanNormOn_eq_toReal, parabolicELpMeanNormOn,
    ENNReal.toReal_ofReal hδ] using hreal

/-- A canonical affine moment projection is bounded at a point of the literal
closed forward box by a uniform closed-box bound on an integrable input. -/
theorem abs_parabolicMorreyBoxAffineProjection_apply_le_of_memLp_of_forall_mem_parabolicClosedBox
    {d : Nat} (t₀ : Real) (v₀ : PDE.Vec d) {r : Real} (hr : 0 < r)
    (f : TimeVelocity d → Real)
    (hf : MemLp f (parabolicExponent d)
      (parabolicNormalizedVolumeOn (parabolicBox 1 r t₀ v₀)))
    (z : TimeVelocity d) (hz : z ∈ parabolicClosedBox 1 r t₀ v₀)
    (δ : Real)
    (hbound : ∀ w : TimeVelocity d, w ∈ parabolicClosedBox 1 r t₀ v₀ →
      |f w| ≤ δ) :
    |parabolicMorreyBoxAffineProjection t₀ v₀ r f z| ≤
      (1 + 3 * (d : Real)) * δ := by
  have hmean := parabolicLpMeanNormOn_le_of_memLp_of_forall_mem_parabolicClosedBox
    t₀ v₀ hr f hf z hz δ hbound
  have hcoeff := parabolicMorreyBoxCoefficientBound_le_parabolicLpMeanNormOn
    t₀ v₀ hr f hf
  have hzVelocity : ∀ i : Fin d, |z.2 i - v₀ i| ≤ r := by
    exact mem_velocityClosedCube_iff.mp (mem_parabolicClosedBox_iff.mp hz).2.2
  have hsum : |∑ i : Fin d, parabolicMorreyBoxVelocitySlope t₀ v₀ r f i *
      (z.2 i - v₀ i)| ≤
      r * ∑ i : Fin d, |parabolicMorreyBoxVelocitySlope t₀ v₀ r f i| := by
    calc
      |∑ i : Fin d, parabolicMorreyBoxVelocitySlope t₀ v₀ r f i *
          (z.2 i - v₀ i)| ≤
          ∑ i : Fin d, |parabolicMorreyBoxVelocitySlope t₀ v₀ r f i *
            (z.2 i - v₀ i)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i : Fin d, |parabolicMorreyBoxVelocitySlope t₀ v₀ r f i| *
          |z.2 i - v₀ i| := by simp_rw [abs_mul]
      _ ≤ ∑ i : Fin d, |parabolicMorreyBoxVelocitySlope t₀ v₀ r f i| * r :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (hzVelocity i) (abs_nonneg _)
      _ = r * ∑ i : Fin d, |parabolicMorreyBoxVelocitySlope t₀ v₀ r f i| := by
        rw [Finset.mul_sum]
        simp_rw [mul_comm r]
  rw [parabolicMorreyBoxAffineProjection]
  calc
    |parabolicMorreyBoxAverage t₀ v₀ r f +
        ∑ i : Fin d, parabolicMorreyBoxVelocitySlope t₀ v₀ r f i *
          (z.2 i - v₀ i)| ≤
        |parabolicMorreyBoxAverage t₀ v₀ r f| +
          r * ∑ i : Fin d, |parabolicMorreyBoxVelocitySlope t₀ v₀ r f i| :=
      (abs_add_le _ _).trans (by
        simpa only [add_comm] using
          (add_le_add_left hsum |parabolicMorreyBoxAverage t₀ v₀ r f|))
    _ ≤ (1 + 3 * (d : Real)) * parabolicLpMeanNormOn d f
        (parabolicBox 1 r t₀ v₀) hf := hcoeff
    _ ≤ (1 + 3 * (d : Real)) * δ := by
      gcongr

private theorem normalized_memLp_sub_const_of_continuous
    {d : Nat} (u : TimeVelocity d → Real) (hu : Continuous u)
    (t₀ : Real) (v₀ : PDE.Vec d) {r : Real} (hr : 0 < r) (c : Real) :
    MemLp (fun w => u w - c) (parabolicExponent d)
      (parabolicNormalizedVolumeOn (parabolicBox 1 r t₀ v₀)) := by
  have hpull : Continuous (pullbackScalar (fun w => u w - c) t₀ v₀ r) := by
    exact (hu.sub continuous_const).comp
      (contDiff_parabolicAffine t₀ v₀ r).continuous
  have hraw := Continuous.memLp_parabolicMorreyUnitBox hpull
  have hunit : MemLp (pullbackScalar (fun w => u w - c) t₀ v₀ r)
      (parabolicExponent d)
      (parabolicNormalizedVolumeOn (parabolicMorreyUnitBox d)) := by
    exact memLp_parabolicNormalizedVolumeOn_of_memLp
      (ENNReal.toReal_pos_iff.mp (volume_parabolicMorreyUnitBox_toReal_pos d)).1 hraw
  exact (memLp_parabolicNormalizedVolumeOn_parabolicBox_iff t₀ v₀ hr _).mpr hunit

private theorem parabolicMorreyBoxAffineProjection_sub_const_apply_of_continuous
    {d : Nat} (u : TimeVelocity d → Real) (hu : Continuous u)
    (t₀ : Real) (v₀ : PDE.Vec d) {r : Real} (hr : 0 < r)
    (c : Real) (z : TimeVelocity d) :
    parabolicMorreyBoxAffineProjection t₀ v₀ r (fun w => u w - c) z =
      parabolicMorreyBoxAffineProjection t₀ v₀ r u z - c := by
  obtain ⟨w, hw⟩ := parabolicAffine_surjective (t₀ := t₀) (v₀ := v₀) hr z
  rw [← hw, parabolicMorreyBoxAffineProjection_parabolicAffine t₀ v₀ hr]
  have hcontU : Continuous (pullbackScalar u t₀ v₀ r) :=
    hu.comp (contDiff_parabolicAffine t₀ v₀ r).continuous
  have hcontC : Continuous (fun _ : TimeVelocity d => -c) := continuous_const
  letI : Fact (volume (parabolicMorreyUnitBox d) < ∞) :=
    ⟨lt_top_iff_ne_top.mpr (volume_parabolicMorreyUnitBox_ne_top d)⟩
  have hU : Integrable (pullbackScalar u t₀ v₀ r)
      (volume.restrict (parabolicMorreyUnitBox d)) :=
    (Continuous.memLp_parabolicMorreyUnitBox hcontU).integrable (parabolicExponent_one_le d)
  have hC : Integrable (fun _ : TimeVelocity d => -c)
      (volume.restrict (parabolicMorreyUnitBox d)) :=
    (Continuous.memLp_parabolicMorreyUnitBox hcontC).integrable (parabolicExponent_one_le d)
  have hUV : ∀ i : Fin d, Integrable (fun y =>
      pullbackScalar u t₀ v₀ r y * y.2 i)
      (volume.restrict (parabolicMorreyUnitBox d)) := by
    intro i
    exact (Continuous.memLp_parabolicMorreyUnitBox
      (hcontU.mul ((continuous_apply i).comp continuous_snd))).integrable
      (parabolicExponent_one_le d)
  have hCV : ∀ i : Fin d, Integrable (fun y : TimeVelocity d => (-c) * y.2 i)
      (volume.restrict (parabolicMorreyUnitBox d)) := by
    intro i
    exact (Continuous.memLp_parabolicMorreyUnitBox
      (hcontC.mul ((continuous_apply i).comp continuous_snd))).integrable
      (parabolicExponent_one_le d)
  have hpull : pullbackScalar (fun y => u y - c) t₀ v₀ r =
      pullbackScalar u t₀ v₀ r + fun _ => -c := by
    funext y
    simp only [pullbackScalar_apply, Pi.add_apply]
    ring
  rw [hpull, parabolicMorreyUnitAffineProjection_add _ _ hU hC hUV hCV]
  have hconstant : parabolicMorreyUnitAffineProjection (fun _ : TimeVelocity d => -c) w =
      -c := by
    simpa using congrFun
      (parabolicMorreyUnitAffineProjection_reproduces_velocity_affine (-c) 0) w
  rw [parabolicMorreyBoxAffineProjection_parabolicAffine t₀ v₀ hr]
  simp only [Pi.add_apply]
  rw [hconstant]
  ring

/-- Uniform closed-forward-box oscillation controls the error of the canonical
affine projection at a closed-box point. -/
theorem
  abs_parabolicMorreyBoxAffineProjection_sub_apply_le_of_continuous_of_forall_mem_parabolicClosedBox
    {d : Nat} (u : TimeVelocity d → Real) (hu : Continuous u)
    (z : TimeVelocity d) (t₀ : Real) (v₀ : PDE.Vec d) {r : Real}
    (hr : 0 < r) (hz : z ∈ parabolicClosedBox 1 r t₀ v₀)
    (δ : Real)
    (hbound : ∀ w : TimeVelocity d, w ∈ parabolicClosedBox 1 r t₀ v₀ →
      |u w - u z| ≤ δ) :
    |parabolicMorreyBoxAffineProjection t₀ v₀ r u z - u z| ≤
      (1 + 3 * (d : Real)) * δ := by
  let f : TimeVelocity d → Real := fun w => u w - u z
  have hf := normalized_memLp_sub_const_of_continuous u hu t₀ v₀ hr (u z)
  have hcore :=
    abs_parabolicMorreyBoxAffineProjection_apply_le_of_memLp_of_forall_mem_parabolicClosedBox
      t₀ v₀ hr f hf z hz δ hbound
  rw [parabolicMorreyBoxAffineProjection_sub_const_apply_of_continuous
    u hu t₀ v₀ hr (u z) z] at hcore
  exact hcore

private theorem dist_lt_of_mem_parabolicClosedBox_of_two_mul_radius_lt
    {d : Nat} (t₀ : Real) (v₀ : PDE.Vec d) {r η : Real}
    (hr : 0 < r) (hrsmall : r ≤ 1 / 2)
    {z w : TimeVelocity d}
    (hz : z ∈ parabolicClosedBox 1 r t₀ v₀)
    (hw : w ∈ parabolicClosedBox 1 r t₀ v₀)
    (hsmall : 2 * r < η) :
    dist w z < η := by
  have hcoord := parabolicCoordinateDist_le_two_mul_radius_of_mem_parabolicClosedBox
    t₀ v₀ hr hz hw
  have htimeRoot : Real.sqrt |z.1 - w.1| ≤ 2 * r :=
    (le_max_left _ _).trans hcoord
  have htimeSq : |z.1 - w.1| ≤ (2 * r) ^ 2 := by
    have hnonneg : 0 ≤ 2 * r := by positivity
    have hsquare := (sq_le_sq₀ (Real.sqrt_nonneg _) hnonneg).mpr htimeRoot
    rwa [Real.sq_sqrt (abs_nonneg _)] at hsquare
  have htwo : 2 * r ≤ 1 := by linarith
  have htime : |w.1 - z.1| ≤ 2 * r := by
    rw [abs_sub_comm]
    calc
      |z.1 - w.1| ≤ (2 * r) ^ 2 := htimeSq
      _ ≤ 2 * r := by nlinarith
  have hvelocity : ‖w.2 - z.2‖ ≤ 2 * r := by
    rw [norm_sub_rev]
    exact (le_max_right _ _).trans hcoord
  rw [Prod.dist_eq]
  apply max_lt
  · simpa only [Real.dist_eq] using htime.trans_lt hsmall
  · exact hvelocity.trans_lt hsmall

/-- Canonical affine moment projections on literal forward boxes shrinking to
a point recover a continuous function at that point. -/
theorem tendsto_parabolicMorreyBoxAffineProjection_apply_of_continuous
    {d : Nat} (u : TimeVelocity d → Real) (hu : Continuous u)
    (z : TimeVelocity d) (t : Nat → Real) (v : Nat → PDE.Vec d)
    (r : Nat → Real) (hr : ∀ n : Nat, 0 < r n)
    (hz : ∀ n : Nat, z ∈ parabolicClosedBox 1 (r n) (t n) (v n))
    (hr0 : Tendsto r atTop (nhds 0)) :
    Tendsto
      (fun n => parabolicMorreyBoxAffineProjection (t n) (v n) (r n) u z)
      atTop (nhds (u z)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hCpos : 0 < 1 + 3 * (d : Real) := by positivity
  obtain ⟨η, hηpos, hη⟩ := (Metric.continuousAt_iff.mp hu.continuousAt)
    (ε / (2 * (1 + 3 * (d : Real)))) (div_pos hε (mul_pos (by norm_num) hCpos))
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hr0) (min (η / 2) (1 / 2))
    (lt_min (half_pos hηpos) (by norm_num))
  refine ⟨N, fun n hn => ?_⟩
  have hnsmall : dist (r n) 0 < min (η / 2) (1 / 2) := hN n hn
  have hnr : r n ≤ 1 / 2 := by
    have : r n < 1 / 2 := by
      simpa only [Real.dist_eq, sub_zero, abs_of_pos (hr n)] using
        hnsmall.trans_le (min_le_right _ _)
    exact this.le
  have hnη : 2 * r n < η := by
    have hlt : r n < η / 2 := by
      simpa only [Real.dist_eq, sub_zero, abs_of_pos (hr n)] using
        hnsmall.trans_le (min_le_left _ _)
    nlinarith [hηpos]
  have hosc : ∀ w : TimeVelocity d,
      w ∈ parabolicClosedBox 1 (r n) (t n) (v n) →
      |u w - u z| ≤ ε / (2 * (1 + 3 * (d : Real))) := by
    intro w hw
    have hdist := dist_lt_of_mem_parabolicClosedBox_of_two_mul_radius_lt
      (t n) (v n) (hr n) hnr (hz n) hw hnη
    have hvalue := hη hdist
    simpa only [Real.dist_eq] using hvalue.le
  have hprojection :=
  abs_parabolicMorreyBoxAffineProjection_sub_apply_le_of_continuous_of_forall_mem_parabolicClosedBox
      u hu z (t n) (v n) (hr n) (hz n)
      (ε / (2 * (1 + 3 * (d : Real)))) hosc
  rw [Real.dist_eq]
  calc
    |parabolicMorreyBoxAffineProjection (t n) (v n) (r n) u z - u z| ≤
        (1 + 3 * (d : Real)) * (ε / (2 * (1 + 3 * (d : Real)))) := hprojection
    _ = ε / 2 := by field_simp [hCpos.ne']
    _ < ε := half_lt_self hε

/-- Smooth shrinking-box recovery, as the direct `ContDiff` specialization. -/
theorem tendsto_parabolicMorreyBoxAffineProjection_apply_of_contDiff
    {d : Nat} (u : TimeVelocity d → Real) (hu : ContDiff Real 2 u)
    (z : TimeVelocity d) (t : Nat → Real) (v : Nat → PDE.Vec d)
    (r : Nat → Real) (hr : ∀ n : Nat, 0 < r n)
    (hz : ∀ n : Nat, z ∈ parabolicClosedBox 1 (r n) (t n) (v n))
    (hr0 : Tendsto r atTop (nhds 0)) :
    Tendsto
      (fun n => parabolicMorreyBoxAffineProjection (t n) (v n) (r n) u z)
      atTop (nhds (u z)) := by
  exact tendsto_parabolicMorreyBoxAffineProjection_apply_of_continuous
    u hu.continuous z t v r hr hz hr0

end HypoellipticAleksandrov.Parabolic
