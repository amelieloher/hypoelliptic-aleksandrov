module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2Cutoff
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2CoordinatesDifferential
import Mathlib.Tactic.FieldSimp

/-!
# Literal extension of the homogeneous cutoff profile

The position-zero branch is the radial source formula, including its zero origin value.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/-- The literal profile with the source's extension at zero position. -/
def geometricProfile {d : ℕ} (alpha C₀ sigma R : ℝ) (q : PDE.Vec d × PDE.Vec d) : ℝ :=
  if q.1 = 0 then radialProfile alpha q.2 else
    homogeneousAnsatz alpha (cutoffProfile alpha C₀ sigma R) q.1 q.2

/-- The profile vanishes at the joint origin for positive homogeneity degree. -/
theorem geometricProfile_zero (d : ℕ) (alpha C₀ sigma R : ℝ) (ha : 0 < alpha) :
    geometricProfile (d := d) alpha C₀ sigma R 0 = 0 := by
  simp [geometricProfile, radialProfile, PDE.vecNormSq, PDE.vecDot, Real.rpow_eq_pow,
    Real.zero_rpow (ne_of_gt (div_pos ha (by norm_num : (0 : ℝ) < 2)))]

/-- The literal radial profile scales by the exact power alpha under positive dilation. -/
theorem radialProfile_smul {d : ℕ} (alpha r : ℝ) (hr : 0 < r) (v : PDE.Vec d) :
    radialProfile alpha (r • v) = Real.rpow r alpha * radialProfile alpha v := by
  unfold radialProfile
  rw [PDE.vecNormSq_smul]
  simp only [Real.rpow_eq_pow]
  rw [Real.mul_rpow (sq_nonneg r) (PDE.vecNormSq_nonneg v),
    ← Real.rpow_natCast_mul hr.le]
  norm_num only [Nat.cast_ofNat]
  congr 2
  ring

/-- The extended profile has exact kinetic homogeneity, including both axes. -/
theorem geometricProfile_homogeneous {d : ℕ} (alpha C₀ sigma R r : ℝ) (hr : 0 < r)
    (q : PDE.Vec d × PDE.Vec d) :
    geometricProfile alpha C₀ sigma R (r ^ 3 • q.1, r • q.2) =
      Real.rpow r alpha * geometricProfile alpha C₀ sigma R q := by
  have hzero : r ^ 3 • q.1 = 0 ↔ q.1 = 0 :=
    smul_eq_zero_iff_right (pow_ne_zero 3 hr.ne')
  unfold geometricProfile
  by_cases hx : q.1 = 0
  · simp only [hx, smul_zero, ite_true]
    exact radialProfile_smul alpha r hr q.2
  · simp only [hx, hzero.not.mpr hx, ite_false]
    exact homogeneousAnsatz_dilate alpha r hr _ q.1 q.2

/-- The extended profile is positive at every nonzero kinetic point. -/
theorem geometricProfile_pos {d : ℕ} (alpha C₀ sigma R : ℝ)
    (hC₀ : 0 ≤ C₀) (hsigma : 0 < sigma) (hR : 0 < R)
    (q : PDE.Vec d × PDE.Vec d) (hq : q ≠ 0) :
    0 < geometricProfile alpha C₀ sigma R q := by
  unfold geometricProfile
  split_ifs with hx
  · apply radialProfile_pos
    intro hv
    exact hq (Prod.ext hx hv)
  · apply mul_pos
    · exact Real.rpow_pos_of_pos (PDE.vecEuclideanNorm_pos_iff.mpr hx) _
    · exact cutoffProfile_pos alpha C₀ sigma R hC₀ hsigma hR _ _

/-- Exterior interpolation cancels all position dependence of the ansatz exactly. -/
theorem homogeneousAnsatz_eq_radial {d : ℕ} (alpha C₀ sigma R : ℝ) (hR : 0 < R)
    (x v : PDE.Vec d) (hx : x ≠ 0)
    (hout : 2 * R ≤ PDE.vecEuclideanNorm (normalizedVelocity x v)) :
    homogeneousAnsatz alpha (cutoffProfile alpha C₀ sigma R) x v = radialProfile alpha v := by
  have hr : 0 < PDE.vecEuclideanNorm x := PDE.vecEuclideanNorm_pos_iff.mpr hx
  unfold homogeneousAnsatz
  rw [cutoffProfile_eq_radial alpha C₀ sigma R hR _ _ hout]
  unfold radialProfile normalizedVelocity
  rw [PDE.vecNormSq_smul]
  simp only [Real.rpow_eq_pow]
  rw [Real.mul_rpow (sq_nonneg _) (PDE.vecNormSq_nonneg v),
    ← Real.rpow_natCast_mul (Real.rpow_nonneg hr.le _), ← Real.rpow_mul hr.le]
  norm_num only [Nat.cast_ofNat]
  rw [← mul_assoc, ← Real.rpow_add hr]
  have he : alpha / 3 + (-(1 / 3 : ℝ) * (2 * (alpha / 2))) = 0 := by ring
  rw [he, Real.rpow_zero, one_mul]

/-- The physical outer-region condition forces exact radial agreement. -/
theorem geometricProfile_eq_radial_of_outer {d : ℕ} (alpha C₀ sigma R : ℝ) (hR : 0 < R)
    (q : PDE.Vec d × PDE.Vec d)
    (hout : 2 * R * Real.rpow (PDE.vecEuclideanNorm q.1) (1 / 3) ≤
      PDE.vecEuclideanNorm q.2) :
    geometricProfile alpha C₀ sigma R q = radialProfile alpha q.2 := by
  by_cases hx : q.1 = 0
  · simp [geometricProfile, hx]
  · rw [geometricProfile, ite_eq_right hx]
    apply homogeneousAnsatz_eq_radial alpha C₀ sigma R hR q.1 q.2 hx
    have hr : 0 < PDE.vecEuclideanNorm q.1 := PDE.vecEuclideanNorm_pos_iff.mpr hx
    have hp : 0 < Real.rpow (PDE.vecEuclideanNorm q.1) (1 / 3) :=
      Real.rpow_pos_of_pos hr _
    unfold normalizedVelocity
    simp only [Real.rpow_eq_pow] at hp hout ⊢
    rw [PDE.vecEuclideanNorm_smul,
      abs_of_pos (Real.rpow_pos_of_pos hr (-(1 / 3 : ℝ)))]
    rw [Real.rpow_neg hr.le]
    have hh := (le_div_iff₀ hp).mpr hout
    simpa only [div_eq_mul_inv, mul_comm] using hh

/-- The ansatz of the actual smooth cutoff is smooth at every nonzero position. -/
theorem contDiffAt_cutoffAnsatz {d : ℕ} (alpha C₀ sigma R : ℝ)
    (hsigma : 0 < sigma) (hR : 0 < R) (q : PDE.Vec d × PDE.Vec d) (hx : q.1 ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun z : PDE.Vec d × PDE.Vec d =>
        homogeneousAnsatz alpha (cutoffProfile alpha C₀ sigma R) z.1 z.2) q := by
  have hbase := PDE.vecNormSq_eq_zero_iff.not.mpr hx
  have hnorm := PDE.vecEuclideanNorm_eq_zero_iff.not.mpr hx
  have hr : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun z : PDE.Vec d × PDE.Vec d => PDE.vecEuclideanNorm z.1) q :=
    (PDE.contDiff_vecNormSq.comp contDiff_fst).contDiffAt.sqrt hbase
  have he : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun z : PDE.Vec d × PDE.Vec d => positionDirection z.1) q :=
    (hr.inv hnorm).smul contDiffAt_fst
  have hy : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun z : PDE.Vec d × PDE.Vec d => normalizedVelocity z.1 z.2) q :=
    (hr.rpow_const_of_ne (p := -(1 / 3 : ℝ)) hnorm).smul contDiffAt_snd
  exact (hr.rpow_const_of_ne (p := alpha / 3) hnorm).mul
    ((contDiff_cutoffProfile alpha C₀ sigma R hsigma hR).contDiffAt.comp q (hy.prodMk he))

/-- The literal extension is smooth everywhere except the joint origin. -/
theorem geometricProfile_smooth_off_origin {d : ℕ} (alpha C₀ sigma R : ℝ)
    (hsigma : 0 < sigma) (hR : 0 < R) :
    ContDiffOn ℝ (⊤ : ℕ∞) (geometricProfile (d := d) alpha C₀ sigma R) ({0}ᶜ) := by
  intro q hq
  apply ContDiffAt.contDiffWithinAt
  by_cases hx : q.1 = 0
  · have hv : q.2 ≠ 0 := by
      intro hv
      apply hq
      exact Set.mem_singleton_iff.mpr (Prod.ext hx hv)
    have hr : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun z : PDE.Vec d × PDE.Vec d => radialProfile alpha z.2) q :=
      (PDE.contDiff_vecNormSq.comp contDiff_snd).contDiffAt.rpow_const_of_ne
        (PDE.vecNormSq_eq_zero_iff.not.mpr hv)
    have hc : Continuous (fun z : PDE.Vec d × PDE.Vec d =>
        2 * R * Real.rpow (PDE.vecEuclideanNorm z.1) (1 / 3)) := by
      apply continuous_const.mul
      exact (PDE.continuous_vecEuclideanNorm.comp continuous_fst).rpow_const
        (fun _ => Or.inr (by norm_num))
    have hopen := isOpen_lt hc (PDE.continuous_vecEuclideanNorm.comp continuous_snd)
    have hmem : q ∈ {z : PDE.Vec d × PDE.Vec d |
        2 * R * Real.rpow (PDE.vecEuclideanNorm z.1) (1 / 3) <
          PDE.vecEuclideanNorm z.2} := by
      simpa [hx, PDE.vecEuclideanNorm, PDE.vecNormSq, PDE.vecDot, Real.rpow_eq_pow]
        using PDE.vecEuclideanNorm_pos_iff.mpr hv
    apply hr.congr_of_eventuallyEq
    filter_upwards [hopen.mem_nhds hmem] with z hz
    exact geometricProfile_eq_radial_of_outer alpha C₀ sigma R hR z hz.le
  · apply (contDiffAt_cutoffAnsatz alpha C₀ sigma R hsigma hR q hx).congr_of_eventuallyEq
    filter_upwards [continuous_fst.continuousAt.eventually_ne hx] with z hz
    simp only [geometricProfile, ite_eq_right hz]

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
