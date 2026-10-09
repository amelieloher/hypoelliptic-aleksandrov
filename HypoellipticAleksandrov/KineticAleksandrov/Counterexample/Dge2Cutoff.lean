module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2Coordinates
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import PDEFoundation.Geometry.EuclideanBall.Topology
import Mathlib.Tactic.Positivity

/-!
# The literal radial interpolation in Appendix C

The scalar bump is composed with the squared Euclidean radius. Its inner and outer
levels are one and four, giving the source's radii R and 2R.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/-- Fixed smooth scalar bump for the squared radial variable. -/
def squaredRadiusBump : ContDiffBump (0 : ℝ) := ⟨1, 4, by norm_num, by norm_num⟩

/-- The radial cutoff of Appendix C, using the Euclidean squared length. -/
def radialCutoff {d : ℕ} (R : ℝ) (y : PDE.Vec d) : ℝ :=
  squaredRadiusBump (PDE.vecNormSq y / R ^ 2)

/-- The source's radial power profile. -/
def radialProfile {d : ℕ} (alpha : ℝ) (y : PDE.Vec d) : ℝ :=
  Real.rpow (PDE.vecNormSq y) (alpha / 2)

/-- The literal interpolation of the translated seed with the radial profile. -/
def cutoffProfile {d : ℕ} (alpha C₀ sigma R : ℝ) (y e : PDE.Vec d) : ℝ :=
  radialProfile alpha y + radialCutoff R y * (seed alpha C₀ sigma y e - radialProfile alpha y)

/-- The radial cutoff takes values between zero and one. -/
theorem radialCutoff_mem_Icc {d : ℕ} (R : ℝ) (y : PDE.Vec d) :
    radialCutoff R y ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨squaredRadiusBump.nonneg, squaredRadiusBump.le_one⟩

/-- The cutoff is one on the closed Euclidean ball of radius R. -/
theorem radialCutoff_eq_one {d : ℕ} (R : ℝ) (hR : 0 < R) (y : PDE.Vec d)
    (hy : PDE.vecEuclideanNorm y ≤ R) : radialCutoff R y = 1 := by
  apply squaredRadiusBump.one_of_mem_closedBall
  have hsq : PDE.vecNormSq y ≤ R ^ 2 := by
    rw [← PDE.vecEuclideanNorm_sq]
    exact pow_le_pow_left₀ (PDE.vecEuclideanNorm_nonneg y) hy 2
  have hpos : 0 < R ^ 2 := sq_pos_of_pos hR
  have hn : 0 ≤ PDE.vecNormSq y / R ^ 2 := div_nonneg (PDE.vecNormSq_nonneg y) hpos.le
  have hle : PDE.vecNormSq y / R ^ 2 ≤ 1 := (div_le_one hpos).mpr hsq
  simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_of_nonneg hn,
    squaredRadiusBump] using hle

/-- The cutoff is zero outside the open Euclidean ball of radius 2R. -/
theorem radialCutoff_eq_zero {d : ℕ} (R : ℝ) (hR : 0 < R) (y : PDE.Vec d)
    (hy : 2 * R ≤ PDE.vecEuclideanNorm y) : radialCutoff R y = 0 := by
  apply squaredRadiusBump.zero_of_le_dist
  have hsq : 4 * R ^ 2 ≤ PDE.vecNormSq y := by
    rw [← PDE.vecEuclideanNorm_sq]
    nlinarith [PDE.vecEuclideanNorm_nonneg y]
  have hpos : 0 < R ^ 2 := sq_pos_of_pos hR
  have hn : 0 ≤ PDE.vecNormSq y / R ^ 2 := div_nonneg (PDE.vecNormSq_nonneg y) hpos.le
  have hle : 4 ≤ PDE.vecNormSq y / R ^ 2 := (le_div_iff₀ hpos).mpr hsq
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hn, squaredRadiusBump] using hle

/-- The cutoff profile equals the seed on the closed inner ball. -/
theorem cutoffProfile_eq_seed {d : ℕ} (alpha C₀ sigma R : ℝ) (hR : 0 < R)
    (y e : PDE.Vec d) (hy : PDE.vecEuclideanNorm y ≤ R) :
    cutoffProfile alpha C₀ sigma R y e = seed alpha C₀ sigma y e := by
  unfold cutoffProfile
  rw [radialCutoff_eq_one R hR y hy]
  ring

/-- The cutoff profile equals the radial profile on the closed outer region. -/
theorem cutoffProfile_eq_radial {d : ℕ} (alpha C₀ sigma R : ℝ) (hR : 0 < R)
    (y e : PDE.Vec d) (hy : 2 * R ≤ PDE.vecEuclideanNorm y) :
    cutoffProfile alpha C₀ sigma R y e = radialProfile alpha y := by
  unfold cutoffProfile
  rw [radialCutoff_eq_zero R hR y hy]
  ring

/-- The cutoff is smooth on the entire native velocity space. -/
theorem contDiff_radialCutoff {d : ℕ} (R : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (radialCutoff (d := d) R) := by
  unfold radialCutoff
  apply squaredRadiusBump.contDiff.comp
  unfold PDE.vecNormSq PDE.vecDot
  fun_prop

/-- The radial profile is positive away from the velocity origin. -/
theorem radialProfile_pos {d : ℕ} (alpha : ℝ) (y : PDE.Vec d) (hy : y ≠ 0) :
    0 < radialProfile alpha y := by
  apply Real.rpow_pos_of_pos
  exact (PDE.vecNormSq_nonneg y).lt_of_ne' (PDE.vecNormSq_eq_zero_iff.not.mpr hy)

/-- The interpolation is strictly positive, including at velocity zero. -/
theorem cutoffProfile_pos {d : ℕ} (alpha C₀ sigma R : ℝ) (hC₀ : 0 ≤ C₀)
    (hsigma : 0 < sigma) (hR : 0 < R) (y e : PDE.Vec d) :
    0 < cutoffProfile alpha C₀ sigma R y e := by
  by_cases hy : y = 0
  · rw [cutoffProfile_eq_seed alpha C₀ sigma R hR y e]
    · exact seed_pos alpha C₀ sigma hC₀ hsigma y e
    · simp [hy, PDE.vecEuclideanNorm, PDE.vecNormSq, PDE.vecDot, hR.le]
  · have hseed := seed_pos alpha C₀ sigma hC₀ hsigma y e
    have hrad := radialProfile_pos alpha y hy
    obtain ⟨hchi0, hchi1⟩ := radialCutoff_mem_Icc R y
    unfold cutoffProfile
    by_cases hc : radialCutoff R y = 0
    · simp [hc, hrad]
    · have hchi : 0 < radialCutoff R y := lt_of_le_of_ne hchi0 (Ne.symm hc)
      have hh := mul_pos hchi hseed
      have hr := mul_nonneg (sub_nonneg.mpr hchi1) hrad.le
      nlinarith

/-- The interpolation is smooth jointly, including where its radial summands are singular. -/
theorem contDiff_cutoffProfile {d : ℕ} (alpha C₀ sigma R : ℝ)
    (hsigma : 0 < sigma) (hR : 0 < R) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun q : PDE.Vec d × PDE.Vec d => cutoffProfile alpha C₀ sigma R q.1 q.2) := by
  apply contDiff_iff_contDiffAt.mpr
  intro q
  by_cases hy : PDE.vecEuclideanNorm q.1 < R
  · have hevent : ∀ᶠ z : PDE.Vec d × PDE.Vec d in nhds q,
        PDE.vecEuclideanNorm z.1 < R :=
      (PDE.continuous_vecEuclideanNorm.comp continuous_fst).continuousAt.eventually_lt_const hy
    apply (contDiff_seed alpha C₀ sigma hsigma).contDiffAt.congr_of_eventuallyEq
    filter_upwards [hevent] with z hz
    exact cutoffProfile_eq_seed alpha C₀ sigma R hR z.1 z.2 hz.le
  · have hnonzero : q.1 ≠ 0 := by
      intro hzero
      apply hy
      simpa [hzero, PDE.vecEuclideanNorm, PDE.vecNormSq, PDE.vecDot] using hR
    have hbase : PDE.vecNormSq q.1 ≠ 0 := PDE.vecNormSq_eq_zero_iff.not.mpr hnonzero
    have hr : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun z : PDE.Vec d × PDE.Vec d => radialProfile alpha z.1) q := by
      exact (PDE.contDiff_vecNormSq.comp contDiff_fst).contDiffAt.rpow_const_of_ne hbase
    have hc : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun z : PDE.Vec d × PDE.Vec d => radialCutoff R z.1) q :=
      ((contDiff_radialCutoff R).comp contDiff_fst).contDiffAt
    exact hr.add (hc.mul ((contDiff_seed alpha C₀ sigma hsigma).contDiffAt.sub hr))

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
