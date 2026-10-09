module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsMollifier
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsScaling

/-! # Actual rectangular cutoffs for sublinear Bellman barriers -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Set MeasureTheory

/-- A fixed unit inner radius and two-unit outer radius cutoff. -/
def barrierCutoffBump : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩

/-- The same scalar cutoff is used on the two different kinetic scales. -/
def barrierCutoff : ℝ → ℝ := barrierCutoffBump

/-- The cutoff takes values in the source unit interval. -/
theorem barrierCutoff_bounds (x : ℝ) : 0 ≤ barrierCutoff x ∧ barrierCutoff x ≤ 1 :=
  ⟨barrierCutoffBump.nonneg, barrierCutoffBump.le_one⟩

/-- The fixed cutoff is C∞. -/
theorem barrierCutoff_contDiff : ContDiff ℝ (⊤ : ℕ∞) barrierCutoff :=
  barrierCutoffBump.contDiff

/-- The cutoff and both actual derivatives vanish outside its outer interval. -/
theorem barrierCutoff_zero_jets {x : ℝ} (hx : 2 < |x|) :
    barrierCutoff x = 0 ∧ deriv barrierCutoff x = 0 ∧
      deriv (deriv barrierCutoff) x = 0 := by
  have hn : x ∉ tsupport barrierCutoff := by
    rw [barrierCutoff, barrierCutoffBump.tsupport_eq]
    simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, not_le, barrierCutoffBump] using hx
  exact ⟨image_eq_zero_of_notMem_tsupport hn, deriv_of_notMem_tsupport hn,
    deriv_of_notMem_tsupport (fun h => hn (tsupport_deriv_subset h))⟩

/-- The two scalar derivative bounds are fixed before any coefficient or spatial scale. -/
theorem barrierCutoff_derivative_bounds : ∃ D1 D2 : ℝ, 0 ≤ D1 ∧ 0 ≤ D2 ∧
    (∀ x, |deriv barrierCutoff x| ≤ D1) ∧
    (∀ x, |deriv (deriv barrierCutoff) x| ≤ D2) := by
  obtain ⟨_, D1, D2, _, hD1, hD2, _, h1, h2⟩ := barrier_kernel_uniform_bounds
    barrierCutoff (barrierCutoff_contDiff.of_le (by simp)) barrierCutoffBump.hasCompactSupport
  exact ⟨D1, D2, hD1, hD2, h1, h2⟩

/-- The physical rectangular cutoff, centered at the barrier's position singularity. -/
def barrierRectCutoff (Y R : ℝ) (z : ℝ × ℝ) : ℝ :=
  barrierCutoff ((z.1 - Y) / R ^ 3) * barrierCutoff (z.2 / R)

/-- The rectangular cutoff remains between zero and one. -/
theorem barrierRectCutoff_bounds (Y R : ℝ) (z : ℝ × ℝ) :
    0 ≤ barrierRectCutoff Y R z ∧ barrierRectCutoff Y R z ≤ 1 := by
  exact ⟨mul_nonneg (barrierCutoff_bounds _).1 (barrierCutoff_bounds _).1,
    (mul_le_mul (barrierCutoff_bounds _).2 (barrierCutoff_bounds _).2
      (barrierCutoff_bounds _).1 zero_le_one).trans_eq (one_mul _)⟩

/-- The literal rectangular cutoff is continuous on the physical plane. -/
theorem barrierRectCutoff_continuous (Y R : ℝ) : Continuous (barrierRectCutoff Y R) :=
  (barrierCutoff_contDiff.continuous.comp
    ((continuous_fst.sub continuous_const).div_const _)).mul
      (barrierCutoff_contDiff.continuous.comp (continuous_snd.div_const _))

/-- Multiplication by the literal kinetic rectangle produces a compact physical test. -/
theorem barrierRectCutoff_hasCompactSupport (Y R : ℝ) (hR : 0 < R) (f : ℝ × ℝ → ℝ) :
    HasCompactSupport (fun z => barrierRectCutoff Y R z * f z) := by
  apply HasCompactSupport.of_support_subset_isCompact
    ((isCompact_Icc (a := Y - 2 * R ^ 3) (b := Y + 2 * R ^ 3)).prod
      (isCompact_Icc (a := -(2 * R)) (b := 2 * R)))
  intro z hz
  by_contra hn
  have hlarge : 2 < |(z.1 - Y) / R ^ 3| ∨ 2 < |z.2 / R| := by
    by_contra hh
    push Not at hh
    apply hn
    have hx := (div_le_iff₀ (pow_pos hR 3)).mp
      (by simpa only [abs_div, abs_of_pos (pow_pos hR 3)] using hh.1)
    have hv := (div_le_iff₀ hR).mp
      (by simpa only [abs_div, abs_of_pos hR] using hh.2)
    have hxb := abs_le.mp hx
    have hvb := abs_le.mp hv
    exact ⟨⟨by linarith only [hxb.1], by linarith only [hxb.2]⟩, hvb⟩
  apply hz
  rcases hlarge with hx | hv
  · simp only [barrierRectCutoff, (barrierCutoff_zero_jets hx).1, zero_mul]
  · simp only [barrierRectCutoff, (barrierCutoff_zero_jets hv).1, mul_zero, zero_mul]

/-- The literal rectangular cutoff preserves joint C² regularity. -/
theorem barrierRectCutoff_contDiff (Y R : ℝ) (f : ℝ × ℝ → ℝ) (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 2 (fun z => barrierRectCutoff Y R z * f z) := by
  have hc : ContDiff ℝ 2 barrierCutoff := barrierCutoff_contDiff.of_le (by simp)
  exact ((hc.comp ((contDiff_fst.sub contDiff_const).div_const (R ^ 3))).mul
    (hc.comp (contDiff_snd.div_const R))).mul hf

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
