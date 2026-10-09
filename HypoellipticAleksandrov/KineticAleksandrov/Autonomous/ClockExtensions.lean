module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockCalculus
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! # Literal cutoff construction for the clock coefficient extensions

The cutoff has inner radius `3/4` and outer radius `7/8`, so its support stays
strictly inside the source coefficient region `|y| < 1`.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open MeasureTheory Filter
open scoped Topology

/-- A fixed genuine smooth cutoff with the required normalized radii. -/
def clockCutoff : ContDiffBump (0 : ℝ) where
  rIn := 3 / 4
  rOut := 7 / 8
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The cutoff equals one throughout the normalized active interval. -/
theorem clockCutoff_eq_one {y : ℝ} (hy : |y| ≤ 3 / 4) : clockCutoff y = 1 := by
  apply clockCutoff.one_of_mem_closedBall
  simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, clockCutoff] using hy

/-- Away from the cutoff region it vanishes on a neighborhood, not just at one point. -/
theorem clockCutoff_eventually_zero {y : ℝ} (hy : ¬ |y| < 1) :
    ∀ᶠ t in 𝓝 y, clockCutoff t = 0 := by
  have hh : (7 / 8 : ℝ) < |y| := by linarith only [not_lt.mp hy]
  have hn : ∀ᶠ t in 𝓝 y, (7 / 8 : ℝ) < |t| :=
    (isOpen_lt continuous_const continuous_abs).mem_nhds hh
  filter_upwards [hn] with t ht
  apply clockCutoff.zero_of_le_dist
  simpa only [Real.dist_eq, sub_zero, clockCutoff] using ht.le

/-- The exact convex diffusion extension from the source proof. -/
def Clock.extendedDiffusion (c : Clock) (lam : ℝ) (a : ℝ → ℝ → ℝ)
    (e : Point) (s y : ℝ) : ℝ :=
  clockCutoff y * c.diffusion a e s y + (1 - clockCutoff y) * lam

/-- The exact convex derivative to be integrated for the transport extension. -/
def Clock.extendedDriftDerivative (c : Clock) (y : ℝ) : ℝ :=
  clockCutoff y * (c.vbar ^ 2 / (c.vbar + c.r * y) ^ 2) + 1 - clockCutoff y

/-- The exact integral transport extension, normalized to vanish at zero. -/
def Clock.extendedDrift (c : Clock) (y : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..y, c.extendedDriftDerivative t

/-- The diffusion extension is genuinely smooth, including outside the raw denominator region. -/
theorem Clock.extendedDiffusion_smooth {lam Lam : ℝ} (c : Clock)
    (A : SmoothAutonomous lam Lam) (e : Point) :
    ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (c.extendedDiffusion lam A.a e)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro q
  by_cases hy : |q.2| < 1
  · exact ((clockCutoff.contDiffAt.comp q contDiffAt_snd).mul
      (c.diffusion_contDiffAt A e q (c.normalized_ne_zero hy))).add
      ((contDiffAt_const.sub (clockCutoff.contDiffAt.comp q contDiffAt_snd)).mul
        contDiffAt_const)
  · have hz := clockCutoff_eventually_zero hy
    have hq : ∀ᶠ p : ℝ × ℝ in 𝓝 q, clockCutoff p.2 = 0 :=
      (continuous_snd.continuousAt.tendsto.eventually hz)
    apply (contDiffAt_const (c := lam)).congr_of_eventuallyEq
    filter_upwards [hq] with p hp
    simp only [Function.uncurry, Clock.extendedDiffusion, hp, zero_mul, sub_zero, one_mul, zero_add]

/-- The extended drift derivative is globally smooth. -/
theorem Clock.extendedDriftDerivative_smooth (c : Clock) :
    ContDiff ℝ (⊤ : ℕ∞) c.extendedDriftDerivative := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases hy : |y| < 1
  · have hd : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun t : ℝ => c.vbar ^ 2 / (c.vbar + c.r * t) ^ 2) y :=
      contDiffAt_const.div
        ((contDiffAt_const.add (contDiffAt_const.mul contDiffAt_id)).pow 2)
        (pow_ne_zero _ (c.normalized_ne_zero hy))
    exact ((clockCutoff.contDiffAt.mul hd).add contDiffAt_const).sub clockCutoff.contDiffAt
  · apply (contDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq
    filter_upwards [clockCutoff_eventually_zero hy] with t ht
    simp only [Clock.extendedDriftDerivative, ht, zero_mul, zero_add, sub_zero]

/-- The extension agrees with the raw diffusion on the normalized active interval. -/
theorem Clock.extendedDiffusion_eq {lam : ℝ} (c : Clock) (a : ℝ → ℝ → ℝ)
    (e : Point) (s y : ℝ) (hy : y ∈ normalizedActive) :
    c.extendedDiffusion lam a e s y = c.diffusion a e s y := by
  have hy' : (-3 / 4 : ℝ) < y ∧ y < 3 / 4 := hy
  have hb : |y| ≤ 3 / 4 := (abs_lt.mpr
    ⟨by linarith only [hy'.1], hy'.2⟩).le
  simp only [Clock.extendedDiffusion, clockCutoff_eq_one hb, one_mul, sub_self, zero_mul,
    add_zero]

/-- The global diffusion bounds depend only on the original ellipticity constants. -/
theorem Clock.extendedDiffusion_bounds {lam Lam : ℝ} (hlam : 0 < lam)
    (hLam : lam ≤ Lam) (c : Clock) (A : SmoothAutonomous lam Lam)
    (e : Point) (s y : ℝ) :
    3 * lam / 5 ≤ c.extendedDiffusion lam A.a e s y ∧
      c.extendedDiffusion lam A.a e s y ≤ 3 * Lam := by
  by_cases hy : |y| < 1
  · have hb := c.diffusion_bounds hlam hLam A e s y hy
    have ht0 : 0 ≤ clockCutoff y := clockCutoff.nonneg
    have ht1 : clockCutoff y ≤ 1 := clockCutoff.le_one
    have h1 := mul_nonneg ht0 (sub_nonneg.mpr hb.1)
    have h2 := mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr (by
      linarith only [hlam] : 3 * lam / 5 ≤ lam))
    have h3 := mul_nonneg ht0 (sub_nonneg.mpr hb.2)
    have h4 := mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr (by
      linarith only [hlam, hLam] : lam ≤ 3 * Lam))
    simp only [Clock.extendedDiffusion]
    constructor <;> nlinarith only [h1, h2, h3, h4]
  · have ht : clockCutoff y = 0 := by
      apply clockCutoff.zero_of_le_dist
      have hh : (7 / 8 : ℝ) ≤ |y| := by linarith only [not_lt.mp hy]
      simpa only [Real.dist_eq, sub_zero, clockCutoff] using hh
    simp only [Clock.extendedDiffusion, ht, zero_mul, sub_zero, one_mul, zero_add]
    constructor <;> linarith only [hlam, hLam]

/-- The convex extension of the derivative retains the universal source bounds. -/
theorem Clock.extendedDriftDerivative_bounds (c : Clock) (y : ℝ) :
    (9 / 25 : ℝ) ≤ c.extendedDriftDerivative y ∧ c.extendedDriftDerivative y ≤ 9 := by
  by_cases hy : |y| < 1
  · have hb := c.drift_deriv_bounds hy
    rw [(c.hasDerivAt_drift hy).deriv] at hb
    have ht0 : 0 ≤ clockCutoff y := clockCutoff.nonneg
    have ht1 : clockCutoff y ≤ 1 := clockCutoff.le_one
    have h1 := mul_nonneg ht0 (sub_nonneg.mpr hb.1)
    have h2 := mul_nonneg ht0 (sub_nonneg.mpr hb.2)
    simp only [Clock.extendedDriftDerivative]
    constructor <;> nlinarith only [h1, h2, ht0, ht1]
  · have ht : clockCutoff y = 0 := by
      apply clockCutoff.zero_of_le_dist
      have hh : (7 / 8 : ℝ) ≤ |y| := by linarith only [not_lt.mp hy]
      simpa only [Real.dist_eq, sub_zero, clockCutoff] using hh
    simp only [Clock.extendedDriftDerivative, ht, zero_mul, zero_add, sub_zero]
    norm_num

/-- The integrated extension has exactly the constructed derivative at every point. -/
theorem Clock.hasDerivAt_extendedDrift (c : Clock) (y : ℝ) :
    HasDerivAt c.extendedDrift (c.extendedDriftDerivative y) y := by
  have hc := c.extendedDriftDerivative_smooth.continuous
  exact intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable _ _) hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

/-- The transport extension is globally C-infinity, not merely continuously differentiable. -/
theorem Clock.extendedDrift_smooth (c : Clock) :
    ContDiff ℝ (⊤ : ℕ∞) c.extendedDrift := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun y => (c.hasDerivAt_extendedDrift y).differentiableAt, ?_⟩
  have hd : deriv c.extendedDrift = c.extendedDriftDerivative :=
    funext (fun y => (c.hasDerivAt_extendedDrift y).deriv)
  rw [hd]
  exact c.extendedDriftDerivative_smooth

/-- The derivative of the extension has the universal bounds everywhere. -/
theorem Clock.extendedDrift_deriv_bounds (c : Clock) (y : ℝ) :
    (9 / 25 : ℝ) ≤ deriv c.extendedDrift y ∧ deriv c.extendedDrift y ≤ 9 := by
  rw [(c.hasDerivAt_extendedDrift y).deriv]
  exact c.extendedDriftDerivative_bounds y

/-- The integrated transport extension agrees with the original drift on `J*`. -/
theorem Clock.extendedDrift_eq (c : Clock) {y : ℝ} (hy : y ∈ normalizedActive) :
    c.extendedDrift y = c.drift y := by
  have hy' : (-3 / 4 : ℝ) < y ∧ y < 3 / 4 := hy
  have hd : ∀ t ∈ Set.uIcc (0 : ℝ) y, |t| ≤ 3 / 4 := by
    intro t ht
    rw [Set.mem_uIcc] at ht
    rcases ht with ht | ht
    · rw [abs_of_nonneg ht.1]
      exact ht.2.trans hy'.2.le
    · rw [abs_of_nonpos ht.2]
      linarith only [ht.1, hy'.1]
  have hh : ∀ t ∈ Set.uIcc (0 : ℝ) y,
      HasDerivAt c.drift (c.extendedDriftDerivative t) t := by
    intro t ht
    have hb := hd t ht
    have hs : |t| < 1 := by linarith only [hb]
    simpa only [Clock.extendedDriftDerivative, clockCutoff_eq_one hb, one_mul,
      add_sub_cancel_right] using! c.hasDerivAt_drift hs
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt hh
    (c.extendedDriftDerivative_smooth.continuous.intervalIntegrable 0 y)
  simpa only [Clock.extendedDrift, Clock.drift, mul_zero, zero_div, sub_zero] using heq

/-- The complete source coefficient extension conclusion, with its shared witnesses. -/
theorem Clock.exists_extensions {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (c : Clock) (A : SmoothAutonomous lam Lam) (e : Point) :
    ∃ B : ℝ → ℝ → ℝ, ∃ b : ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry B) ∧
      ContDiff ℝ (⊤ : ℕ∞) b ∧
      (∀ s y, y ∈ normalizedActive → B s y = c.diffusion A.a e s y) ∧
      (∀ y ∈ normalizedActive, b y = c.drift y) ∧
      (∀ s y, 3 * lam / 5 ≤ B s y ∧ B s y ≤ 3 * Lam) ∧
      (∀ y, (9 / 25 : ℝ) ≤ deriv b y ∧ deriv b y ≤ 9) := by
  refine ⟨c.extendedDiffusion lam A.a e, c.extendedDrift,
    c.extendedDiffusion_smooth A e, c.extendedDrift_smooth, ?_, ?_, ?_, ?_⟩
  · intro s y hy
    exact c.extendedDiffusion_eq A.a e s y hy
  · intro y hy
    exact c.extendedDrift_eq hy
  · intro s y
    exact c.extendedDiffusion_bounds hlam hLam A e s y
  · intro y
    exact c.extendedDrift_deriv_bounds y

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
