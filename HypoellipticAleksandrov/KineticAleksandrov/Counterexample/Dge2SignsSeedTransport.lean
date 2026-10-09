module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2Signs
import Mathlib.Tactic.FieldSimp

/-!
# Uniform transport positivity on the seed ball

The additive seed constant is chosen once by compactness on the position sphere
and the small velocity ball, before any point is quantified.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/-- The compact small seed ball over the Euclidean position sphere. -/
def smallSeedBall (d : ℕ) : Set (PDE.Vec d × PDE.Vec d) :=
  {q | PDE.vecNormSq q.2 = 1 ∧ PDE.vecEuclideanNorm (q.1 - q.2) ≤ 1 / 4}

/-- The small seed ball is compact in the inherited native topology. -/
theorem isCompact_smallSeedBall (d : ℕ) : IsCompact (smallSeedBall d) := by
  have hclosed : IsClosed (smallSeedBall d) :=
    (isClosed_eq (PDE.continuous_vecNormSq.comp continuous_snd) continuous_const).inter
      (isClosed_le (PDE.continuous_vecEuclideanNorm.comp (continuous_fst.sub continuous_snd))
        continuous_const)
  apply (isCompact_closedBall (0 : PDE.Vec d × PDE.Vec d) 2).of_isClosed_subset hclosed
  intro q hq
  obtain ⟨he, hy⟩ := hq
  have hen : PDE.vecEuclideanNorm q.2 = 1 := by simp [PDE.vecEuclideanNorm, he]
  have he' : ‖q.2‖ ≤ 1 := by simpa [hen] using PDE.norm_le_vecEuclideanNorm q.2
  have hy' : ‖q.1 - q.2‖ ≤ 1 / 4 := (PDE.norm_le_vecEuclideanNorm _).trans hy
  have htri : ‖q.1‖ ≤ ‖q.1 - q.2‖ + ‖q.2‖ := by
    simpa only [sub_add_cancel] using norm_add_le (q.1 - q.2) q.2
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff]
  constructor <;> linarith

/-- Increasing the additive seed constant has exactly the source's transport effect. -/
theorem ansatzTransport_seed_shift {d : ℕ} (alpha C₀ sigma : ℝ) (hsigma : 0 < sigma)
    (y e : PDE.Vec d) :
    ansatzTransport alpha (seed alpha C₀ sigma) y e =
      ansatzTransport alpha (seed alpha 0 sigma) y e +
        PDE.vecDot y e * (alpha / 3 * C₀) := by
  rw [ansatzTransport_seed alpha C₀ sigma hsigma, ansatzTransport_seed alpha 0 sigma hsigma]
  unfold seed
  ring

/-- The seed transport is continuous in both vector variables. -/
theorem continuous_seed_transport {d : ℕ} (alpha C₀ sigma : ℝ) (hsigma : 0 < sigma) :
    Continuous (fun q : PDE.Vec d × PDE.Vec d =>
      ansatzTransport alpha (seed alpha C₀ sigma) q.1 q.2) := by
  have hb : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : PDE.Vec d × PDE.Vec d => seedBase sigma q.1 q.2) := by
    unfold seedBase PDE.vecNormSq PDE.vecDot
    fun_prop
  have hp : Continuous (fun q : PDE.Vec d × PDE.Vec d =>
      Real.rpow (seedBase sigma q.1 q.2) (alpha / 2 - 1)) :=
    (hb.rpow_const_of_ne (p := alpha / 2 - 1) fun q =>
      (seedBase_pos sigma hsigma q.1 q.2).ne').continuous
  have hs := (contDiff_seed (d := d) alpha C₀ sigma hsigma).continuous
  simp_rw [ansatzTransport_seed alpha C₀ sigma hsigma]
  unfold PDE.vecDot
  fun_prop

/-- A single positive additive seed constant makes transport at least one on the small ball. -/
theorem seed_transport_pos (d : ℕ) (alpha sigma : ℝ) (ha : 0 < alpha)
    (hsigma : 0 < sigma) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ y e : PDE.Vec d,
      PDE.vecNormSq e = 1 → PDE.vecEuclideanNorm (y - e) ≤ 1 / 4 →
      1 ≤ ansatzTransport alpha (seed alpha C₀ sigma) y e := by
  let f : PDE.Vec d × PDE.Vec d → ℝ :=
    fun q => ansatzTransport alpha (seed alpha 0 sigma) q.1 q.2
  obtain ⟨B₀, hB₀⟩ := (isCompact_smallSeedBall d).bddAbove_image
    (continuous_seed_transport alpha 0 sigma hsigma).abs.continuousOn
  let B := max 0 B₀
  have hB : 0 ≤ B := le_max_left _ _
  let C₀ := 4 * (B + 1) / alpha
  have hC₀ : 0 < C₀ := div_pos (mul_pos (by norm_num) (by linarith)) ha
  refine ⟨C₀, hC₀, ?_⟩
  intro y e he hy
  have hbound : |f (y, e)| ≤ B :=
    (hB₀ ⟨(y, e), ⟨he, hy⟩, rfl⟩).trans (le_max_right _ _)
  have hlow := (abs_le.mp hbound).1
  have hdot := seed_ball_dot_lower y e he hy
  have hc : 0 < alpha / 3 * C₀ := mul_pos (div_pos ha (by norm_num)) hC₀
  have hmul := mul_le_mul_of_nonneg_right hdot hc.le
  have heq : (3 / 4 : ℝ) * (alpha / 3 * C₀) = B + 1 := by
    dsimp [C₀]
    field_simp
  rw [heq] at hmul
  rw [ansatzTransport_seed_shift alpha C₀ sigma hsigma]
  change 1 ≤ f (y, e) + PDE.vecDot y e * (alpha / 3 * C₀)
  linarith

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
