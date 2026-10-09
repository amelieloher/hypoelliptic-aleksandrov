module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VelocityReturn

/-! # The literal scalar semigroup statement of velocity return -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov MeasureTheory Set

/-- The source's active velocity indicator, as actual bounded Borel scalar data. -/
def activeVelocityDatum (c : Clock) : BoundedBorel Z := by
  let B : Set Z := {w | w.2 ∈ c.active}
  have hB : MeasurableSet B := isOpen_Ioo.measurableSet.preimage measurable_snd
  exact ⟨B.indicator (fun _ => 1), measurable_const.indicator hB,
    ⟨1, zero_le_one, fun w => by
      by_cases hw : w ∈ B
      · simp only [indicator_of_mem hw, abs_one, le_refl]
      · simp only [indicator_of_notMem hw, abs_zero, zero_le_one]⟩⟩

/-- Scalar and native physical terminal kernels agree at every nonnegative elapsed time. -/
theorem return_Kphysical_eq_kernelXV
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (t : ℝ) (ht : 0 ≤ t) (z : Z) :
    Kphysical hH hLE hlam hLam A t z =
      kernelXV (fullSpaceEvolution hH hLE hlam hLam A) (Real.toNNReal t) z := by
  unfold Kphysical kernelXV wholeQuery
  rw [dite_eq_left ht]
  simp only [Real.coe_toNNReal t ht]
  rfl

/-- The source active indicator action is the real mass of the same active velocity set. -/
theorem activeVelocityDatum_action_eq
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (t : ℝ) (ht : 0 ≤ t) (z : Z) :
    S hH hLE hlam hLam A t (activeVelocityDatum c) z =
      (kernelXV (fullSpaceEvolution hH hLE hlam hLam A) (Real.toNNReal t) z
        {w | w.2 ∈ c.active}).toReal := by
  rw [S_eq_integral hH hLE hlam hLam A t ht]
  change (∫ w, ({w : Z | w.2 ∈ c.active}).indicator (fun _ => (1 : ℝ)) w
    ∂Kphysical hH hLE hlam hLam A t z) = _
  have hB : MeasurableSet {w : Z | w.2 ∈ c.active} :=
    isOpen_Ioo.measurableSet.preimage measurable_snd
  rw [integral_indicator hB]
  simp only [integral_const, smul_eq_mul, mul_one, Measure.real,
    Measure.restrict_apply MeasurableSet.univ, univ_inter,
    return_Kphysical_eq_kernelXV hH hLE hlam hLam A t ht]

/-- Literal equation `e:velocity-return`, with the scalar source return-time premise. -/
theorem velocity_return_action_of_return_time
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hReturn : ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (F : BoundedBorel Z),
      (∀ z, 0 ≤ F z) → ∀ t s X v : ℝ,
      0 < t → 2 * t ≤ s → s ≤ 3 * t → |v| ≤ Real.sqrt t →
      S hH hLE hlam hLam A t F (X, v) ≤ C * S hH hLE hlam hLam A s F (X, v)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock) (z : Z) (t : ℝ),
      |c.vbar| = 2 * c.r → |z.2| ≤ 3 * c.r → 0 ≤ t →
      S hH hLE hlam hLam A t (activeVelocityDatum c) z ≤
        C * (1 + t / c.r ^ 2) ^ (-(1 : ℝ) / 2) := by
  obtain ⟨C, hC, h⟩ := velocity_band_return_of_return_time hH hLE hlam hLam hReturn
  refine ⟨C, hC, ?_⟩
  intro A c z t hc hz ht
  rw [activeVelocityDatum_action_eq hH hLE hlam hLam A c t ht z]
  have hsub : {w : Z | w.2 ∈ c.active} ⊆ {w | |w.2| ≤ 3 * c.r} := by
    intro w hw
    have hh := (c.active_abs_bounds hw).2
    rw [hc] at hh
    change |w.2| ≤ 3 * c.r
    linarith only [hh]
  have hmass := (measure_mono (subset_univ {w : Z | |w.2| ≤ 3 * c.r})).trans
    (kernelXV_mass_le_one (fullSpaceEvolution hH hLE hlam hLam A) (Real.toNNReal t) z)
  apply (ENNReal.toReal_mono (hmass.trans_lt ENNReal.one_lt_top).ne
    (measure_mono hsub)).trans
  simpa only [Real.coe_toNNReal t ht] using h A c.r z (Real.toNNReal t) c.positive hz

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
