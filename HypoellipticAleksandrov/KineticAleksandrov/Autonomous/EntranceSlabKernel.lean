module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EntranceSlabQuadratic

/-! # The actual terminal family as a finite kernel

This kernel is definitionally the existing terminal family, including the
zero-duration branch. It introduces no alternative terminal measure.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory ProbabilityTheory HypoellipticAleksandrov
open scoped Classical

/-- The guard for the zero-duration branch of the actual terminal family is measurable. -/
theorem entranceSlabTerminal_guard_measurable (c : Clock) (J : Interval) (b : ℝ) :
    MeasurableSet {p : Point | p.time = b ∧
      p.velocity 0 ∈ (visitActiveUnion c J).carrier} :=
  (isClosed_eq continuous_time continuous_const).measurableSet.inter
    ((visitActiveUnion c J).isOpen_carrier.measurableSet.preimage
      ((continuous_apply 0).comp continuous_velocity).measurable)

/-- The existing terminal family, packaged as a measurable finite kernel. -/
def entranceSlabTerminalKernel
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b : ℝ) :
    Kernel Point Point :=
  Kernel.piecewise (entranceSlabTerminal_guard_measurable c J b) Kernel.id
    ((enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) b).restrict
      (show MeasurableSet {p : Point | p.time = b} from
        (isClosed_eq continuous_time continuous_const).measurableSet))

/-- The finite kernel is exactly the canonical terminal family at every pole. -/
theorem entranceSlabTerminalKernel_apply
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b : ℝ) (p : Point) :
    entranceSlabTerminalKernel hH hLE hlam hLam A c J b p =
      enlargedActiveTerminalFamily hH hLE hlam hLam A c J b p := rfl

/-- Each actual terminal family has a uniform finite mass bound. -/
instance entranceSlabTerminalKernel_isFiniteKernel
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b : ℝ) :
    IsFiniteKernel (entranceSlabTerminalKernel hH hLE hlam hLam A c J b) := by
  unfold entranceSlabTerminalKernel
  infer_instance

/-- The actual terminal family is measurable, including its initial-value branch. -/
theorem entranceSlabTerminalFamily_measurable
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b : ℝ) :
    Measurable (enlargedActiveTerminalFamily hH hLE hlam hLam A c J b) :=
  (entranceSlabTerminalKernel hH hLE hlam hLam A c J b).measurable

/-- A mixture of actual terminal families is finite for any finite starting measure. -/
instance entranceSlabTerminal_bind_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b : ℝ)
    (mu : Measure Point) [IsFiniteMeasure mu] :
    IsFiniteMeasure (mu.bind (enlargedActiveTerminalFamily hH hLE hlam hLam A c J b)) :=
  inferInstanceAs (IsFiniteMeasure
    (entranceSlabTerminalKernel hH hLE hlam hLam A c J b ∘ₘ mu))

/-- Actual terminal mixtures remain in the closed active velocity interval. -/
theorem entranceSlabTerminal_ae_velocity
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b : ℝ)
    (mu : Measure Point) :
    ∀ᵐ q ∂mu.bind (enlargedActiveTerminalFamily hH hLE hlam hLam A c J b),
      q.velocity 0 ∈ closure c.active := by
  change ∀ᵐ q ∂(entranceSlabTerminalKernel hH hLE hlam hLam A c J b ∘ₘ mu), _
  apply Measure.ae_comp_of_ae_ae
    (isClosed_closure.measurableSet.preimage
      ((continuous_apply 0).comp continuous_velocity).measurable)
  apply Filter.Eventually.of_forall
  intro p
  rw [entranceSlabTerminalKernel_apply]
  unfold enlargedActiveTerminalFamily
  split
  · rename_i hp
    apply (ae_dirac_iff (isClosed_closure.measurableSet.preimage
      ((continuous_apply 0).comp continuous_velocity).measurable)).mpr
    exact subset_closure (((visitActiveUnion_carrier c J).le hp.2).1)
  · have hz := enlargedActiveExitMixture_ae_velocity hH hLE hlam hLam A c J b
      (Measure.dirac p)
    rw [Measure.dirac_bind
      (enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) b).measurable p]
      at hz
    exact hz.filter_mono (ae_mono Measure.restrict_le_self)

/-- The source quadratic is integrable on every finite actual terminal mixture. -/
theorem entranceSlabTerminal_quadratic_integrable
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b : ℝ)
    (mu : Measure Point) [IsFiniteMeasure mu] :
    Integrable (fun q => visitQuadratic c (q.velocity 0))
      (mu.bind (enlargedActiveTerminalFamily hH hLE hlam hLam A c J b)) := by
  apply Integrable.mono' (integrable_const (9 * c.r ^ 2 / 16))
    (((visitQuadratic_smooth c).continuous.comp
      ((continuous_apply 0).comp continuous_velocity)).measurable.aestronglyMeasurable)
  filter_upwards [entranceSlabTerminal_ae_velocity hH hLE hlam hLam A c J b mu] with q hq
  change ‖visitQuadratic c (q.velocity 0)‖ ≤ 9 * c.r ^ 2 / 16
  rw [Real.norm_eq_abs, abs_of_nonneg (visitQuadratic_nonneg c hq)]
  exact visitQuadratic_le c _

/-- Outside the open active interval the source quadratic is nonpositive. -/
theorem entranceSlabQuadratic_nonpos (c : Clock) (v : ℝ) (hv : v ∉ c.active) :
    visitQuadratic c v ≤ 0 := by
  have hr := c.positive
  change ¬(c.vbar - 3 * c.r / 4 < v ∧ v < c.vbar + 3 * c.r / 4) at hv
  rw [visitQuadratic]
  by_cases hl : c.vbar - 3 * c.r / 4 < v
  · have hu : c.vbar + 3 * c.r / 4 ≤ v := le_of_not_gt (fun h => hv ⟨hl, h⟩)
    exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hl.le) (sub_nonpos.mpr hu)
  · have hl' : v ≤ c.vbar - 3 * c.r / 4 := le_of_not_gt hl
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hl') (by linarith)

/-- The quadratic terminal contribution charges only the open active band. -/
theorem entranceSlabQuadratic_integral_le_active (c : Clock) (mu : Measure Point)
    [IsFiniteMeasure mu] (hi : Integrable (fun q => visitQuadratic c (q.velocity 0)) mu) :
    (∫ q, visitQuadratic c (q.velocity 0) ∂mu) ≤
      9 * c.r ^ 2 / 16 * (mu {q | q.velocity 0 ∈ c.active}).toReal := by
  let B : Set Point := {q | q.velocity 0 ∈ c.active}
  have hB : MeasurableSet B := isOpen_Ioo.measurableSet.preimage
    ((continuous_apply 0).comp continuous_velocity).measurable
  have hm := integral_mono_ae hi ((integrable_const (9 * c.r ^ 2 / 16)).indicator hB)
    (Filter.Eventually.of_forall fun q => by
      by_cases hq : q ∈ B
      · rw [indicator_of_mem hq]
        exact visitQuadratic_le c _
      · rw [indicator_of_notMem hq]
        exact entranceSlabQuadratic_nonpos c _ hq)
  rw [integral_indicator hB] at hm
  simpa only [integral_const, smul_eq_mul, Measure.real,
    Measure.restrict_apply MeasurableSet.univ, univ_inter, mul_comm] using hm

/-- Removing starts can only decrease the actual terminal mixture. -/
theorem entranceSlabTerminal_restrict_bind_le
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b : ℝ)
    (mu : Measure Point) (D : Set Point) :
    (mu.restrict D).bind (enlargedActiveTerminalFamily hH hLE hlam hLam A c J b) ≤
      mu.bind (enlargedActiveTerminalFamily hH hLE hlam hLam A c J b) := by
  apply Measure.le_iff.mpr
  intro B hB
  rw [Measure.bind_apply hB
    (entranceSlabTerminalFamily_measurable hH hLE hlam hLam A c J b).aemeasurable,
    Measure.bind_apply hB
      (entranceSlabTerminalFamily_measurable hH hLE hlam hLam A c J b).aemeasurable]
  exact lintegral_mono' Measure.restrict_le_self le_rfl

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
