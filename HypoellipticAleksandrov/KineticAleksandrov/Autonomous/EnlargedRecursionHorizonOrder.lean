module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionHorizonLimit
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripRepresentation

/-! # Closed early-time exit domination at an intermediate observation time -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Filter
open SectionTwo TheoremA Evolution
open scoped Topology

/-- Nonnegative compact smooth physical probes determine order of finite measures. -/
theorem enlarged_physical_measure_le {mu nu : Measure Point}
    [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (h : ∀ f : exitProbeSubmodule, (∀ p, 0 ≤ exitProbePhysical f p) →
      (∫ p, exitProbePhysical f p ∂mu) ≤ ∫ p, exitProbePhysical f p ∂nu) : mu ≤ nu := by
  let e := reconstructionPhysicalHomeomorph
  have hm : mu.map e.symm ≤ nu.map e.symm := by
    apply measure_le_of_smooth_integral_le isOpen_univ (by simp)
    intro f hf hc _ hn
    let F : exitProbeSubmodule := ⟨f, hf, hc⟩
    have hh := h F (fun p => hn _)
    have hi (rho : Measure Point) : (∫ x, f x ∂rho.map e.symm) =
        ∫ p, exitProbePhysical F p ∂rho :=
      integral_map e.symm.measurable.aemeasurable hf.continuous.measurable.aestronglyMeasurable
    rw [hi mu, hi nu]
    exact hh
  have hb (rho : Measure Point) : (rho.map e.symm).map e = rho := by
    rw [Measure.map_map e.measurable e.symm.measurable]
    have he : e ∘ e.symm = (id : Point → Point) := funext e.apply_symm_apply
    rw [he, Measure.map_id]
  have hmap := Measure.map_mono hm e.measurable
  rwa [hb mu, hb nu] at hmap

/-- Later-horizon exits up to a closed intermediate time are dominated by its stopped exit.
This retains possible endpoint mass rather than assuming temporal atomlessness. -/
theorem enlarged_stripExit_early_closed_le
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (e : StripPole H ⊤)
    (b T : ℝ) (hb : e.1.time < b) (hBT : b < T) :
    (stripExit hH hLE hlam hLam A H T
      (stripPoleFinite H e T (hb.trans hBT))).restrict {p | p.time ≤ b} ≤
        stripExit hH hLE hlam hLam A H b (stripPoleFinite H e b hb) := by
  let t := fun n : ℕ => b + 1 / ((n : ℝ) + 1)
  have hbt (n : ℕ) : b < t n := by dsimp [t]; exact lt_add_of_pos_right b (by positivity)
  have ht (n : ℕ) : e.1.time < t n := hb.trans (hbt n)
  have hlim : Tendsto t atTop (𝓝 b) := by
    simpa only [add_zero] using tendsto_one_div_add_atTop_nhds_zero_nat.const_add b
  have hsmall : ∀ᶠ n in atTop, t n < T := hlim.eventually (gt_mem_nhds hBT)
  let S : Set Point := {p | p.time ≤ b}
  have hS : MeasurableSet S := (isClosed_le continuous_time continuous_const).measurableSet
  apply enlarged_physical_measure_le
  intro f hn
  have hconv := enlarged_exit_probe_right_limit hH hLE hlam hLam A H e b hb f
  apply ge_of_tendsto hconv
  filter_upwards [hsmall] with n hnT
  let R := (b + t n) / 2
  have hR : b < R := by dsimp [R]; linarith [hbt n]
  have hRt : R ≤ t n := by dsimp [R]; linarith [hbt n]
  have hRT : R ≤ T := hRt.trans hnT.le
  have he := stripExit_horizon_consistency hH hLE hlam hLam A H e T (t n)
    (hb.trans hBT) (ht n) R hRT hRt
  have he' := congrArg (fun rho : Measure Point => rho.restrict S) he
  have hs : S ⊆ {p : Point | p.time < R} := fun p hp => hp.trans_lt hR
  simp only [Measure.restrict_restrict hS, inter_eq_left.mpr hs] at he'
  rw [he']
  exact integral_mono_measure Measure.restrict_le_self (Filter.Eventually.of_forall hn)
    (nestedProbe_integrable A f _)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
