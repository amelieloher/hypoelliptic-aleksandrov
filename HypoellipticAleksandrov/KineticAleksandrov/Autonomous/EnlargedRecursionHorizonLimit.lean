module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonConsistency
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripMeasureExt
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripTimeMarginal
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-! # Right horizon limits of the actual finite-strip exit measures -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Filter
open SectionTwo TheoremA Evolution
open scoped Topology

/-- The actual occupation measure has no mass on a fixed physical time slice. -/
theorem enlarged_stripGreen_time_slice_zero
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (e : StripPole H ⊤) (b : ℝ) :
    stripGreen hH hLE hlam hLam A H ⊤ e {p | p.time = b} = 0 := by
  have h := stripGreen_timeMarginal hH hLE hlam hLam A H ⊤ e {b}
    (measurableSet_singleton b)
  simp only [Real.volume_singleton, mem_singleton_iff] at h
  exact le_antisymm h zero_le

/-- Every compact smooth probe has the correct right limit as its exit horizon decreases. -/
theorem enlarged_exit_probe_right_limit
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (e : StripPole H ⊤)
    (b : ℝ) (hb : e.1.time < b) (f : exitProbeSubmodule) :
    let t := fun n : ℕ => b + 1 / ((n : ℝ) + 1)
    let ht := fun n : ℕ => hb.trans (show b < t n by
      dsimp [t]
      exact lt_add_of_pos_right b (by positivity))
    Tendsto (fun n => ∫ p, exitProbePhysical f p
      ∂stripExit hH hLE hlam hLam A H (t n) (stripPoleFinite H e (t n) (ht n)))
      atTop (𝓝 (∫ p, exitProbePhysical f p
        ∂stripExit hH hLE hlam hLam A H b (stripPoleFinite H e b hb))) := by
  dsimp only
  let t := fun n : ℕ => b + 1 / ((n : ℝ) + 1)
  have ht (n : ℕ) : e.1.time < t n := hb.trans (by
      dsimp [t]
      exact lt_add_of_pos_right b (by positivity))
  have htlim : Tendsto t atTop (𝓝 b) := by
    simpa only [add_zero] using tendsto_one_div_add_atTop_nhds_zero_nat.const_add b
  let G := stripGreen hH hLE hlam hLam A H ⊤ e
  let g := forwardScalarOperator A.a (exitProbePhysical f)
  have hg : Integrable g G :=
    stripGreen_integrable hH hLE hlam hLam A H ⊤ e (exitProbeOperatorDatum A f)
  let D := fun n : ℕ => {p : Point | p.time < t n}
  have hanti : Antitone D := by
    intro n m hnm p hp
    have hn : (n : ℝ) ≤ m := Nat.cast_le.mpr hnm
    have hdiv : 1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := by
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    change p.time < b + 1 / ((m : ℝ) + 1) at hp
    change p.time < b + 1 / ((n : ℝ) + 1)
    linarith
  have hD : (⋂ n, D n) = {p : Point | p.time ≤ b} := by
    ext p
    constructor
    · intro hp
      exact ge_of_tendsto htlim
        (Filter.Eventually.of_forall fun n => (show p.time < t n from mem_iInter.mp hp n).le)
    · intro hp
      apply mem_iInter.mpr
      intro n
      change p.time < b + 1 / ((n : ℝ) + 1)
      exact hp.trans_lt (lt_add_of_pos_right b (by positivity))
  have hi := tendsto_setIntegral_of_antitone
    (fun n => (isOpen_lt continuous_time continuous_const).measurableSet) hanti
      (⟨0, hg.integrableOn⟩ : ∃ n, IntegrableOn g (D n) G)
  rw [hD] at hi
  have hae : {p : Point | p.time ≤ b} =ᵐ[G] {p | p.time < b} := by
    have hz := enlarged_stripGreen_time_slice_zero hH hLE hlam hLam A H e b
    have hn : ∀ᵐ p ∂G, p.time ≠ b := by
      rw [ae_iff]
      simpa only [not_not] using hz
    filter_upwards [hn] with p hp
    exact propext (lt_iff_le_and_ne.trans (and_iff_left hp)).symm
  rw [Measure.restrict_congr_set hae] at hi
  have hp (B : ℝ) (hB : e.1.time < B) :
      (∫ p, exitProbePhysical f p
        ∂stripExit hH hLE hlam hLam A H B (stripPoleFinite H e B hB)) =
        exitProbePhysical f e.1 + ∫ p in {p : Point | p.time < B}, g p ∂G := by
    have h := stripExitOfRealization_probe_integral hH hlam hLam A H
      (stripEvolution hH hLE hlam hLam A H)
      (stripEvolution_spec hH hLE hlam hLam A H) B (stripPoleFinite H e B hB) f
    change _ = exitProbePhysical f e.1 + ∫ p, g p
      ∂stripGreen hH hLE hlam hLam A H B (stripPoleFinite H e B hB) at h
    rw [stripGreen_finite_restrict_infinite] at h
    exact h
  have hf := hi.const_add (exitProbePhysical f e.1)
  rw [← hp b hb] at hf
  exact hf.congr (fun n => (hp (t n) (ht n)).symm)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
