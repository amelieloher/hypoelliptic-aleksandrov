module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceFutureInterior
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceLinearity
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ClassicalTerminalWeak
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Interior continuity for positive bounded Borel sources

A separating time splits the actual source into a continuous future potential and a recent
potential uniformly controlled by the short time barrier. No continuity of the source is used.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set Filter Evolution Metric
open scoped Topology
variable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}

/-- The literal positive bounded Borel potential is continuous on the open past cylinder. -/
theorem continuousOn_duhamelPotential_bounded_nonneg
    (hH : HormanderHypoellipticityStatement)
    (hΩa : IsAdmissibleEvolutionDomain Ω) (hΩ : MeasurableSet Ω) (hγ : Continuous γ)
    (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    (S : TerminalOperatorFamily Ω γ) (K : MovingFiberKernel Ω γ)
    (hreal : RealizesTerminalEvolution Ω γ hΩ B b S K)
    (hB : IsSmoothFullKineticCoefficient B) (hBs : IsSymmetricFullKineticCoefficient B)
    (hb : IsSmoothDrift b) (lam Lam m : ℝ) (hlam : 0 < lam) (hm : 0 < m)
    (hell : HasEverywhereLoewnerBounds lam Lam B)
    (hcoerc : HasUnitDirectionDriftCoercivity m b)
    (T : ℝ) (F : KineticPoint d → ℝ) (hF : Measurable F) (M : ℝ) (hM : 0 ≤ M)
    (hFb : ∀ p, 0 ≤ F p ∧ F p ≤ M)
    (hFz : ∀ p, KineticPoint.equivProd d p ∉ boundedSourcePast Ω γ T → F p = 0) :
    ContinuousOn (duhamelPotential K T F) (evolutionPastOpenCylinder Ω γ T) := by
  classical
  intro p hp
  have hc : ContinuousAt (duhamelPotential K T F) p := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    let δ := min ((T - p.time) / 2) (ε / (16 * (M + 1)))
    have hδ : 0 < δ := lt_min (half_pos (sub_pos.mpr hp.1)) (by positivity)
    have hδT : δ ≤ (T - p.time) / 2 := min_le_left _ _
    have hδε : δ * (16 * (M + 1)) ≤ ε :=
      (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    let s := p.time + δ
    have hps : p.time < s := by dsimp [s]; linarith
    have hsT : s ≤ T := by dsimp [s]; linarith
    let f := {q : KineticPoint d | s < q.time}.indicator F
    let g := {q : KineticPoint d | q.time ≤ s}.indicator F
    have hfm : Measurable f := hF.indicator (measurableSet_lt measurable_const
      continuous_time.measurable)
    have hgm : Measurable g := hF.indicator (measurableSet_le continuous_time.measurable
      measurable_const)
    have hfb : ∀ q, 0 ≤ f q ∧ f q ≤ M := by
      intro q
      by_cases hq : s < q.time
      · simpa only [f, indicator_apply, mem_ofPred_eq, ite_eq_left hq] using hFb q
      · simp only [f, indicator_apply, mem_ofPred_eq, ite_eq_right hq]
        exact ⟨le_rfl, hM⟩
    have hgb : ∀ q, 0 ≤ g q ∧ g q ≤ M := by
      intro q
      by_cases hq : q.time ≤ s
      · simpa only [g, indicator_apply, mem_ofPred_eq, ite_eq_left hq] using hFb q
      · simp only [g, indicator_apply, mem_ofPred_eq, ite_eq_right hq]
        exact ⟨le_rfl, hM⟩
    have hfz : ∀ q, KineticPoint.equivProd d q ∉ boundedSourceFutureSet Ω γ s T →
        f q = 0 := by
      intro q hq
      by_cases hqt : s < q.time
      · have hqpast : KineticPoint.equivProd d q ∉ boundedSourcePast Ω γ T :=
          fun h => hq ⟨hqt, h⟩
        simp only [f, indicator_apply, mem_ofPred_eq, ite_eq_left hqt, hFz q hqpast]
      · simp only [f, indicator_apply, mem_ofPred_eq, ite_eq_right hqt]
    have hgzero : ∀ q : KineticPoint d, s < q.time → g q = 0 := by
      intro q hq
      simp only [g, indicator_apply, mem_ofPred_eq, ite_eq_right (not_le_of_gt hq)]
    have hsplit : F = (fun q => f q + g q) := by
      funext q
      by_cases hq : s < q.time
      · simp only [f, g, indicator_apply, mem_ofPred_eq, ite_eq_left hq,
          ite_eq_right (not_le_of_gt hq), add_zero]
      · simp only [f, g, indicator_apply, mem_ofPred_eq, ite_eq_right hq,
          ite_eq_left (le_of_not_gt hq), zero_add]
    have hfa : ∀ q, |f q| ≤ M := fun q => by
      rw [abs_of_nonneg (hfb q).1]; exact (hfb q).2
    have hga : ∀ q, |g q| ≤ M := fun q => by
      rw [abs_of_nonneg (hgb q).1]; exact (hgb q).2
    have heq (q : KineticPoint d) : duhamelPotential K T F q =
        duhamelPotential K T f q + duhamelPotential K T g q := by
      conv_lhs => rw [hsplit]
      exact duhamelPotential_add_bounded K hΩ hγ f g hfm hgm M M hM hM hfa hga T q
    have hfuture := continuousOn_duhamelFuture_before_source hH hΩa hΩ hγ B b S K hreal
      hB hBs hb lam Lam m hlam hm hell hcoerc s T hsT f hfm M hM hfb hfz
    have hfutureAt := hfuture.continuousAt
      ((isOpen_evolutionPastOpenCylinder (isOpen_of_isAdmissibleEvolutionDomain hΩa)
        hγ s).mem_nhds ⟨hps, hp.2⟩)
    have hnear := hfutureAt.eventually (Metric.ball_mem_nhds _ (half_pos hε))
    have htime := continuous_time.continuousAt.eventually (Metric.ball_mem_nhds p.time hδ)
    filter_upwards [hnear, htime] with q hq hqt
    change dist (duhamelPotential K T f q) (duhamelPotential K T f p) < ε / 2 at hq
    change dist q.time p.time < δ at hqt
    rw [Real.dist_eq] at hq hqt
    have hqtime : q.time ≤ s := by
      have ht := (abs_lt.mp hqt).2
      dsimp only [s]
      linarith
    have hrecent (w : KineticPoint d) (hws : w.time ≤ s) :
        |duhamelPotential K T g w| ≤ (s - w.time) * M := by
      rw [duhamelPotential_eq_short_terminal K g s T hsT hgzero w]
      exact abs_duhamelPotential_le K g M hM hga w s hws
    have hbq : |duhamelPotential K T g q| ≤ 2 * δ * M := by
      have ht := (abs_lt.mp hqt).1
      exact (hrecent q hqtime).trans (mul_le_mul_of_nonneg_right (by dsimp [s]; linarith) hM)
    have hbp : |duhamelPotential K T g p| ≤ δ * M := by
      simpa only [s, add_sub_cancel_left] using hrecent p hps.le
    have habs : |duhamelPotential K T F q - duhamelPotential K T F p| ≤
        |duhamelPotential K T f q - duhamelPotential K T f p| +
          |duhamelPotential K T g q| + |duhamelPotential K T g p| := by
      rw [heq q, heq p]
      have hid (a b c d : ℝ) : (a + b) - (c + d) = (a - c) + (b - d) := by ring
      rw [hid]
      exact (abs_add_le _ _).trans (by
        have hh := abs_sub (duhamelPotential K T g q) (duhamelPotential K T g p)
        linarith)
    rw [Real.dist_eq]
    nlinarith
  exact hc.continuousWithinAt

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
