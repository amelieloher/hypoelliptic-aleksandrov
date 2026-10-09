module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TerminalMomentBoundsKernel
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic

/-! # Compact polynomial truncation and kernel comparison

Actual smooth compact terminal tests converge pointwise to the polynomial.
Fatou passes their uniform comparison bound to the extended terminal integral.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set MeasureTheory Filter
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal Topology

/-- A smooth polynomial times the conservation cutoff is an actual bounded datum. -/
def momentCutoff (g : EvolutionAmbientState 1 → ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (N : ℕ) : BoundedBorel (EvolutionAmbientState 1) := by
  have hs := hg.mul (conservationDatum_smoothCompact N 0).1
  have hc : HasCompactSupport (fun x => g x * conservationDatum N x) :=
    (conservationDatum_smoothCompact N 0).2.1.mul_left
  refine ⟨fun x => g x * conservationDatum N x, hs.continuous.measurable, ?_⟩
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hs.continuous
  exact ⟨max C 0, le_max_right _ _, fun x =>
    (show |g x * conservationDatum N x| ≤ C from
      by simpa only [Real.norm_eq_abs] using hC x).trans (le_max_left _ _)⟩

/-- The compact polynomial truncation is admitted by the realization. -/
theorem momentCutoff_smoothCompact (g : EvolutionAmbientState 1 → ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (N : ℕ) (tau : ℝ) :
    IsSmoothCompactTerminalDatum autonomousWholeDomain (fun _ => 0) tau
      (momentCutoff g hg N) := by
  refine ⟨hg.mul (conservationDatum_smoothCompact N tau).1,
    (conservationDatum_smoothCompact N tau).2.1.mul_left, ?_⟩
  exact tsupport_mul_subset_right.trans (conservationDatum_smoothCompact N tau).2.2

/-- Each fixed point eventually lies in the unit region of both coordinate cutoffs. -/
theorem conservationDatum_eventually_one (x : EvolutionAmbientState 1) :
    ∀ᶠ N : ℕ in atTop, conservationDatum N x = 1 := by
  have h1 : ∀ᶠ N : ℕ in atTop, ‖x.1‖ ≤ (N : ℝ) + 1 :=
    (tendsto_natCast_atTop_atTop.eventually_ge_atTop ‖x.1‖).mono fun N h => by linarith
  have h2 : ∀ᶠ N : ℕ in atTop, ‖x.2‖ ≤ (N : ℝ) + 1 :=
    (tendsto_natCast_atTop_atTop.eventually_ge_atTop ‖x.2‖).mono fun N h => by linarith
  filter_upwards [h1, h2] with N hN1 hN2
  change zCutoffN 1 N x.1 * zCutoffN 1 N x.2 = 1
  rw [zCutoffN_eq_one hN1, zCutoffN_eq_one hN2, one_mul]

/-- Comparison bounds the integral of every actual compact polynomial test. -/
theorem momentCutoff_integral_le {lam Lam : ℝ} (hlam : 0 < lam)
    (A : SmoothAutonomous lam Lam) (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E)
    (g : EvolutionAmbientState 1 → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (W : Point → ℝ) (hc : Continuous W) (hr : ∀ p, IsSliceRegularAt W p)
    (tau : ℝ) (hn : ∀ p, p.time ≤ tau → 0 ≤ W p)
    (hop : ∀ p, p.time ≤ tau →
      transportedForwardOperator (evolutionCoefficient A.a) (identityDrift 1) W p ≤ 0)
    (ht : ∀ p, p.time = tau → g (p.position, p.velocity) = W p)
    (q : EvolutionQuery autonomousWholeDomain (fun _ => 0)) (hq : q.1.2.1 = tau) (N : ℕ) :
    ∫ x, momentCutoff g hg N x ∂E.2.master q ≤
      W ⟨q.1.1, q.1.2.2.1, q.1.2.2.2⟩ := by
  obtain ⟨u, hu, hrep, -⟩ := hE.1 tau (momentCutoff g hg N)
    (momentCutoff_smoothCompact g hg N tau)
  let state : EvolutionState autonomousWholeDomain (fun _ => 0) q.1.1 :=
    ⟨q.1.2.2, q.2.2⟩
  have horder : q.1.1 ≤ tau := hq ▸ q.2.1
  have he := integral_master_eq_fiber E.2 autonomousWholeDomain_measurable
    q.1.1 tau horder state (momentCutoff g hg N) (momentCutoff g hg N).measurable
  have hi := hE.2.1 q.1.1 tau horder state (terminalStateDatum (momentCutoff g hg N))
  have huq : u ⟨q.1.1, q.1.2.2.1, q.1.2.2.2⟩ =
      ∫ x, momentCutoff g hg N x ∂E.2.master q := by
    have hquery : evolutionQueryOfState autonomousWholeDomain (fun _ => 0)
        q.1.1 tau horder state = q := by
      apply Subtype.ext
      change (q.1.1, tau, q.1.2.2) = q.1
      rw [← hq]
    rw [hquery] at he
    exact (hrep q.1.1 horder state).trans (hi.trans he.symm)
  rw [← huq]
  apply terminal_polynomial_comparison hlam A tau _ u W hu hc hr hn hop
    (fun p hp => ?_) _ horder
  change g (p.position, p.velocity) * conservationDatum N (p.position, p.velocity) ≤ W p
  rw [ht p hp]
  exact (mul_le_mul_of_nonneg_left (conservationDatum_bounds N _).2 (hn p hp.le)).trans
    (by rw [mul_one])

/-- Fatou transfers compact polynomial comparison to the unbounded terminal moment. -/
theorem terminal_polynomial_lintegral_le {lam Lam : ℝ} (hlam : 0 < lam)
    (A : SmoothAutonomous lam Lam) (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E)
    (g : EvolutionAmbientState 1 → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hg0 : ∀ x, 0 ≤ g x)
    (W : Point → ℝ) (hc : Continuous W) (hr : ∀ p, IsSliceRegularAt W p)
    (tau : ℝ) (hn : ∀ p, p.time ≤ tau → 0 ≤ W p)
    (hop : ∀ p, p.time ≤ tau →
      transportedForwardOperator (evolutionCoefficient A.a) (identityDrift 1) W p ≤ 0)
    (ht : ∀ p, p.time = tau → g (p.position, p.velocity) = W p)
    (q : EvolutionQuery autonomousWholeDomain (fun _ => 0)) (hq : q.1.2.1 = tau) :
    (∫⁻ x, ENNReal.ofReal (g x) ∂E.2.master q) ≤
      ENNReal.ofReal (W ⟨q.1.1, q.1.2.2.1, q.1.2.2.2⟩) := by
  let f := fun N x => ENNReal.ofReal (momentCutoff g hg N x)
  have hlim (x) : liminf (fun N => f N x) atTop = ENNReal.ofReal (g x) := by
    have he : (fun N => f N x) =ᶠ[atTop] fun _ => ENNReal.ofReal (g x) := by
      filter_upwards [conservationDatum_eventually_one x] with N hN
      change ENNReal.ofReal (g x * conservationDatum N x) = _
      rw [hN, mul_one]
    rw [Filter.liminf_congr he, liminf_const]
  rw [← lintegral_congr hlim]
  apply (lintegral_liminf_le (fun N => (momentCutoff g hg N).measurable.ennreal_ofReal)).trans
  refine liminf_le_of_frequently_le ?_ (by isBoundedDefault)
  apply (Filter.Eventually.of_forall (fun N => ?_)).frequently
  let : IsFiniteMeasure (E.2.master q) :=
    ⟨(E.2.mass_le_one q).trans_lt ENNReal.one_lt_top⟩
  have hfi : Integrable (momentCutoff g hg N) (E.2.master q) :=
    boundedBorel_integrable (momentCutoff g hg N) _
  rw [← ofReal_integral_eq_lintegral_ofReal hfi (Filter.Eventually.of_forall
    (fun x => by
      change 0 ≤ g x * conservationDatum N x
      exact mul_nonneg (hg0 x) (conservationDatum_bounds N x).1))]
  exact ENNReal.ofReal_le_ofReal (momentCutoff_integral_le hlam A E hE g hg W hc hr
    tau hn hop ht q hq N)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
