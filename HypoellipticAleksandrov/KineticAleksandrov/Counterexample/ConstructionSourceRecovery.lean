module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionJointSource
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionSourceBound

/-! # Spacetime recovery and shell domination of the actual limiting source -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory Filter Set HypoellipticAleksandrov.Parabolic
open scoped Topology

/-- The spacetime indicator uses exactly the fixed-time profile domain. -/
theorem constructionIndicatorSource_apply {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r mu R t : ℝ) (q : XV d) :
    constructionIndicatorSource h r mu R (t, q) =
      {y | profileFunction h y < 1}.indicator
        (fun y => timeCutoffSourceRepresentative h r mu R ⟨t, y.1, y.2⟩) q := by
  by_cases hp : profileFunction h q < 1 <;> simp [constructionIndicatorSource, hp]

/-- The actual mollified operator converges almost everywhere in native spacetime
volume to a jointly measurable version of the selected zero-extended source. -/
theorem construction_smoothedOperator_tendsto_ae_spacetime {d : ℕ} (hd : 1 ≤ d)
    {alpha : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1)
    (h : CounterProfileStatement d alpha) (r mu R m : ℝ)
    (hr : 0 < r) (hmu : 0 < mu) (hR : 0 < R) (hm : m < R ^ 2)
    (hscale : 2 * Real.rpow r alpha ≤ 1)
    (hmargin : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 < m) :
    ∀ᵐ P : KineticPoint d ∂volume, Tendsto (fun n =>
      backwardOperator (fun _t x v => profileMatrix h (x, v))
        (smoothedZeroExtendedProfile h r mu R (standardMollifierSequence n)) P)
      atTop (𝓝 (constructionIndicatorSource h r mu R (KineticPoint.equivProd d P))) := by
  have hA := (selectedProfile_spec h).2.2.2.2.1
  have hF (n : ℕ) := measurable_backwardOperator_of_joint_smooth (profileMatrix h) hA
    (smoothedZeroExtendedProfile h r mu R (standardMollifierSequence n))
    (smoothedZeroExtendedProfile_contDiff ha h r mu R hr hmu hR
      (fun q hq => (hmargin q hq).trans hm) (standardMollifierSequence n))
  have he := construction_fixed_time_tendsto_ae_spacetime
    (fun n z => backwardOperator (fun _t x v => profileMatrix h (x, v))
      (smoothedZeroExtendedProfile h r mu R (standardMollifierSequence n))
      ((KineticPoint.equivProd d).symm z)) (constructionIndicatorSource h r mu R)
    (fun n => (hF n).comp (KineticPoint.measurable_equivProd_symm d))
    (construction_indicatorSource_measurable h r mu R) ?_
  · simpa only [Equiv.symm_apply_apply] using! he
  · intro t
    filter_upwards [construction_smoothed_operator_tendsto_ae hd ha ha1 h r mu R m
      hr hmu hR hm hscale (fun q hq => (hmargin q hq).le) (profileMatrix h) t,
      construction_extendedSource_eq_indicator_ae hd ha ha1 h r mu R m hr hmu hR hm
        hscale hmargin t] with q hq heq
    simpa only [constructionIndicatorSource_apply,
      ← heq] using! hq

/-- Jointly measurable fixed-time almost-everywhere inequalities lift to spacetime. -/
theorem construction_fixed_time_le_ae_spacetime {d : ℕ} (f g : ℝ × XV d → ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (hfg : ∀ t : ℝ, ∀ᵐ q ∂volume, f (t, q) ≤ g (t, q)) :
    ∀ᵐ P : KineticPoint d ∂volume,
      f (KineticPoint.equivProd d P) ≤ g (KineticPoint.equivProd d P) := by
  have hs : MeasurableSet {z | f z ≤ g z} := measurableSet_le hf hg
  have hp : ∀ᵐ z : ℝ × XV d ∂volume, f z ≤ g z :=
    (Measure.ae_prod_iff_ae_ae hs).mpr (Eventually.of_forall hfg)
  exact (KineticPoint.measurePreserving_equivProd d).quasiMeasurePreserving.ae hp

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
