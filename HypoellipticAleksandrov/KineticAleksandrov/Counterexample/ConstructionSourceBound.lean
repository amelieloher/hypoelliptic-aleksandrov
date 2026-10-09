module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionSourceIdentity

/-! # Positive extended sources are controlled by the literal stationary shell source -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory Set

/-- The positive part of the full selected source is bounded by the literal flattened shell
source on `H < 1` and vanishes outside that domain, at every fixed time. -/
theorem construction_extended_positive_source_le_shell_ae {d : ℕ} (hd : 1 ≤ d)
    {alpha : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1)
    (h : CounterProfileStatement d alpha) (r mu R m : ℝ)
    (hr : 0 < r) (hmu : 0 < mu) (hR : 0 < R) (hm : m < R ^ 2)
    (hrate : mu = (d : ℝ) * profileLowerEllipticity h / R ^ 2)
    (hscale : 2 * Real.rpow r alpha ≤ 1)
    (hmargin : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 < m) (t : ℝ) :
    ∀ᵐ q : XV d ∂volume,
      max (constructionExtendedSource h r mu R m (profileMatrix h) ⟨t, q.1, q.2⟩) 0 ≤
        {y | profileFunction h y < 1}.indicator
          (flatSource (profileMatrix h) (profileFunction h) flatteningPsi alpha r) q := by
  have he := construction_extendedSource_eq_indicator_ae hd ha ha1 h r mu R m
    hr hmu hR hm hscale hmargin t
  have hb := timeCutoff_source_le_of_profile hd h r hr R hR t
  have hn := flatSource_nonneg_ae_of_profile h r hr
  filter_upwards [he, hb, hn] with q hq hbq hnq
  rw [hq]
  by_cases hprof : q ∈ {y | profileFunction h y < 1}
  · rw [indicator_of_mem hprof, indicator_of_mem hprof]
    rw [hrate]
    exact max_le hbq hnq
  · rw [indicator_of_notMem hprof, indicator_of_notMem hprof, max_self]

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
