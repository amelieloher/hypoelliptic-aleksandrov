module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionOperator

/-! # Pointwise recovery of the actual mollified operator at each fixed time -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory Filter
open scoped Topology

/-- The selected full extended source, with the literal backward-operator sign convention. -/
def constructionExtendedSource {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r mu R m : ℝ) (A : XV d → PDE.Mat d)
    (P : KineticPoint d) : ℝ :=
  constructionExtendedTimeJet h r mu R P.time (P.position, P.velocity) +
    PDE.vecDot P.velocity (fun i => constructionExtendedNativeGradient h r mu R m P.time
      (P.position, P.velocity) (Fin.castAdd d i)) -
    matrixContraction (A (P.position, P.velocity)) (fun i k =>
      constructionExtendedNativeHessian h r mu R m P.time (P.position, P.velocity) i k)

/-- At each time the actual smoothed operator converges almost everywhere to the full
source formed from the same selected representatives. -/
theorem construction_smoothed_operator_tendsto_ae {d : ℕ} (hd : 1 ≤ d)
    {alpha : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1)
    (h : CounterProfileStatement d alpha) (r mu R m : ℝ)
    (hr : 0 < r) (hmu : 0 < mu) (hR : 0 < R) (hm : m < R ^ 2)
    (hscale : 2 * Real.rpow r alpha ≤ 1)
    (hmargin : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 ≤ m)
    (A : XV d → PDE.Mat d) (t : ℝ) :
    ∀ᵐ q : XV d ∂volume, Tendsto (fun n => backwardOperator (fun _t x v => A (x, v))
      (smoothedZeroExtendedProfile h r mu R (standardMollifierSequence n)) ⟨t, q.1, q.2⟩)
      atTop (𝓝 (constructionExtendedSource h r mu R m A ⟨t, q.1, q.2⟩)) := by
  have ht := construction_spatialMollify_tendsto_ae _
    (construction_extendedTimeJet_locallyIntegrable h r mu R t)
  filter_upwards [ht, construction_selected_jets_tendsto_ae h r hr mu R m t] with q hqt hq
  have hx := tendsto_finsetSum Finset.univ (fun i _ =>
    (hq.1 (Fin.castAdd d i)).const_mul (q.2 i))
  have hh := tendsto_finsetSum Finset.univ (fun i _ =>
    tendsto_finsetSum Finset.univ (fun k _ => (hq.2 i k).const_mul (A q i k)))
  have he := (hqt.add hx).sub hh
  simp_rw [construction_smoothed_operator_eq hd ha ha1 h r mu R m hr hmu hR hm
    hscale hmargin]
  simpa only [constructionExtendedSource, PDE.vecDot, matrixContraction] using! he

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
