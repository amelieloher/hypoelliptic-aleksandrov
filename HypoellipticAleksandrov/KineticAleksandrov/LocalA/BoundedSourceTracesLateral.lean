module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceBarrierMeasure

/-! # Uniform lateral traces for bounded signed sources

The source-independent quadratic barrier proves the zero lateral limit, including
sources that touch the velocity boundary.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set Filter Evolution
open scoped Topology

/-- The diffused quadratic vanishes on the actual Euclidean ball frontier. -/
theorem boundedSourceQuadratic_eq_zero_of_frontier {d : ℕ} (c : PDE.Vec d) (R lam : ℝ)
    (p : KineticPoint d) (hp : p.position ∈ frontier (PDE.euclideanBall c R)) :
    boundedSourceQuadratic c R lam p = 0 := by
  rw [(PDE.isOpen_euclideanBall c R).frontier_eq] at hp
  have hs : closure (PDE.euclideanBall c R) ⊆
      {y : PDE.Vec d | PDE.vecNormSq (y - c) ≤ R ^ 2} := by
    apply closure_minimal
    · intro y hy
      change PDE.vecNormSq (y - c) < R ^ 2 at hy
      exact hy.le
    · exact isClosed_le (contDiff_vecNormSq_sub c).continuous continuous_const
  have hlo := hs hp.1
  have hhi : R ^ 2 ≤ PDE.vecNormSq (p.position - c) := by
    apply le_of_not_gt
    exact hp.2
  have heq := le_antisymm hlo hhi
  simp only [boundedSourceQuadratic, heq, sub_self, zero_div]

/-- The bounded signed potential is continuous with value zero at the lateral frontier. -/
theorem continuousWithinAt_duhamelPotential_bounded_lateral
    (hH : HormanderHypoellipticityStatement) {d : ℕ} (hd : 0 < d)
    {c : PDE.Vec d} {R : ℝ} (hR : 0 < R) {lam Lam m Lb : ℝ}
    (hlam : 0 < lam) (hm : 0 < m)
    (B : FullKineticCoefficient d) (hB : IsSmoothFullKineticCoefficient B)
    (hBs : IsSymmetricFullKineticCoefficient B)
    (hell : HasEverywhereLoewnerBounds lam Lam B)
    (b : PDE.Vec d → PDE.Vec d) (hb : IsSmoothDrift b)
    (hbounds : HasTransportBounds m Lb b)
    (S : TerminalOperatorFamily (PDE.euclideanBall c R) (fun _ => 0))
    (K : MovingFiberKernel (PDE.euclideanBall c R) (fun _ => 0))
    (hreal : RealizesTerminalEvolution (PDE.euclideanBall c R) (fun _ => 0)
      (PDE.isOpen_euclideanBall c R).measurableSet B b S K)
    (g : KineticPoint d → ℝ) (hg : Measurable g) (M : ℝ) (hM : 0 ≤ M)
    (hgb : ∀ q, |g q| ≤ M) (T : ℝ) (p : KineticPoint d)
    (_hp : p ∈ evolutionPastClosedCylinder (PDE.euclideanBall c R) (fun _ => 0) T)
    (hfront : p.position ∈ frontier (PDE.euclideanBall c R)) :
    ContinuousWithinAt (duhamelPotential K T g)
      (evolutionPastClosedCylinder (PDE.euclideanBall c R) (fun _ => 0) T) p := by
  have hQ0 := boundedSourceQuadratic_eq_zero_of_frontier c R lam p hfront
  have hWp : duhamelPotential K T g p = 0 := by
    apply duhamelPotential_eq_zero_of_not_mem
    rw [boundedSource_stationary_domain]
    rw [(PDE.isOpen_euclideanBall c R).frontier_eq] at hfront
    exact hfront.2
  rw [ContinuousWithinAt, hWp]
  apply tendsto_zero_iff_norm_tendsto_zero.2
  have hQ : Continuous (fun q : KineticPoint d => boundedSourceQuadratic c R lam q * M) :=
    (continuous_boundedSourceQuadratic c R lam).mul continuous_const
  have hQt : Tendsto (fun q => boundedSourceQuadratic c R lam q * M)
      (𝓝[evolutionPastClosedCylinder (PDE.euclideanBall c R) (fun _ => 0) T] p) (𝓝 0) := by
    simpa only [hQ0, zero_mul] using (hQ.continuousAt (x := p)).continuousWithinAt.tendsto
  apply squeeze_zero' (Eventually.of_forall fun q => norm_nonneg _) ?_ hQt
  filter_upwards [self_mem_nhdsWithin] with q hq
  rw [Real.norm_eq_abs]
  exact abs_duhamelPotential_le_boundedSourceQuadratic hH hd hR hlam hm B hB hBs hell
    b hb hbounds S K hreal g hg M hM hgb T q hq

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
