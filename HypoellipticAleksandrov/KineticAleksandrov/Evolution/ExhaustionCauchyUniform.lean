module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionCauchyParameters
public import Mathlib.Topology.MetricSpace.Cauchy

/-!
# Uniform Cauchy convergence of actual finite Dirichlet solutions

The common-cylinder estimate is applied after fixing the error parameters. All
analytic hypotheses concern actual finite solutions; no Cauchy bound is assumed.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set Filter
open scoped Topology MatrixOrder

/-- Actual finite ellipsoid approximants are uniformly Cauchy on every bounded inner
cylinder. The transported radii only need to tend to infinity. -/
theorem uniformCauchySeqOn_innerBall_dirichlet
    {n : ℕ} {lam Lam Lb : ℝ} {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
    (hlam : 0 < lam) (hB : HasEverywhereLoewnerBounds lam Lam B)
    (hBs : IsSmoothFullKineticCoefficient B) (hbs : IsSmoothDrift b)
    (hb : HasEuclideanLipschitzDrift Lb b)
    {a α τ r0 δ0 S0 d L C ε : ℝ} (haα : a < α) (hατ : α < τ)
    (hδ0 : 0 < δ0) (hδr : δ0 < r0) (hd : 0 < d) (hdr : d < r0 / 4)
    (hL : 0 ≤ L) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hC : 0 ≤ C)
    {Γ : ℝ → PDE.Vec n} (hΓ : Continuous Γ)
    (F : BoundedBorel (EvolutionAmbientState n)) (hFC : ∀ q, |F q| ≤ C)
    (hsupp : ∀ q ∈ tsupport (F : EvolutionAmbientState n → ℝ),
      4 * d ≤ r0 - PDE.vecEuclideanNorm (q.1 - Γ τ))
    (β R : ℕ → ℝ) (hβpos : ∀ k, 0 < β k)
    (hβlim : Tendsto β atTop (𝓝 0)) (hRlim : Tendsto R atTop atTop)
    (g : ℕ → ℝ → PDE.Vec n) (hg : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (g k))
    (hgL : ∀ k s t, PDE.vecEuclideanNorm (g k s - g k t) ≤ L * |s - t|)
    (hclose : ∀ k s, s ∈ Icc α τ → PDE.vecEuclideanNorm (g k s - Γ s) ≤ β k / 2)
    (u : ℕ → TimeVelocity (n + n) → ℝ)
    (hu : ∀ k, IsClassicalBackwardDirichletSolution a τ
      (openEllipsoid (straightenedEllipsoidMatrix n (r0 - β k) (R k)))
      (straightenedCoefficient B (g k) ε) (straightenedDrift b (g k))
      (fun _ _ => 0) (fun _ _ => 0)
      (fun x => F (g k τ + spatialY x, spatialZ x)) (fun _ => 0) (u k)) :
    UniformCauchySeqOn (fun k => straightenedPullback (g k) (u k)) atTop
      (movingClosedSlab (PDE.euclideanBall 0 (r0 - δ0)) Γ α τ ∩
        {p | radialSq p ≤ S0 ^ 2}) := by
  let K := movingClosedSlab (PDE.euclideanBall 0 (r0 - δ0)) Γ α τ ∩
    {p | radialSq p ≤ S0 ^ 2}
  let cg := growthConstant n Lam (PDE.vecEuclideanNorm (b 0)) Lb
  obtain ⟨M0, hM0⟩ := (isCompact_movingClosedSlab_inter
    (Ω := PDE.euclideanBall 0 (r0 - δ0)) hΓ α τ S0).bddAbove_image
    (continuous_growthBarrier cg τ).continuousOn
  let M := max M0 0
  have hM : 0 ≤ M := le_max_right _ _
  have hΦ : ∀ p ∈ K, growthBarrier cg τ p ≤ M :=
    fun p hp => (hM0 ⟨p, hp, rfl⟩).trans (le_max_left _ _)
  apply Metric.uniformCauchySeqOn_iff.mpr
  intro e he
  obtain ⟨δ, A, S, hδ, hδδ0, hδr0, hA, hAd, hgap, hS, herr⟩ :=
    exists_small_dirichlet_comparison_parameters
      (div_pos (by linarith : 0 < 1 + L) hlam) hd hδ0
      (by linarith : 0 < r0) hC hM he S0
  obtain ⟨R0, -, hcompare⟩ := exists_transportedRadius_dirichlet_cauchy_bound
    hlam hB hBs hbs hb haα hατ hA.le hAd hgap hδr0 hd hdr hL hε hε1 hC
    hΓ F hFC hsupp
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((hβlim.eventually (gt_mem_nhds hA)).and
      (hRlim.eventually (eventually_ge_atTop R0)))
  refine ⟨N, ?_⟩
  intro k hk l hl p hp
  let j (i : Fin 2) := if i = 0 then k else l
  have hj (i : Fin 2) : N ≤ j i := by dsimp [j]; split_ifs <;> assumption
  have hp' : p ∈ movingClosedSlab (PDE.euclideanBall 0 (r0 - δ)) Γ α τ ∩
      {p | radialSq p ≤ S ^ 2} := by
    refine ⟨⟨hp.1.1, hp.1.2.1, ?_⟩, (show radialSq p ≤ S0 ^ 2 from hp.2).trans hS⟩
    apply mem_closure_movingDomain_iff.mpr
    apply closure_mono (PDE.euclideanBall_mono (by linarith : 0 ≤ r0 - δ0)
      (by linarith : r0 - δ0 ≤ r0 - δ))
    exact mem_closure_movingDomain_iff.mp hp.1.2.2
  have he' := hcompare (fun i => β (j i)) (fun i => R (j i))
    (fun i => ⟨hβpos _, (hN _ (hj i)).1.le⟩) (fun i => (hN _ (hj i)).2)
    (fun i => g (j i)) (fun i => hg _) (fun i => hgL _)
    (fun i => hclose _) (fun i => u (j i)) (fun i => hu _) p hp'
  have hbound : growthBarrier cg τ p / (1 + S ^ 2) ≤ M / (1 + S ^ 2) :=
    div_le_div_of_nonneg_right (hΦ p hp) (by positivity)
  have hfinal := he'.trans_lt ((mul_le_mul_of_nonneg_left
    (add_le_add hbound (le_refl _)) (by positivity)).trans_lt herr)
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simpa only [j, ite_true, h10, ite_false, Real.dist_eq] using hfinal

end HypoellipticAleksandrov.KineticAleksandrov
