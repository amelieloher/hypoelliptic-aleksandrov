module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitUniform
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitMeasure
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Compact-region integral convergence for actual approximants

Dominated convergence uses eventual continuity and the actual finite-domain
maximum-principle bound. No ambient measurability of a Dirichlet extension is assumed.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set Filter MeasureTheory
open scoped Topology MatrixOrder

/-- Integration against any continuous test on a fixed bounded inner cylinder
commutes with the actual Dirichlet exhaustion limit. -/
theorem tendsto_setIntegral_mul_innerBall_dirichlet
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
      (fun x => F (g k τ + spatialY x, spatialZ x)) (fun _ => 0) (u k))
    (φ : KineticPoint n → ℝ) (hφ : Continuous φ) :
    Tendsto (fun k => ∫ p in
      movingClosedSlab (PDE.euclideanBall 0 (r0 - δ0)) Γ α τ ∩
        {p | radialSq p ≤ S0 ^ 2}, straightenedPullback (g k) (u k) p * φ p)
      atTop (𝓝 (∫ p in movingClosedSlab (PDE.euclideanBall 0 (r0 - δ0)) Γ α τ ∩
        {p | radialSq p ≤ S0 ^ 2},
        limUnder atTop (fun k => straightenedPullback (g k) (u k) p) * φ p)) := by
  let K := movingClosedSlab (PDE.euclideanBall 0 (r0 - δ0)) Γ α τ ∩
    {p | radialSq p ≤ S0 ^ 2}
  have hK : IsCompact K := isCompact_movingClosedSlab_inter hΓ α τ S0
  have hU := tendstoUniformlyOn_innerBall_dirichlet (S0 := S0)
    hlam hB hBs hbs hb haα hατ hδ0 hδr hd hdr hL hε hε1 hC hΓ F hFC hsupp
    β R hβpos hβlim hRlim g hg hgL hclose u hu
  have hmem := eventually_innerCylinder_mem_straightenedEllipsoid (S := S0)
    hδ0 hδr β R hβlim hRlim g hclose
  have hclosed (k : ℕ) (hk : 0 < r0 - β k ∧ 0 < R k ∧
      ∀ p ∈ K, (straightenedPoint (g k) p).2 ∈
        openEllipsoid (straightenedEllipsoidMatrix n (r0 - β k) (R k))) :
      MapsTo (straightenedPoint (g k)) K
        (scalarParabolicClosedCylinder a τ
          (openEllipsoid (straightenedEllipsoidMatrix n (r0 - β k) (R k)))) :=
    fun p hp => ⟨⟨haα.le.trans hp.1.1, hp.1.2.1⟩, subset_closure (hk.2.2 p hp)⟩
  apply tendsto_integral_filter_of_dominated_convergence (fun p => C * |φ p|)
  · exact hmem.mono fun k hk => (((hu k).1.comp
      (continuous_straightenedPoint (hg k).continuous).continuousOn (hclosed k hk)).mul
        hφ.continuousOn).aestronglyMeasurable hK.measurableSet
  · refine hmem.mono fun k hk => ?_
    filter_upwards [ae_restrict_mem hK.measurableSet] with p hp
    have hbnd := abs_le_straightened_dirichlet
      hlam hB hBs hbs (haα.trans hατ) hk.1 hk.2.1 (hg k) hε F (u k) (hu k)
      hC hFC _ (hclosed k hk hp)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right hbnd (abs_nonneg _)
  · exact (continuous_const.mul hφ.abs).continuousOn.integrableOn_compact hK
  · filter_upwards [ae_restrict_mem hK.measurableSet] with p hp
    exact (hU.tendsto_at hp).mul tendsto_const_nhds

end HypoellipticAleksandrov.KineticAleksandrov
