module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitBoundary
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitCover
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionCollarApproximation
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitGeometry
public import Mathlib.Topology.UniformSpace.UniformApproximation

/-! # Exact uniform bound and terminal/lateral traces of the exhaustion candidate -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set Filter
open scoped Topology MatrixOrder

/-- The continuous zero extension has the original uniform bound and terminal
values, and vanishes on the actual moving lateral boundary. -/
theorem innerBallDirichletLimit_bound_terminal_lateral
    {n : ℕ} {lam Lam Lb : ℝ} {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
    (hlam : 0 < lam) (hB : HasEverywhereLoewnerBounds lam Lam B)
    (hBs : IsSmoothFullKineticCoefficient B) (hbs : IsSmoothDrift b)
    (hb : HasEuclideanLipschitzDrift Lb b)
    {a α τ r0 d L C ε : ℝ} (haα : a < α) (hατ : α < τ)
    (hd : 0 < d) (hdr : d < r0 / 4)
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
    (∀ p ∈ movingClosedSlab (PDE.euclideanBall 0 r0) Γ α τ,
      |innerBallDirichletLimit r0 Γ g u p| ≤ C) ∧
    (∀ p ∈ movingClosedSlab (PDE.euclideanBall 0 r0) Γ α τ, p.time = τ →
      innerBallDirichletLimit r0 Γ g u p = F (p.position, p.velocity)) ∧
    (∀ p : KineticPoint n,
      p.position ∈ frontier (movingDomain (PDE.euclideanBall 0 r0) Γ p.time) →
      innerBallDirichletLimit r0 Γ g u p = 0) := by
  have hr0 : 0 < r0 := by linarith
  have hpoint (p : KineticPoint n)
      (hp : p ∈ movingClosedSlab (PDE.euclideanBall 0 r0) Γ α τ)
      (hi : p.position ∈ movingDomain (PDE.euclideanBall 0 r0) Γ p.time) :
      |innerBallDirichletLimit r0 Γ g u p| ≤ C := by
    obtain ⟨δ, S, hδ, hδr, hpK, -⟩ :=
      exists_innerClosedCylinder_mem_nhdsWithin hΓ hr0 hp hi
    rw [innerBallDirichletLimit_eq_limit r0 Γ g u hi]
    exact (continuousOn_bounded_innerBall_dirichlet_limit (S0 := S)
      hlam hB hBs hbs hb haα hατ hδ hδr hd hdr hL hε hε1 hC hΓ
      F hFC hsupp β R hβpos hβlim hRlim g hg hgL hclose u hu).2 p hpK
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    by_cases hi : p.position ∈ movingDomain (PDE.euclideanBall 0 r0) Γ p.time
    · exact hpoint p hp hi
    · simpa only [innerBallDirichletLimit, ite_eq_right hi, abs_zero] using hC
  · intro p hp ht
    by_cases hi : p.position ∈ movingDomain (PDE.euclideanBall 0 r0) Γ p.time
    · obtain ⟨δ, S, hδ, hδr, hpK, -⟩ :=
        exists_innerClosedCylinder_mem_nhdsWithin hΓ hr0 hp hi
      have hU := tendstoUniformlyOn_innerBall_dirichlet (S0 := S)
        hlam hB hBs hbs hb haα hατ hδ hδr hd hdr hL hε hε1 hC hΓ
        F hFC hsupp β R hβpos hβlim hRlim g hg hgL hclose u hu
      have hmem := eventually_innerCylinder_mem_straightenedEllipsoid (S := S)
        hδ hδr β R hβlim hRlim g hclose
      have he : ∀ᶠ k : ℕ in atTop,
          straightenedPullback (g k) (u k) p = F (p.position, p.velocity) := by
        filter_upwards [hmem] with k hk
        have hm := subset_closure (hk.2.2 p hpK)
        simp only [straightenedPoint, ht] at hm
        have het := (hu k).2.2.2.1 _ hm
        simpa only [straightenedPullback, straightenedPoint, ht,
          spatialY_spatialPack, spatialZ_spatialPack, add_sub_cancel] using het
      rw [innerBallDirichletLimit_eq_limit r0 Γ g u hi]
      exact tendsto_nhds_unique (hU.tendsto_at hpK)
        (tendsto_const_nhds.congr' (he.mono fun k hk => hk.symm))
    · have hzero : F (p.position, p.velocity) = 0 := by
        by_contra hne
        have hs := hsupp (p.position, p.velocity)
          (subset_tsupport (F : EvolutionAmbientState n → ℝ) hne)
        have hn := (mem_movingBall_iff_norm_lt hr0).not.mp hi
        rw [ht] at hn
        linarith
      simp only [innerBallDirichletLimit, ite_eq_right hi, hzero]
  · intro p hp
    have hnot : p.position ∉ movingDomain (PDE.euclideanBall 0 r0) Γ p.time :=
      by
        have hopen := isOpen_movingDomain (γ := Γ) (PDE.isOpen_euclideanBall 0 r0) p.time
        change p.position ∈ closure _ ∧ p.position ∉ interior _ at hp
        simpa only [hopen.interior_eq] using hp.2
    exact ite_eq_right hnot

end HypoellipticAleksandrov.KineticAleksandrov
