module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitEquation
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitTrace
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.PastGluingFinite
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitClassical
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitBoundary
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.PastGluingLocality
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExternalRegularity
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitAdjoint
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TruncationWeak
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitMeasure
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Actual finite-slab classical ball solutions

All finite-slab steps are supplied by the actual exhaustion construction:
bounds, continuity, interior smoothness, the pointwise equation, and both traces.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set Filter MeasureTheory
open Evolution
open scoped Topology MatrixOrder

/-- Actual finite ball approximants yield a classical finite-slab solution relative
to the explicit Hörmander input. No boundary estimate or weak equation is assumed. -/
theorem isClassicalViscousFiniteSolution_innerBallDirichletLimit
    (hH : HormanderHypoellipticityStatement)
    {n : ℕ} {lam Lam Lb m : ℝ} {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
    (hn : 1 ≤ n) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hm : 0 < m) (hmLb : m ≤ Lb) (hB : HasEverywhereLoewnerBounds lam Lam B)
    (hBs : IsSmoothFullKineticCoefficient B)
    (hBsym : IsSymmetricFullKineticCoefficient B) (hbs : IsSmoothDrift b)
    (hb : HasEuclideanLipschitzDrift Lb b)
    (hbco : HasUnitDirectionDriftCoercivity m b)
    {a α τ r0 d L C ε : ℝ} (haα : a < α) (hατ : α < τ)
    (hd : 0 < d) (hdr : d < r0 / 4)
    (hL : 0 ≤ L) (hε : 0 < ε) (hε1 : ε ≤ 1) (hC : 0 ≤ C)
    {Γ : ℝ → PDE.Vec n} (hΓ : IsContinuousPiecewiseC1 Γ)
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
    IsClassicalViscousFiniteSolution (PDE.euclideanBall 0 r0) Γ B b ε α τ F
      (innerBallDirichletLimit r0 Γ g u) := by
  have hr0 : 0 < r0 := by linarith
  have htrace := innerBallDirichletLimit_bound_terminal_lateral
    hlam hB hBs hbs hb haα hατ hd hdr hL hε.le hε1 hC hΓ.1
    F hFC hsupp β R hβpos hβlim hRlim g hg hgL hclose u hu
  have hcont := continuousOn_innerBallDirichletLimit
    hlam hB hBs hbs hb haα hατ hd hdr hL hε.le hε1 hC hΓ.1
    F hFC hsupp β R hβpos hβlim hRlim g hg hgL hclose u hu
  have hlocal (δ S : ℝ) (hδ : 0 < δ) (hδr : δ < r0) :=
    classical_innerBallDirichletLimit_on_innerCylinder (S0 := S)
      hH hn hlam hlamLam hm hmLb hB hBs hBsym hbs hb hbco haα hατ hδ hδr hd hdr
      hL hε hε1 hC hΓ F hFC hsupp β R hβpos hβlim hRlim g hg hgL hclose u hu
  refine ⟨⟨C, hC, htrace.1⟩, hcont, ?_, ?_, ?_, ?_⟩
  · intro q hq
    let p : KineticPoint n := ⟨q.1, q.2.1, q.2.2⟩
    obtain ⟨δ, S, hδ, hδr, hp⟩ := exists_boundedInnerOpenCylinder_mem hr0
      (p := p) ⟨hq.1, hq.2.1⟩ hq.2.2
    let x := (evolutionProdCLE n).symm q
    have hxp : evolutionHomeomorph n x = p := by
      apply (KineticPoint.equivProd n).injective
      change (evolutionProdCLE n) ((evolutionProdCLE n).symm q) = q
      exact (evolutionProdCLE n).apply_symm_apply q
    have hx : x ∈ evolutionHomeomorph n ⁻¹'
        boundedInnerOpenCylinder (r0 - δ) Γ α τ S := by
      change evolutionHomeomorph n x ∈ boundedInnerOpenCylinder (r0 - δ) Γ α τ S
      rw [hxp]
      exact hp
    have hV := (isOpen_boundedInnerOpenCylinder (r0 - δ) hΓ.1 α τ S).preimage
      (evolutionHomeomorph n).continuous
    have hc := ((hlocal δ S hδ hδr).1.contDiffAt (hV.mem_nhds hx)).comp q
      (evolutionProdCLE n).symm.contDiff.contDiffAt
    have hfun : (innerBallDirichletLimit r0 Γ g u ∘ evolutionHomeomorph n) ∘
        (evolutionProdCLE n).symm = fun q =>
          innerBallDirichletLimit r0 Γ g u ⟨q.1, q.2.1, q.2.2⟩ := by
      funext q
      change innerBallDirichletLimit r0 Γ g u
        (evolutionHomeomorph n ((evolutionProdCLE n).symm q)) =
        innerBallDirichletLimit r0 Γ g u ⟨q.1, q.2.1, q.2.2⟩
      apply congrArg (innerBallDirichletLimit r0 Γ g u)
      apply (KineticPoint.equivProd n).injective
      change (evolutionProdCLE n) ((evolutionProdCLE n).symm q) = q
      exact (evolutionProdCLE n).apply_symm_apply q
    simpa only [hfun] using hc.contDiffWithinAt
  · intro p hp ha
    obtain ⟨δ, S, hδ, hδr, hpU⟩ := exists_boundedInnerOpenCylinder_mem hr0
      ⟨ha, hp.2.1⟩ hp.2.2
    exact (hlocal δ S hδ hδr).2 p hpU
  · intro p hp
    have hpc : p ∈ movingClosedSlab (PDE.euclideanBall 0 r0) Γ α τ :=
      ⟨by rw [hp.1]; exact hατ.le, hp.1.le, by simpa only [hp.1] using hp.2⟩
    exact htrace.2.1 p hpc hp.1
  · intro p _ hp
    exact htrace.2.2 p hp

end HypoellipticAleksandrov.KineticAleksandrov
