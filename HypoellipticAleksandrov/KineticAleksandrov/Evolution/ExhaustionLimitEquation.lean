module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitRegularity
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitClassical
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitBoundary
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.PastGluingLocality
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExternalRegularity
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitAdjoint
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TruncationWeak
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitMeasure
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Actual smoothness and pointwise viscous equation for the exhaustion candidate -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set Filter MeasureTheory
open Evolution
open scoped Topology MatrixOrder

/-- The actual continuous zero extension is smooth and solves the viscous equation
pointwise on every strict bounded inner cylinder, relative to the explicit Hörmander input. -/
theorem classical_innerBallDirichletLimit_on_innerCylinder
    (hH : HormanderHypoellipticityStatement)
    {n : ℕ} {lam Lam Lb m : ℝ} {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
    (hn : 1 ≤ n) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hm : 0 < m) (hmLb : m ≤ Lb) (hB : HasEverywhereLoewnerBounds lam Lam B)
    (hBs : IsSmoothFullKineticCoefficient B)
    (hBsym : IsSymmetricFullKineticCoefficient B) (hbs : IsSmoothDrift b)
    (hb : HasEuclideanLipschitzDrift Lb b)
    (hbco : HasUnitDirectionDriftCoercivity m b)
    {a α τ r0 δ0 S0 d L C ε : ℝ} (haα : a < α) (hατ : α < τ)
    (hδ0 : 0 < δ0) (hδr : δ0 < r0) (hd : 0 < d) (hdr : d < r0 / 4)
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
    ContDiffOn ℝ (⊤ : ℕ∞) (innerBallDirichletLimit r0 Γ g u ∘ evolutionHomeomorph n)
      (evolutionHomeomorph n ⁻¹' boundedInnerOpenCylinder (r0 - δ0) Γ α τ S0) ∧
    ∀ p ∈ boundedInnerOpenCylinder (r0 - δ0) Γ α τ S0,
      viscousTransportedOperator B b ε (innerBallDirichletLimit r0 Γ g u) p = 0 := by
  let U := boundedInnerOpenCylinder (r0 - δ0) Γ α τ S0
  let vlim (p : KineticPoint n) :=
    limUnder atTop (fun k => straightenedPullback (g k) (u k) p)
  have hU : IsOpen U := isOpen_boundedInnerOpenCylinder _ hΓ.1 _ _ _
  have hV : IsOpen (evolutionHomeomorph n ⁻¹' U) :=
    hU.preimage (evolutionHomeomorph n).continuous
  have hsm := contDiffOn_innerBall_dirichlet_limit (S0 := S0)
    hH hn hlam hlamLam hm hmLb hB hBs hBsym hbs hb hbco haα hατ hδ0 hδr hd hdr
    hL hε hε1 hC hΓ F hFC hsupp β R hβpos hβlim hRlim g hg hgL hclose u hu
  have hw := weakRegularized_innerBall_dirichlet_limit (S0 := S0)
    hn hlam hlamLam hm hmLb hB hBs hBsym hbs hb hbco haα hατ hδ0 hδr hd hdr
    hL hε hε1 hC hΓ F hFC hsupp β R hβpos hβlim hRlim g hg hgL hclose u hu
  have hwPack := (isWeakRegularizedSolution_comp_iff B b ε U vlim (fun _ => 0)).mpr hw
  have heq := regularizedOperator_eq_zero_of_smooth_weak hV hBs hBsym hbs ε hsm hwPack
  have hinside : ∀ p ∈ U, p.position ∈ movingDomain (PDE.euclideanBall 0 r0) Γ p.time :=
    fun p hp => innerClosedCylinder_subset_movingBall hδ0 hδr
      (boundedInnerOpenCylinder_subset_closed _ Γ α τ S0 hp)
  refine ⟨hsm.congr (fun x hx => innerBallDirichletLimit_eq_limit r0 Γ g u
    (hinside _ hx)), ?_⟩
  intro p hp
  have hnear : ∀ᶠ q in 𝓝 p,
      q.position ∈ movingDomain (PDE.euclideanBall 0 r0) Γ q.time :=
    (isOpen_setOf_mem_movingDomain (PDE.isOpen_euclideanBall 0 r0) hΓ.1).mem_nhds
      (hinside p hp)
  have hgerm : innerBallDirichletLimit r0 Γ g u =ᶠ[𝓝 p] vlim :=
    hnear.mono (fun q hq => innerBallDirichletLimit_eq_limit r0 Γ g u hq)
  rw [viscousTransportedOperator_congr_germ B b ε hgerm]
  let x := (evolutionHomeomorph n).symm p
  have hx : x ∈ evolutionHomeomorph n ⁻¹' U := by
    change evolutionHomeomorph n x ∈ U
    simpa only [x, Homeomorph.apply_symm_apply] using hp
  have hc2 : ContDiffAt ℝ 2 (vlim ∘ evolutionHomeomorph n) x :=
    (hsm.contDiffAt (hV.mem_nhds hx)).of_le (by norm_num)
  have hOp := regularizedOperator_comp (B := B) (b := b) ε hc2
  have hz := heq x hx
  rw [hOp] at hz
  simpa only [x, Homeomorph.apply_symm_apply, viscousTransportedOperator] using hz

end HypoellipticAleksandrov.KineticAleksandrov
