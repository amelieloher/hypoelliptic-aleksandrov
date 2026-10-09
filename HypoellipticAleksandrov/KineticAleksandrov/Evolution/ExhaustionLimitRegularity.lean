module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitWeak
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExternalRegularity
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitAdjoint
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TruncationWeak
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitMeasure
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Pointwise smoothness of the actual exhaustion limit

The explicit Hörmander premise produces a smooth almost-everywhere representative.
Actual limit continuity identifies that representative pointwise on the open cylinder.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set Filter MeasureTheory
open Evolution
open scoped Topology MatrixOrder

/-- Relative to the Hörmander input, the actual Dirichlet
exhaustion limit is smooth on each strict bounded inner cylinder. -/
theorem contDiffOn_innerBall_dirichlet_limit
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
    ContDiffOn ℝ (⊤ : ℕ∞)
      ((fun p => limUnder atTop (fun k => straightenedPullback (g k) (u k) p)) ∘
        evolutionHomeomorph n)
      (evolutionHomeomorph n ⁻¹' boundedInnerOpenCylinder (r0 - δ0) Γ α τ S0) := by
  let U := boundedInnerOpenCylinder (r0 - δ0) Γ α τ S0
  let vlim (p : KineticPoint n) :=
    limUnder atTop (fun k => straightenedPullback (g k) (u k) p)
  have hU : IsOpen U := isOpen_boundedInnerOpenCylinder _ hΓ.1 _ _ _
  have hw := weakRegularized_innerBall_dirichlet_limit (S0 := S0)
    hn hlam hlamLam hm hmLb hB hBs hBsym hbs hb hbco haα hατ hδ0 hδr hd hdr
    hL hε hε1 hC hΓ F hFC hsupp β R hβpos hβlim hRlim g hg hgL hclose u hu
  obtain ⟨v, hvs, hae⟩ := exists_smooth_viscous_kinetic_representative
    hH hlam hBs hB hbs U hU ε hε vlim hw
  have hcLim : ContinuousOn vlim U :=
    (continuousOn_bounded_innerBall_dirichlet_limit (S0 := S0)
      hlam hB hBs hbs hb haα hατ hδ0 hδr hd hdr hL hε.le hε1 hC hΓ.1
      F hFC hsupp β R hβpos hβlim hRlim g hg hgL hclose u hu).1.mono
        (boundedInnerOpenCylinder_subset_closed _ Γ α τ S0)
  have hcPack : ContinuousOn (vlim ∘ evolutionHomeomorph n)
      (evolutionHomeomorph n ⁻¹' U) :=
    hcLim.comp (evolutionHomeomorph n).continuous.continuousOn (fun _ hx => hx)
  have heq := eqOn_of_ae_eq_of_continuousOn_kinetic hU hcPack hvs.continuousOn hae
  exact hvs.congr (fun x hx => heq hx)

end HypoellipticAleksandrov.KineticAleksandrov
