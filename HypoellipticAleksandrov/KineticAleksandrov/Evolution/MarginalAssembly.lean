module

import Mathlib.Tactic.Linarith
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Realization
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.MarginalOperator
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.MarginalRegularity

/-!
# Assembly of the parabolic marginal package (Proposition 2.1)

The final marginal conjunct (`SectionTwo.HasParabolicMarginalBundle`) for a moving fiber
kernel `K` whose master measures are the terminal measures `μ q` (the master kernel `K₀` is
such a kernel by definition).  The ten subclauses come from

* marginal independence: `parabolicMarginalKernel_eq_fiberFirstMarginal_of_master_eq`;
* the marginal operators `marginalOperators` (the shared `Q₀`: operator integral, positivity,
  contraction);
* joint measurability `measurable_parabolicMarginalAmbientMeasure` (joint Borel);
* the endpoint (`terminalFiberKernel_self`), giving the endpoint identity of the marginal kernel
  and `Q σ σ = id`;
* Chapman-Kolmogorov for the marginal kernels (and for `Q`) from the Chapman-Kolmogorov identity of
  the fiber kernel `K.HasComposition` (Proposition 2.1, composition), the marginal independence
  at the intermediate state and the first-coordinate push-forward;
* `exists_classical_terminalMarginal_of_master_eq` (the full scalar solution with the shared
  `V`, representation through `Q` and uniqueness).
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic MeasureTheory Set
open scoped ENNReal ProbabilityTheory

section EvolutionData

variable (n : ℕ) (hn : 1 ≤ n) (lam Lam m L_b : ℝ)
variable (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
variable (hm : 0 < m) (hmLb : m ≤ L_b)
variable (Ω : Set (PDE.Vec n)) (γ : ℝ → PDE.Vec n)
variable (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n)
variable (hΩ : IsAdmissibleEvolutionDomain Ω)
variable (hγ : IsContinuousPiecewiseC1 γ)
variable (hB_smooth : IsSmoothFullKineticCoefficient B)
variable (hB_symm : IsSymmetricFullKineticCoefficient B)
variable (hB_ell : HasEverywhereLoewnerBounds lam Lam B)
variable (hb_smooth : IsSmoothDrift b)
variable (hb_lipschitz : HasEuclideanLipschitzDrift L_b b)
variable (hb_coercive : HasUnitDirectionDriftCoercivity m b)
variable (hEx : ClassicalTerminalExistence Ω γ B b)
include hn hlam hlamLam hm hmLb hΩ hγ hB_smooth hB_symm hB_ell
include hb_smooth hb_lipschitz hb_coercive hEx

local notation "μ" => terminalMeasure n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
local notation "κ" => terminalFiberKernel n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx

/-- The fiber kernel of a moving fiber kernel with master measures `μ q` is `κ`. -/
theorem fiberKernel_eq_terminalFiberKernel_of_master_eq
    (K : MovingFiberKernel Ω γ) (hK : ∀ q, K.master q = μ q) (σ τ : ℝ) (hστ : σ ≤ τ) :
    K.fiberKernel (measurableSet_of_isAdmissibleEvolutionDomain hΩ) σ τ hστ = κ σ τ hστ := by
  refine ProbabilityTheory.Kernel.ext fun p => ?_
  rw [MovingFiberKernel.fiberKernel_apply, hK]
  rfl

/-- Endpoint identity of the fiber kernel for a kernel with master measures `μ q`. -/
theorem hasEndpoint_of_master_eq (K : MovingFiberKernel Ω γ) (hK : ∀ q, K.master q = μ q) :
    K.HasEndpoint (measurableSet_of_isAdmissibleEvolutionDomain hΩ) := fun σ => by
  rw [fiberKernel_eq_terminalFiberKernel_of_master_eq n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ
    B b hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx K hK]
  exact terminalFiberKernel_self n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx σ

/-- Endpoint identity of the scalar marginal kernel (clause 8). -/
theorem parabolicMarginalKernel_self_of_master_eq
    (K : MovingFiberKernel Ω γ) (hK : ∀ q, K.master q = μ q) (σ : ℝ) :
    parabolicMarginalKernel K (measurableSet_of_isAdmissibleEvolutionDomain hΩ) σ σ le_rfl =
      (ProbabilityTheory.Kernel.id :
        ProbabilityTheory.Kernel (EvolutionPosition Ω γ σ) (EvolutionPosition Ω γ σ)) := by
  refine ProbabilityTheory.Kernel.ext fun y => ?_
  have hE := hasEndpoint_of_master_eq n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx K hK σ
  rw [parabolicMarginalKernel_apply, MovingFiberKernel.fiberFirstMarginal,
    ProbabilityTheory.Kernel.map_apply _ (MovingFiberKernel.measurable_firstPosition Ω γ σ), hE,
    ProbabilityTheory.Kernel.id_apply, ProbabilityTheory.Kernel.id_apply]
  exact Measure.map_dirac' (MovingFiberKernel.measurable_firstPosition Ω γ σ)
    (positionStateZero Ω γ σ y)

/-- Chapman-Kolmogorov for the scalar marginal kernels (clause 9), from the Chapman-Kolmogorov
identity `hComp` of the fiber kernel and the marginal independence. -/
theorem parabolicMarginalKernel_comp_of_master_eq
    (K : MovingFiberKernel Ω γ) (hK : ∀ q, K.master q = μ q)
    (hBz : ∀ (σ : ℝ) (y z z' : PDE.Vec n), B σ y z = B σ y z')
    (hComp : K.HasComposition (measurableSet_of_isAdmissibleEvolutionDomain hΩ))
    (σ r τ : ℝ) (hσr : σ ≤ r) (hrτ : r ≤ τ) :
    parabolicMarginalKernel K (measurableSet_of_isAdmissibleEvolutionDomain hΩ)
        σ τ (hσr.trans hrτ) =
      parabolicMarginalKernel K (measurableSet_of_isAdmissibleEvolutionDomain hΩ) r τ hrτ ∘ₖ
        parabolicMarginalKernel K (measurableSet_of_isAdmissibleEvolutionDomain hΩ) σ r hσr := by
  refine ProbabilityTheory.Kernel.ext fun y => Measure.ext fun s hs => ?_
  have hfirst : ∀ ρ : ℝ, Measurable (MovingFiberKernel.firstPosition Ω γ ρ) :=
    MovingFiberKernel.measurable_firstPosition Ω γ
  have hind : ∀ x : EvolutionState Ω γ r,
      parabolicMarginalKernel K (measurableSet_of_isAdmissibleEvolutionDomain hΩ) r τ hrτ
          (MovingFiberKernel.firstPosition Ω γ r x) =
        K.fiberFirstMarginal (measurableSet_of_isAdmissibleEvolutionDomain hΩ) r τ hrτ x := by
    intro x
    have := parabolicMarginalKernel_eq_fiberFirstMarginal_of_master_eq n hn lam Lam m L_b hlam
      hlamLam hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive
      hEx K hK hBz r τ hrτ (MovingFiberKernel.firstPosition Ω γ r x) x.1.2
    exact this
  rw [ProbabilityTheory.Kernel.comp_apply' _ _ _ hs]
  rw [parabolicMarginalKernel_apply, MovingFiberKernel.fiberFirstMarginal,
    ProbabilityTheory.Kernel.map_apply _ (hfirst τ), Measure.map_apply (hfirst τ) hs,
    hComp σ r τ hσr hrτ, ProbabilityTheory.Kernel.comp_apply' _ _ _ (hfirst τ hs)]
  have hmeas : Measurable fun y' : EvolutionPosition Ω γ r =>
      parabolicMarginalKernel K (measurableSet_of_isAdmissibleEvolutionDomain hΩ) r τ hrτ y' s :=
    (parabolicMarginalKernel K (measurableSet_of_isAdmissibleEvolutionDomain hΩ)
      r τ hrτ).measurable_coe hs
  have hmarg : parabolicMarginalKernel K (measurableSet_of_isAdmissibleEvolutionDomain hΩ)
      σ r hσr y =
      Measure.map (MovingFiberKernel.firstPosition Ω γ r)
        (K.fiberKernel (measurableSet_of_isAdmissibleEvolutionDomain hΩ) σ r hσr
          (positionStateZero Ω γ σ y)) := by
    rw [parabolicMarginalKernel_apply, MovingFiberKernel.fiberFirstMarginal,
      ProbabilityTheory.Kernel.map_apply _ (hfirst r)]
  rw [hmarg, lintegral_map hmeas (hfirst r)]
  refine lintegral_congr fun x => ?_
  rw [hind x, MovingFiberKernel.fiberFirstMarginal,
    ProbabilityTheory.Kernel.map_apply _ (hfirst τ), Measure.map_apply (hfirst τ) hs]

/-- The full parabolic marginal package of the terminal evolution (companion paper,
Proposition 2.1), for every moving fiber kernel `K` whose master measures are the terminal
measures `μ q`, with ONE shared operator family `Q₀ = marginalOperators K`.  The
Chapman-Kolmogorov identity `hComp` of the fiber kernel (Proposition 2.1, composition) is
used for the two Chapman-Kolmogorov clauses; Hörmander enters only through `hH`. -/
theorem terminalMarginal_properties_of_master_eq
    (hH : HormanderHypoellipticityStatement)
    (K : MovingFiberKernel Ω γ) (hK : ∀ q, K.master q = μ q)
    (hComp : K.HasComposition (measurableSet_of_isAdmissibleEvolutionDomain hΩ)) :
    SectionTwo.HasParabolicMarginalBundle Ω γ
      (measurableSet_of_isAdmissibleEvolutionDomain hΩ) B K := by
  unfold SectionTwo.HasParabolicMarginalBundle
  intro hBz
  have hCK := parabolicMarginalKernel_comp_of_master_eq n hn lam Lam m L_b hlam hlamLam hm hmLb
    Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx K hK hBz hComp
  have hQ := marginalOperators_apply K (measurableSet_of_isAdmissibleEvolutionDomain hΩ)
  refine ⟨marginalOperators K (measurableSet_of_isAdmissibleEvolutionDomain hΩ), ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun σ τ hστ y z =>
      parabolicMarginalKernel_eq_fiberFirstMarginal_of_master_eq n hn lam Lam m L_b hlam hlamLam
        hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx K
        hK hBz σ τ hστ y z
  · intro σ
    refine LinearMap.ext fun f => BoundedBorel.ext fun y => ?_
    rw [hQ, parabolicMarginalKernel_self_of_master_eq n hn lam Lam m L_b hlam hlamLam hm hmLb
      Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx K hK,
      ProbabilityTheory.Kernel.id_apply, integral_dirac' _ _ f.measurable.stronglyMeasurable]
    rfl
  · exact fun σ τ hστ f hf =>
      marginalOperators_nonneg K (measurableSet_of_isAdmissibleEvolutionDomain hΩ) σ τ hστ f hf
  · exact fun σ τ hστ =>
      marginalOperators_one_le K (measurableSet_of_isAdmissibleEvolutionDomain hΩ) σ τ hστ
  · intro σ r τ hσr hrτ
    refine LinearMap.ext fun f => BoundedBorel.ext fun y => ?_
    have h1 := isFiniteKernel_parabolicMarginalKernel K
      (measurableSet_of_isAdmissibleEvolutionDomain hΩ) σ r hσr
    have h2 := isFiniteKernel_parabolicMarginalKernel K
      (measurableSet_of_isAdmissibleEvolutionDomain hΩ) r τ hrτ
    rw [LinearMap.comp_apply, hQ, hQ, hCK σ r τ hσr hrτ,
      ProbabilityTheory.Kernel.integral_comp (integrable_boundedBorel f _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y' => ?_)
    exact (hQ r τ hrτ f y').symm
  · exact fun σ τ hστ y f => hQ σ τ hστ f y
  · exact fun E hE => measurable_parabolicMarginalAmbientMeasure K
      (measurableSet_of_isAdmissibleEvolutionDomain hΩ) E hE
  · exact fun σ => parabolicMarginalKernel_self_of_master_eq n hn lam Lam m L_b hlam hlamLam hm
      hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx K hK σ
  · exact hCK
  · intro τ F hF
    obtain ⟨V, hV1, hV2, hV3⟩ := exists_classical_terminalMarginal_of_master_eq n hn lam Lam m L_b
      hlam hlamLam hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz
      hb_coercive hEx hH K hK hBz τ F hF
    exact ⟨V, hV1, fun σ hστ y =>
      (hV2 σ hστ y).trans (hQ σ τ hστ (terminalPositionDatum F) y).symm, hV3⟩

end EvolutionData

end HypoellipticAleksandrov.KineticAleksandrov
