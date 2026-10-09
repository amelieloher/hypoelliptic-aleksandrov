module

import Mathlib.Tactic.Linarith
public import HypoellipticAleksandrov.KineticAleksandrov.EvolutionProblem
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TerminalIntegralOperator
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TranslationCovariance

/-!
# The scalar marginal kernels and operators

Companion paper, Proposition 2.1 (marginal clause).  All of the following is about the single moving
fiber kernel `K`; the scalar marginal kernel is the zero-`z` pullback of its first marginal
(`parabolicMarginalKernel`).

* `parabolicMarginalKernel_eq_fiberFirstMarginal_of_master_eq`: if `B` does not depend on
  the transported coordinate, the first marginal of the fiber kernel does not depend on the
  transported coordinate of the source, so the zero-`z` pullback is the first marginal at every `z`.
* `exists_unique_marginalIntegralOperator`, `marginalOperators`: the integral operators of
  the marginal kernels as the unique real-linear maps of bounded Borel functions; positivity and
  contraction (no hypothesis on `B`).
* `measurable_parabolicMarginalAmbientMeasure`: the constrained joint measurability of the
  ambient marginal measure (no hypothesis on `B`).
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic MeasureTheory Set
open scoped ENNReal ProbabilityTheory

section Outside

variable {n : ℕ} {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n}
  (K : MovingFiberKernel Ω γ) (hΩ : MeasurableSet Ω)

/-- The scalar marginal kernel has mass at most one. -/
theorem parabolicMarginalKernel_univ_le_one (σ τ : ℝ) (hστ : σ ≤ τ)
    (y : EvolutionPosition Ω γ σ) : parabolicMarginalKernel K hΩ σ τ hστ y univ ≤ 1 := by
  rw [parabolicMarginalKernel_apply, MovingFiberKernel.fiberFirstMarginal,
    ProbabilityTheory.Kernel.map_apply _ (MovingFiberKernel.measurable_firstPosition Ω γ τ),
    Measure.map_apply (MovingFiberKernel.measurable_firstPosition Ω γ τ) MeasurableSet.univ,
    preimage_univ]
  exact K.fiberKernel_mass_le_one hΩ σ τ hστ _

/-- The scalar marginal kernel is a finite kernel. -/
theorem isFiniteKernel_parabolicMarginalKernel (σ τ : ℝ) (hστ : σ ≤ τ) :
    ProbabilityTheory.IsFiniteKernel (parabolicMarginalKernel K hΩ σ τ hστ) :=
  ⟨⟨1, ENNReal.one_lt_top, fun y => parabolicMarginalKernel_univ_le_one K hΩ σ τ hστ y⟩⟩

/-- The integral of a bounded Borel function against the scalar marginal kernel, as a bounded
Borel function of the source position. -/
def marginalIntegralDatum (σ τ : ℝ) (hστ : σ ≤ τ) (f : BoundedBorel (EvolutionPosition Ω γ τ)) :
    BoundedBorel (EvolutionPosition Ω γ σ) :=
  haveI := isFiniteKernel_parabolicMarginalKernel K hΩ σ τ hστ
  ⟨fun y => ∫ y', f y' ∂(parabolicMarginalKernel K hΩ σ τ hστ y),
    (MeasureTheory.StronglyMeasurable.integral_kernel f.measurable.stronglyMeasurable :
      StronglyMeasurable fun y => ∫ y', f y' ∂(parabolicMarginalKernel K hΩ σ τ hστ y)).measurable,
    by
      obtain ⟨C, hC0, hC⟩ := f.exists_bound
      exact ⟨C, hC0, fun y => abs_integral_boundedBorel_le f _
        (parabolicMarginalKernel_univ_le_one K hΩ σ τ hστ y) hC0 hC⟩⟩

/-- Evaluation of `marginalIntegralDatum`. -/
theorem marginalIntegralDatum_apply (σ τ : ℝ) (hστ : σ ≤ τ)
    (f : BoundedBorel (EvolutionPosition Ω γ τ)) (y : EvolutionPosition Ω γ σ) :
    marginalIntegralDatum K hΩ σ τ hστ f y =
      ∫ y', f y' ∂(parabolicMarginalKernel K hΩ σ τ hστ y) :=
  rfl

/-- The integral operator against the scalar marginal kernel is the unique real-linear
map of bounded Borel functions with the integral formula. -/
theorem exists_unique_marginalIntegralOperator (σ τ : ℝ) (hστ : σ ≤ τ) :
    ∃! T : BoundedBorel (EvolutionPosition Ω γ τ) →ₗ[ℝ] BoundedBorel (EvolutionPosition Ω γ σ),
      ∀ (f : BoundedBorel (EvolutionPosition Ω γ τ)) (y : EvolutionPosition Ω γ σ),
        T f y = ∫ y', f y' ∂(parabolicMarginalKernel K hΩ σ τ hστ y) := by
  let T : BoundedBorel (EvolutionPosition Ω γ τ) →ₗ[ℝ] BoundedBorel (EvolutionPosition Ω γ σ) :=
    { toFun := marginalIntegralDatum K hΩ σ τ hστ
      map_add' := fun f g => BoundedBorel.ext fun y => by
        simp only [marginalIntegralDatum_apply, BoundedBorel.add_apply]
        have := isFiniteKernel_parabolicMarginalKernel K hΩ σ τ hστ
        exact integral_add (integrable_boundedBorel f _) (integrable_boundedBorel g _)
      map_smul' := fun c f => BoundedBorel.ext fun y => by
        simp only [marginalIntegralDatum_apply, BoundedBorel.smul_apply, RingHom.id_apply,
          smul_eq_mul]
        exact integral_const_mul c _ }
  refine ⟨T, fun f y => rfl, fun T' hT' => ?_⟩
  exact LinearMap.ext fun f => BoundedBorel.ext fun y => by
    rw [hT' f y]; rfl

/-- The family `Q₀` of scalar marginal integral operators, chosen from the `∃!`
statements `exists_unique_marginalIntegralOperator`. -/
def marginalOperators : ParabolicOperatorFamily Ω γ :=
  fun σ τ hστ => (exists_unique_marginalIntegralOperator K hΩ σ τ hστ).choose

/-- The integral formula for the marginal operators. -/
theorem marginalOperators_apply (σ τ : ℝ) (hστ : σ ≤ τ)
    (f : BoundedBorel (EvolutionPosition Ω γ τ)) (y : EvolutionPosition Ω γ σ) :
    marginalOperators K hΩ σ τ hστ f y =
      ∫ y', f y' ∂(parabolicMarginalKernel K hΩ σ τ hστ y) :=
  (exists_unique_marginalIntegralOperator K hΩ σ τ hστ).choose_spec.1 f y

/-- A linear map with the integral formula is the chosen operator. -/
theorem marginalOperators_eq_of_apply (σ τ : ℝ) (hστ : σ ≤ τ)
    (T : BoundedBorel (EvolutionPosition Ω γ τ) →ₗ[ℝ] BoundedBorel (EvolutionPosition Ω γ σ))
    (hT : ∀ (f : BoundedBorel (EvolutionPosition Ω γ τ)) (y : EvolutionPosition Ω γ σ),
      T f y = ∫ y', f y' ∂(parabolicMarginalKernel K hΩ σ τ hστ y)) :
    T = marginalOperators K hΩ σ τ hστ :=
  (exists_unique_marginalIntegralOperator K hΩ σ τ hστ).unique hT
    (marginalOperators_apply K hΩ σ τ hστ)

/-- The marginal operators are positive. -/
theorem marginalOperators_nonneg (σ τ : ℝ) (hστ : σ ≤ τ)
    (f : BoundedBorel (EvolutionPosition Ω γ τ)) (hf : 0 ≤ f) :
    0 ≤ marginalOperators K hΩ σ τ hστ f := fun y => by
  rw [BoundedBorel.zero_apply, marginalOperators_apply]
  exact integral_nonneg fun x => hf x

/-- The marginal operators are contractions on the constant one. -/
theorem marginalOperators_one_le (σ τ : ℝ) (hστ : σ ≤ τ) :
    marginalOperators K hΩ σ τ hστ (1 : BoundedBorel (EvolutionPosition Ω γ τ)) ≤
      (1 : BoundedBorel (EvolutionPosition Ω γ σ)) := fun y => by
  rw [marginalOperators_apply]
  simp only [BoundedBorel.one_apply, integral_const, smul_eq_mul, mul_one]
  have hmass := parabolicMarginalKernel_univ_le_one K hΩ σ τ hστ y
  rw [Measure.real]
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hmass)

/-- The lift of a parabolic query to the kinetic query with transported source `0`. -/
def parabolicQueryLift (q : ParabolicEvolutionQuery Ω γ) : EvolutionQuery Ω γ :=
  evolutionQueryOfState Ω γ q.1.1 q.1.2.1 q.property.1
    (positionStateZero Ω γ q.1.1 (parabolicQuerySource q))

/-- The parabolic query lift is measurable. -/
theorem measurable_parabolicQueryLift : Measurable (parabolicQueryLift (Ω := Ω) (γ := γ)) := by
  apply Measurable.subtype_mk
  show Measurable fun q : ParabolicEvolutionQuery Ω γ =>
    ((q.1.1, (q.1.2.1, (q.1.2.2, (0 : PDE.Vec n)))) : RawEvolutionQuery n)
  fun_prop

/-- The ambient marginal measure is the first marginal of the master measure at the lifted query. -/
theorem parabolicMarginalAmbientMeasure_eq (q : ParabolicEvolutionQuery Ω γ) :
    parabolicMarginalAmbientMeasure K hΩ q = K.firstMarginal (parabolicQueryLift q) := by
  rw [parabolicMarginalAmbientMeasure, parabolicMarginalKernel_apply,
    MovingFiberKernel.map_fiberFirstMarginal_eq_firstMarginal]
  rfl

/-- Constrained joint measurability of the ambient marginal measure: the evaluation on
a Borel set is measurable in the parabolic query (no hypothesis on `B`). -/
theorem measurable_parabolicMarginalAmbientMeasure (E : Set (PDE.Vec n)) (hE : MeasurableSet E) :
    Measurable (fun q : ParabolicEvolutionQuery Ω γ =>
      parabolicMarginalAmbientMeasure K hΩ q E) := by
  have h : (fun q : ParabolicEvolutionQuery Ω γ => parabolicMarginalAmbientMeasure K hΩ q E) =
      fun q => K.master (parabolicQueryLift q) {p | p.1 ∈ E} := by
    funext q
    rw [parabolicMarginalAmbientMeasure_eq, MovingFiberKernel.firstMarginal_apply _ _ _ hE]
  rw [h]
  exact (K.master.measurable_coe (measurable_fst hE)).comp measurable_parabolicQueryLift

end Outside

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

/-- **Marginal independence** (Proposition 2.1, first clause), for every moving fiber kernel `K`
whose master measures are the terminal measures `μ q`.  If `B` does not depend on the transported
coordinate, the zero-`z` pullback of the first marginal equals the first marginal at every
transported coordinate `z` of the source. -/
theorem parabolicMarginalKernel_eq_fiberFirstMarginal_of_master_eq
    (K : MovingFiberKernel Ω γ) (hK : ∀ q, K.master q = μ q)
    (hBz : ∀ (σ : ℝ) (y z z' : PDE.Vec n), B σ y z = B σ y z')
    (σ τ : ℝ) (hστ : σ ≤ τ) (y : EvolutionPosition Ω γ σ) (z : PDE.Vec n) :
    parabolicMarginalKernel K (measurableSet_of_isAdmissibleEvolutionDomain hΩ) σ τ hστ y =
      K.fiberFirstMarginal (measurableSet_of_isAdmissibleEvolutionDomain hΩ)
        σ τ hστ (evolutionStateOfPosition Ω γ σ y z) := by
  have hs : evolutionStateOfPosition Ω γ σ y z =
      evolutionStateShift Ω γ σ z (positionStateZero Ω γ σ y) :=
    Subtype.ext (Prod.ext rfl (zero_add z).symm)
  have hfs : ∀ (p : EvolutionState Ω γ τ) (h : PDE.Vec n),
      MovingFiberKernel.firstPosition Ω γ τ (evolutionStateShift Ω γ τ h p) =
        MovingFiberKernel.firstPosition Ω γ τ p := fun p h => rfl
  rw [parabolicMarginalKernel_apply, hs, MovingFiberKernel.fiberFirstMarginal,
    ProbabilityTheory.Kernel.map_apply _ (MovingFiberKernel.measurable_firstPosition Ω γ τ),
    ProbabilityTheory.Kernel.map_apply _ (MovingFiberKernel.measurable_firstPosition Ω γ τ),
    ← terminalKernel_translation_of_master_eq n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx K hK hBz σ τ hστ z,
    Measure.map_map (MovingFiberKernel.measurable_firstPosition Ω γ τ)
      (measurable_evolutionStateShift' τ z)]
  congr 1

end EvolutionData

end HypoellipticAleksandrov.KineticAleksandrov
