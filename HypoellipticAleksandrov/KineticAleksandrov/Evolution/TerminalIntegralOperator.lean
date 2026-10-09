module

import Mathlib.Tactic.Linarith
public import Mathlib.Probability.Kernel.MeasurableIntegral
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.FixedFiberMeasure

/-!
# The integral operators of the terminal evolution

Companion paper, Proposition 2.1 and the endpoint, positivity and contraction clauses of
Proposition 2.1: the bounded Borel operator `P₀ σ τ hστ f p = ∫ f d(κ σ τ hστ p)` and its
basic properties, all for the SAME fiber kernel `κ` built from the terminal measures.

* `exists_unique_terminalIntegralOperator`: the integral operators exist and are unique.
* `terminalOperators`: the full family, chosen from the `∃!` statements; `terminalOperators_apply`.
* `terminalOperators_basic`: endpoint identity, positivity, `P₀ 1 ≤ 1`, `κ σ σ = id`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic MeasureTheory Set
open scoped CompactlySupported ENNReal ProbabilityTheory

section Outside

/-- Bounded Borel functions are integrable for finite measures. -/
theorem integrable_boundedBorel {Y : Type*} [MeasurableSpace Y] (f : BoundedBorel Y)
    (μ : Measure Y) [IsFiniteMeasure μ] : Integrable (fun y => f y) μ := by
  obtain ⟨C, -, hC⟩ := f.exists_bound
  exact Integrable.of_bound f.measurable.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun y => by simpa using hC y)

/-- The integral of a bounded Borel function against a subprobability measure is bounded by
the bound of the function. -/
theorem abs_integral_boundedBorel_le {Y : Type*} [MeasurableSpace Y] (f : BoundedBorel Y)
    (μ : Measure Y) (hμ : μ univ ≤ 1) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ y, |f y| ≤ C) :
    |∫ y, f y ∂μ| ≤ C := by
  have : IsFiniteMeasure μ := ⟨hμ.trans_lt ENNReal.one_lt_top⟩
  have hreal : μ.real univ ≤ 1 := by
    rw [Measure.real]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hμ)
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun y => f y) (C := C)
    (Filter.Eventually.of_forall fun y => by simpa using hC y)
  calc |∫ y, f y ∂μ| = ‖∫ y, f y ∂μ‖ := (Real.norm_eq_abs _).symm
    _ ≤ C * μ.real univ := this
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left hreal hC0
    _ = C := mul_one C

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
local notation "κ" => terminalFiberKernel n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx

/-- The integral of a bounded Borel function against the fiber kernel, as a bounded Borel
function of the source state. -/
def terminalIntegralDatum (σ τ : ℝ) (hστ : σ ≤ τ) (f : BoundedBorel (EvolutionState Ω γ τ)) :
    BoundedBorel (EvolutionState Ω γ σ) :=
  haveI := isFiniteKernel_terminalFiberKernel n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx σ τ hστ
  ⟨fun p => ∫ x, f x ∂(κ σ τ hστ p),
    (MeasureTheory.StronglyMeasurable.integral_kernel f.measurable.stronglyMeasurable :
      StronglyMeasurable fun p => ∫ x, f x ∂(κ σ τ hστ p)).measurable, by
    obtain ⟨C, hC0, hC⟩ := f.exists_bound
    exact ⟨C, hC0, fun p => abs_integral_boundedBorel_le f _
      (terminalFiberKernel_univ_le_one n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
        hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx σ τ hστ p) hC0 hC⟩⟩

/-- Evaluation of `terminalIntegralDatum`. -/
theorem terminalIntegralDatum_apply (σ τ : ℝ) (hστ : σ ≤ τ)
    (f : BoundedBorel (EvolutionState Ω γ τ)) (p : EvolutionState Ω γ σ) :
    terminalIntegralDatum n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx σ τ hστ f p =
        ∫ x, f x ∂(κ σ τ hστ p) :=
  rfl

/-- The integral operator against the fiber kernel is the unique real-linear map of
bounded Borel functions with the integral formula. -/
theorem exists_unique_terminalIntegralOperator
    (σ τ : ℝ) (hστ : σ ≤ τ) :
    ∃! T : BoundedBorel (EvolutionState Ω γ τ) →ₗ[ℝ] BoundedBorel (EvolutionState Ω γ σ),
      ∀ (f : BoundedBorel (EvolutionState Ω γ τ)) (p : EvolutionState Ω γ σ),
        T f p = ∫ x, f x ∂(κ σ τ hστ p) := by
  have hfin := isFiniteKernel_terminalFiberKernel n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx σ τ hστ
  let T : BoundedBorel (EvolutionState Ω γ τ) →ₗ[ℝ] BoundedBorel (EvolutionState Ω γ σ) :=
    { toFun := terminalIntegralDatum n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
        hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx σ τ hστ
      map_add' := fun f g => BoundedBorel.ext fun p => by
        simp only [terminalIntegralDatum_apply, BoundedBorel.add_apply]
        exact integral_add (integrable_boundedBorel f _) (integrable_boundedBorel g _)
      map_smul' := fun c f => BoundedBorel.ext fun p => by
        simp only [terminalIntegralDatum_apply, BoundedBorel.smul_apply, RingHom.id_apply,
          smul_eq_mul]
        exact integral_const_mul c _ }
  refine ⟨T, fun f p => rfl, fun T' hT' => ?_⟩
  exact LinearMap.ext fun f => BoundedBorel.ext fun p => by
    rw [hT' f p]; rfl

/-- The full family of integral operators `P₀ σ τ hστ`, chosen from the `∃!`
statements `exists_unique_terminalIntegralOperator`. -/
def terminalOperators : TerminalOperatorFamily Ω γ :=
  fun σ τ hστ =>
    (exists_unique_terminalIntegralOperator n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx σ τ hστ).choose

local notation "P₀" => terminalOperators n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx

/-- The integral formula for the operators. -/
theorem terminalOperators_apply
    (σ τ : ℝ) (hστ : σ ≤ τ)
    (f : BoundedBorel (EvolutionState Ω γ τ)) (p : EvolutionState Ω γ σ) :
    P₀ σ τ hστ f p = ∫ x, f x ∂(κ σ τ hστ p) :=
  (exists_unique_terminalIntegralOperator n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx σ τ hστ).choose_spec.1
    f p

/-- A linear map with the integral formula is the chosen operator. -/
theorem terminalOperators_eq_of_apply
    (σ τ : ℝ) (hστ : σ ≤ τ)
    (T : BoundedBorel (EvolutionState Ω γ τ) →ₗ[ℝ] BoundedBorel (EvolutionState Ω γ σ))
    (hT : ∀ (f : BoundedBorel (EvolutionState Ω γ τ)) (p : EvolutionState Ω γ σ),
      T f p = ∫ x, f x ∂(κ σ τ hστ p)) :
    T = P₀ σ τ hστ :=
  (exists_unique_terminalIntegralOperator n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx σ τ hστ).unique hT
    (terminalOperators_apply n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx σ τ hστ)

/-- At equal times the fiber kernel is the identity kernel (Dirac characterization of the terminal
measure). -/
theorem terminalFiberKernel_self (σ : ℝ) :
    κ σ σ le_rfl = (ProbabilityTheory.Kernel.id :
      ProbabilityTheory.Kernel (EvolutionState Ω γ σ) (EvolutionState Ω γ σ)) := by
  refine ProbabilityTheory.Kernel.ext fun p => ?_
  rw [terminalFiberKernel_apply, ProbabilityTheory.Kernel.id_apply,
    terminalMeasure_eq_dirac n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx σ p]
  have hU := measurableSet_evolutionStateSet_of_isOpen (γ := γ) (τ := σ)
    (isOpen_of_isAdmissibleEvolutionDomain hΩ)
  have hemb := MeasurableEmbedding.subtype_coe hU
  refine Measure.ext fun A hA => ?_
  rw [hemb.comap_apply, Measure.dirac_apply' _ (hemb.measurableSet_image.2 hA),
    Measure.dirac_apply' _ hA]
  have hiff : p.1 ∈ Subtype.val '' A ↔ p ∈ A := Subtype.val_injective.mem_set_image
  by_cases h : p ∈ A
  · simp [Set.indicator, h, hiff.2 h]
  · simp [Set.indicator, h, mt hiff.1 h]

/-- Endpoint identity, positivity, subprobability contraction, and the identity kernel at
equal times, all for the same `μ`-derived `κ` and `P₀`. -/
theorem terminalOperators_basic :
    (∀ σ, P₀ σ σ le_rfl =
      (LinearMap.id : BoundedBorel (EvolutionState Ω γ σ) →ₗ[ℝ]
        BoundedBorel (EvolutionState Ω γ σ))) ∧
    (∀ σ τ hστ (f : BoundedBorel (EvolutionState Ω γ τ)),
      0 ≤ f → 0 ≤ P₀ σ τ hστ f) ∧
    (∀ σ τ hστ, P₀ σ τ hστ (1 : BoundedBorel (EvolutionState Ω γ τ)) ≤
      (1 : BoundedBorel (EvolutionState Ω γ σ))) ∧
    (∀ σ, κ σ σ le_rfl =
      (ProbabilityTheory.Kernel.id : ProbabilityTheory.Kernel
        (EvolutionState Ω γ σ) (EvolutionState Ω γ σ))) := by
  refine ⟨fun σ => ?_, fun σ τ hστ f hf p => ?_, fun σ τ hστ p => ?_, fun σ => ?_⟩
  · refine LinearMap.ext fun f => BoundedBorel.ext fun p => ?_
    rw [terminalOperators_apply n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx,
      terminalFiberKernel_self n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
        hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx,
      ProbabilityTheory.Kernel.id_apply, integral_dirac' _ _ f.measurable.stronglyMeasurable]
    rfl
  · rw [BoundedBorel.zero_apply, terminalOperators_apply n hn lam Lam m L_b hlam hlamLam hm hmLb
      Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx]
    exact integral_nonneg fun x => hf x
  · rw [terminalOperators_apply n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx]
    simp only [BoundedBorel.one_apply, integral_const, smul_eq_mul, mul_one]
    have hmass := terminalFiberKernel_univ_le_one n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx σ τ hστ p
    rw [Measure.real]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hmass)
  · exact terminalFiberKernel_self n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx σ

end EvolutionData

end HypoellipticAleksandrov.KineticAleksandrov
