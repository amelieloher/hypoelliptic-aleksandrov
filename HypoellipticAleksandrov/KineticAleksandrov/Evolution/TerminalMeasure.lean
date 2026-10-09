module

import Mathlib.Tactic.Linarith
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TerminalFunctional
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TerminalMeasureRiesz

/-!
# The unique Riesz measure of the terminal evolution

Companion paper, Proposition 2.1 (kernels): the positive terminal functional is
represented, by `RealRMK.integral_rieszMeasure`, by a Borel measure on the open terminal fiber of
mass at most one; mapped into the ambient state it is the unique measure with
`μ univ ≤ 1`, supported on the fiber, whose integrals against smooth compactly supported probes
are the point values `terminalValue`.

* `exists_unique_terminalMeasure`: existence and uniqueness of the terminal measure.
* `terminalMeasure`: the unique measure, chosen from the `∃!` statement; `terminalMeasure_spec`.
* `terminalMeasure_eq_dirac`: at equal times the measure is the Dirac mass at the source.
* `comap_terminalMeasure_eq_rieszMeasure`: its fiber part is the Riesz measure of the terminal
  functional.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic MeasureTheory Set
open scoped CompactlySupported ENNReal

section Outside

variable {n : ℕ} {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n} {τ : ℝ}

/-- The open state fiber is locally compact. -/
theorem locallyCompactSpace_evolutionState (hΩ : IsOpen Ω) :
    LocallyCompactSpace (EvolutionState Ω γ τ) :=
  ((isOpen_movingDomain hΩ τ).prod isOpen_univ).locallyCompactSpace

/-- The state fiber is measurable for an open base domain. -/
theorem measurableSet_evolutionStateSet_of_isOpen (hΩ : IsOpen Ω) :
    MeasurableSet (evolutionStateSet Ω γ τ) :=
  ((isOpen_movingDomain hΩ τ).prod isOpen_univ).measurableSet

/-- The push-forward of a measure on a measurable subtype is supported on the subtype. -/
theorem map_subtype_val_restrict {α : Type*} [MeasurableSpace α] {U : Set α}
    (hU : MeasurableSet U) (ν : Measure U) :
    (ν.map Subtype.val).restrict U = ν.map Subtype.val := by
  refine Measure.ext fun A hA => ?_
  rw [Measure.restrict_apply hA, Measure.map_apply measurable_subtype_coe (hA.inter hU),
    Measure.map_apply measurable_subtype_coe hA]
  congr 1
  ext x
  simp

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

local notation "S" => terminalValue n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
local notation "ℓ_" => terminalFunctional n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
local notation "ℓ_spec" => terminalFunctional_spec n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx

/-- The Riesz measure on the open terminal fiber of the terminal functional of the source
state `p` (the terminal functional and `RealRMK.rieszMeasure`). -/
def terminalFiberRieszMeasure (σ τ : ℝ) (hστ : σ ≤ τ) (p : EvolutionState Ω γ σ) :
    Measure (EvolutionState Ω γ τ) :=
  have := locallyCompactSpace_evolutionState (γ := γ) (τ := τ)
    (isOpen_of_isAdmissibleEvolutionDomain hΩ)
  RealRMK.rieszMeasure (ℓ_ σ τ hστ p)

/-- The Riesz measure of the terminal functional has mass at most one. -/
theorem terminalFiberRieszMeasure_univ_le_one
    (σ τ : ℝ) (hστ : σ ≤ τ) (p : EvolutionState Ω γ σ) :
    terminalFiberRieszMeasure n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx σ τ hστ p univ ≤ 1 :=
  have := locallyCompactSpace_evolutionState (γ := γ) (τ := τ)
    (isOpen_of_isAdmissibleEvolutionDomain hΩ)
  rieszMeasure_univ_le_one (ℓ_ σ τ hστ p) (ℓ_spec σ τ hστ p).1

/-- The Riesz measure of the terminal functional is finite. -/
theorem isFiniteMeasure_terminalFiberRieszMeasure
    (σ τ : ℝ) (hστ : σ ≤ τ) (p : EvolutionState Ω γ σ) :
    IsFiniteMeasure (terminalFiberRieszMeasure n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx σ τ hστ p) :=
  ⟨(terminalFiberRieszMeasure_univ_le_one n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx σ τ hστ p).trans_lt
    ENNReal.one_lt_top⟩

/-- The integral of a `C_c` test against the Riesz measure is the value of the functional. -/
theorem integral_terminalFiberRieszMeasure
    (σ τ : ℝ) (hστ : σ ≤ τ) (p : EvolutionState Ω γ σ) (f : C_c(EvolutionState Ω γ τ, ℝ)) :
    ∫ x, f x ∂(terminalFiberRieszMeasure n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx σ τ hστ p) =
      ℓ_ σ τ hστ p f :=
  have := locallyCompactSpace_evolutionState (γ := γ) (τ := τ)
    (isOpen_of_isAdmissibleEvolutionDomain hΩ)
  RealRMK.integral_rieszMeasure (ℓ_ σ τ hστ p) f

/-- The pushed-forward Riesz measure satisfies the characterization of the terminal measure. -/
theorem map_terminalFiberRieszMeasure_spec (q : EvolutionQuery Ω γ) :
    let ν := terminalFiberRieszMeasure n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
      q.1.1 q.1.2.1 q.property.1 ⟨q.1.2.2, q.property.2⟩
    ν.map Subtype.val univ ≤ 1 ∧
      ((ν.map Subtype.val).restrict (evolutionStateSet Ω γ q.1.2.1) = ν.map Subtype.val) ∧
      ∀ (F : BoundedBorel (EvolutionAmbientState n))
        (hF : IsSmoothCompactTerminalDatum Ω γ q.1.2.1 F),
        (∫ x, F x ∂(ν.map Subtype.val)) =
          S q.1.1 q.1.2.1 q.property.1 ⟨q.1.2.2, q.property.2⟩ F hF := by
  intro ν
  have hmass := terminalFiberRieszMeasure_univ_le_one n hn lam Lam m L_b hlam hlamLam hm hmLb
    Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
    q.1.1 q.1.2.1 q.property.1 ⟨q.1.2.2, q.property.2⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ]
    simpa using hmass
  · exact map_subtype_val_restrict (measurableSet_evolutionStateSet_of_isOpen
      (isOpen_of_isAdmissibleEvolutionDomain hΩ)) ν
  · intro F hF
    rw [integral_map measurable_subtype_coe.aemeasurable F.measurable.aestronglyMeasurable]
    have h1 := integral_terminalFiberRieszMeasure n hn lam Lam m L_b hlam hlamLam hm hmLb
      Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
      q.1.1 q.1.2.1 q.property.1 ⟨q.1.2.2, q.property.2⟩
      (terminalProbeCc (terminalProbeOfDatum F hF))
    refine h1.trans ((ℓ_spec q.1.1 q.1.2.1 q.property.1 ⟨q.1.2.2, q.property.2⟩).2 F hF _
      fun x => rfl)

/-- Uniqueness half of Every subprobability measure supported on the open fiber with the
probe integrals `terminalValue` is the pushed-forward Riesz measure. -/
theorem eq_map_terminalFiberRieszMeasure (q : EvolutionQuery Ω γ)
    (μ' : Measure (EvolutionAmbientState n)) (hmass : μ' univ ≤ 1)
    (hres : μ'.restrict (evolutionStateSet Ω γ q.1.2.1) = μ')
    (hint : ∀ (F : BoundedBorel (EvolutionAmbientState n))
      (hF : IsSmoothCompactTerminalDatum Ω γ q.1.2.1 F),
      (∫ x, F x ∂μ') = S q.1.1 q.1.2.1 q.property.1 ⟨q.1.2.2, q.property.2⟩ F hF) :
    μ' = (terminalFiberRieszMeasure n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
      q.1.1 q.1.2.1 q.property.1 ⟨q.1.2.2, q.property.2⟩).map Subtype.val := by
  have hΩo := isOpen_of_isAdmissibleEvolutionDomain hΩ
  have := locallyCompactSpace_evolutionState (γ := γ) (τ := q.1.2.1) hΩo
  have hU := measurableSet_evolutionStateSet_of_isOpen (γ := γ) (τ := q.1.2.1) hΩo
  set ν' : Measure (EvolutionState Ω γ q.1.2.1) := Measure.comap Subtype.val μ' with hν'
  have hmap : ν'.map Subtype.val = μ' := by
    rw [hν', map_comap_subtype_coe hU, hres]
  have hmassν : ν' univ = μ' univ := by
    conv_rhs => rw [← hmap]
    rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ]
    simp
  have : IsFiniteMeasure ν' := ⟨by rw [hmassν]; exact hmass.trans_lt ENNReal.one_lt_top⟩
  have hreal : ν'.real univ ≤ 1 := by
    rw [Measure.real, hmassν]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hmass)
  let Λ : C_c(EvolutionState Ω γ q.1.2.1, ℝ) →ₚ[ℝ] ℝ :=
    CompactlySupportedContinuousMap.integralPositiveLinearMap ν'
  have hΛbd : ∀ (f : C_c(EvolutionState Ω γ q.1.2.1, ℝ)) (c : ℝ), 0 ≤ c → (∀ x, |f x| ≤ c) →
      |Λ f| ≤ c := by
    intro f c hc h
    have := norm_integral_le_of_norm_le_const (μ := ν') (f := fun x => f x) (C := c)
      (Filter.Eventually.of_forall fun x => by simpa using h x)
    calc |Λ f| = ‖∫ x, f x ∂ν'‖ := by simp [Λ, Real.norm_eq_abs]
      _ ≤ c * ν'.real univ := this
      _ ≤ c * 1 := mul_le_mul_of_nonneg_left hreal hc
      _ = c := mul_one c
  have hagree : ∀ F : terminalProbeSubmodule Ω γ q.1.2.1,
      Λ.toLinearMap (terminalProbeCcLinear F) =
        (ℓ_ q.1.1 q.1.2.1 q.property.1 ⟨q.1.2.2, q.property.2⟩).toLinearMap
          (terminalProbeCcLinear F) := by
    intro F
    have h1 : Λ (terminalProbeCcLinear F) = ∫ x, (terminalProbeDatum F) x ∂μ' := by
      rw [← hmap, integral_map measurable_subtype_coe.aemeasurable
        (terminalProbeDatum F).measurable.aestronglyMeasurable]
      simp [Λ]
    have h2 := (ℓ_spec q.1.1 q.1.2.1 q.property.1 ⟨q.1.2.2, q.property.2⟩).2
      (terminalProbeDatum F) (terminalProbeDatum_isSmoothCompact F)
      (terminalProbeCcLinear F) fun x => rfl
    exact h1.trans ((hint _ (terminalProbeDatum_isSmoothCompact F)).trans h2.symm)
  have hlin := eq_of_bounded_of_dense (terminalProbeCcLinear (Ω := Ω) (γ := γ) (τ := q.1.2.1))
    Λ.toLinearMap (ℓ_ q.1.1 q.1.2.1 q.property.1 ⟨q.1.2.2, q.property.2⟩).toLinearMap hΛbd
    (ℓ_spec q.1.1 q.1.2.1 q.property.1 ⟨q.1.2.2, q.property.2⟩).1 hagree
    (fun f ε hε => exists_terminalProbe_close hΩo f ε hε)
  have hν : ν' = terminalFiberRieszMeasure n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
      q.1.1 q.1.2.1 q.property.1 ⟨q.1.2.2, q.property.2⟩ :=
    eq_rieszMeasure_of_integral_eq (ℓ_ q.1.1 q.1.2.1 q.property.1 ⟨q.1.2.2, q.property.2⟩) ν'
      fun f => by
        have := LinearMap.congr_fun hlin f
        simpa [Λ] using this
  rw [← hmap, hν]

/-- For every query there is exactly one subprobability measure on the ambient state,
supported on the open terminal fiber, whose integrals against smooth compactly supported probes
are the terminal point values. -/
theorem exists_unique_terminalMeasure (q : EvolutionQuery Ω γ) :
    ∃! μq : Measure (EvolutionAmbientState n),
      μq univ ≤ 1 ∧ (μq.restrict (evolutionStateSet Ω γ q.1.2.1) = μq) ∧
      ∀ (F : BoundedBorel (EvolutionAmbientState n))
        (hF : IsSmoothCompactTerminalDatum Ω γ q.1.2.1 F),
        (∫ x, F x ∂μq) =
          S q.1.1 q.1.2.1 q.property.1 ⟨q.1.2.2, q.property.2⟩ F hF :=
  ⟨_, map_terminalFiberRieszMeasure_spec n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx q,
    fun μ' h => eq_map_terminalFiberRieszMeasure n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx q μ' h.1 h.2.1 h.2.2⟩

/-- The terminal measure `μ q` of the query `q`, chosen from the `∃!` statement
`exists_unique_terminalMeasure`. -/
def terminalMeasure (q : EvolutionQuery Ω γ) : Measure (EvolutionAmbientState n) :=
  (exists_unique_terminalMeasure n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx q).choose

local notation "μ" => terminalMeasure n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx

/-- The full characterization of `terminalMeasure`. -/
theorem terminalMeasure_spec (q : EvolutionQuery Ω γ) :
    μ q univ ≤ 1 ∧ ((μ q).restrict (evolutionStateSet Ω γ q.1.2.1) = μ q) ∧
    ∀ (F : BoundedBorel (EvolutionAmbientState n))
      (hF : IsSmoothCompactTerminalDatum Ω γ q.1.2.1 F),
      (∫ x, F x ∂(μ q)) =
        S q.1.1 q.1.2.1 q.property.1 ⟨q.1.2.2, q.property.2⟩ F hF :=
  (exists_unique_terminalMeasure n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx q).choose_spec.1

/-- A measure with the characterization is the terminal measure. -/
theorem terminalMeasure_eq_of_spec (q : EvolutionQuery Ω γ) (μ' : Measure (EvolutionAmbientState n))
    (hmass : μ' univ ≤ 1) (hres : μ'.restrict (evolutionStateSet Ω γ q.1.2.1) = μ')
    (hint : ∀ (F : BoundedBorel (EvolutionAmbientState n))
      (hF : IsSmoothCompactTerminalDatum Ω γ q.1.2.1 F),
      (∫ x, F x ∂μ') = S q.1.1 q.1.2.1 q.property.1 ⟨q.1.2.2, q.property.2⟩ F hF) :
    μ' = μ q :=
  (exists_unique_terminalMeasure n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx q).unique
    ⟨hmass, hres, hint⟩ (terminalMeasure_spec n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx q)

/-- The terminal measure is the push-forward of the Riesz measure of the terminal functional. -/
theorem terminalMeasure_eq_map_rieszMeasure (q : EvolutionQuery Ω γ) :
    μ q = (terminalFiberRieszMeasure n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
      q.1.1 q.1.2.1 q.property.1 ⟨q.1.2.2, q.property.2⟩).map Subtype.val :=
  by
  have h := map_terminalFiberRieszMeasure_spec n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx q
  exact (terminalMeasure_eq_of_spec n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx q _
    h.1 h.2.1 h.2.2).symm

/-- The fiber part of the terminal measure is the Riesz measure of the terminal functional. -/
theorem comap_terminalMeasure_eq_rieszMeasure (q : EvolutionQuery Ω γ) :
    Measure.comap ((↑) : EvolutionState Ω γ q.1.2.1 → EvolutionAmbientState n) (μ q) =
      terminalFiberRieszMeasure n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
        hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
        q.1.1 q.1.2.1 q.property.1 ⟨q.1.2.2, q.property.2⟩ := by
  rw [terminalMeasure_eq_map_rieszMeasure n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx q]
  exact (MeasurableEmbedding.subtype_coe (measurableSet_evolutionStateSet_of_isOpen
    (isOpen_of_isAdmissibleEvolutionDomain hΩ))).comap_map _

/-- At equal times the terminal measure is the Dirac mass at the source. -/
theorem terminalMeasure_eq_dirac (σ : ℝ) (p : EvolutionState Ω γ σ) :
    μ (evolutionQueryOfState Ω γ σ σ le_rfl p) = Measure.dirac p.1 := by
  refine (terminalMeasure_eq_of_spec n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
    (evolutionQueryOfState Ω γ σ σ le_rfl p) (Measure.dirac p.1) ?_ ?_ ?_).symm
  · simp
  · have hU := measurableSet_evolutionStateSet_of_isOpen (γ := γ) (τ := σ)
      (isOpen_of_isAdmissibleEvolutionDomain hΩ)
    refine Measure.ext fun A hA => ?_
    show (Measure.dirac p.1).restrict (evolutionStateSet Ω γ σ) A = Measure.dirac p.1 A
    rw [Measure.restrict_apply hA, Measure.dirac_apply' _ (hA.inter hU),
      Measure.dirac_apply' _ hA]
    have hp : p.1 ∈ evolutionStateSet Ω γ σ := p.2
    by_cases h : p.1 ∈ A
    · simp [Set.indicator, h, hp]
    · simp [Set.indicator, h]
  · intro F hF
    rw [integral_dirac]
    exact (terminalValue_self n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx σ p F hF).symm

end EvolutionData

end HypoellipticAleksandrov.KineticAleksandrov
