module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothed.Coefficient
import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv

/-!
# Quadratic forms of the Radon-Nikodym coefficient

The averaged quadratic form `ξ · β ξ` integrates against indicator functions to the averaged
quadratic form of `B`; this is the bridge from the Loewner bounds of `B` to those of `β`
(`ν^δ_τ`-almost everywhere, for each fixed `ξ`).
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

open MeasureTheory
open scoped ENNReal NNReal Matrix

variable {d : ℕ} {δ : ℝ} {η : ℝ → ℝ} {τ Lam : ℝ} {Γ' : Measure (ℝ × EvolutionAmbientState d)}
  {Bt : ℝ → EvolutionAmbientState d → PDE.Mat d}

/-- The quadratic form `ξ · A ξ` as a double sum. -/
theorem quadForm_eq_sum (A : PDE.Mat d) (ξ : PDE.Vec d) :
    ξ ⬝ᵥ (A *ᵥ ξ) = ∑ i, ∑ j, ξ i * ξ j * A i j := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

variable [IsFiniteMeasure Γ']
  (hη : IsMollifier δ η) (hmarg : Γ'.map Prod.fst ≤ volume)
  (hBm : ∀ i j, Measurable fun q : ℝ × EvolutionAmbientState d => Bt q.1 q.2 i j)
  (hBb : ∀ t y i j, |Bt t y i j| ≤ Lam)

include hη hBb hBm in
theorem integrable_fluxIntegrand (i j : Fin d) {f : EvolutionAmbientState d → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : ∀ y, |f y| ≤ C) :
    Integrable (fun q : ℝ × EvolutionAmbientState d => η (τ - q.1) * Bt q.1 q.2 i j * f q.2)
      Γ' := by
  obtain ⟨Cη, hCη⟩ := hη.exists_bound
  have hηm : Measurable fun q : ℝ × EvolutionAmbientState d => η (τ - q.1) :=
    (hη.continuous.comp (continuous_const.sub continuous_fst)).measurable
  refine integrable_of_bounded_measurable ((hηm.mul (hBm i j)).mul (hf.comp measurable_snd))
    (C := Cη * Lam * C) fun q => ?_
  rw [abs_mul, abs_mul]
  exact mul_le_mul (mul_le_mul (hCη _) (hBb _ _ _ _) (abs_nonneg _)
    ((abs_nonneg _).trans (hCη (τ - q.1)))) (hC _) (abs_nonneg _)
    (mul_nonneg ((abs_nonneg _).trans (hCη (τ - q.1))) ((abs_nonneg _).trans (hBb q.1 q.2 i j)))

omit [IsFiniteMeasure Γ'] in
include hη hmarg hBb in
theorem integrable_rawCoefficient (hLam : 0 ≤ Lam) (i j : Fin d) :
    Integrable (fun y => rawCoefficient η Bt Lam τ Γ' y i j) (averagedSlice η τ Γ') := by
  have := isFiniteMeasure_averagedSlice (τ := τ) hη hmarg
  have := isFiniteMeasure_fluxPosMeasure hη hBb hLam i j (τ := τ) (Γ' := Γ') ‹_›
  have h := Measure.integrable_toReal_rnDeriv (μ := fluxPosMeasure η Bt Lam τ i j Γ')
    (ν := averagedSlice η τ Γ')
  exact h.sub (integrable_const _)

omit [IsFiniteMeasure Γ'] in
include hη hmarg hBb in
theorem integrable_mul_rawCoefficient (hLam : 0 ≤ Lam) (i j : Fin d)
    {f : EvolutionAmbientState d → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ y, |f y| ≤ C) :
    Integrable (fun y => f y * rawCoefficient η Bt Lam τ Γ' y i j) (averagedSlice η τ Γ') := by
  refine (integrable_rawCoefficient hη hmarg hBb hLam i j).bdd_mul
    hf.aestronglyMeasurable (Filter.Eventually.of_forall fun y => by
      simpa [Real.norm_eq_abs] using hC y)

include hη hmarg hBm hBb in
/-- The quadratic form of `β` integrates against bounded measurable weights to that of `B`. -/
theorem integral_mul_quadForm_raw (hLam : 0 ≤ Lam) (ξ : PDE.Vec d)
    {f : EvolutionAmbientState d → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ y, |f y| ≤ C) :
    ∫ y, f y * (ξ ⬝ᵥ (rawCoefficient η Bt Lam τ Γ' y *ᵥ ξ)) ∂averagedSlice η τ Γ' =
      ∫ q, η (τ - q.1) * (ξ ⬝ᵥ (Bt q.1 q.2 *ᵥ ξ)) * f q.2 ∂Γ' := by
  have hI := fun i j => integrable_mul_rawCoefficient (τ := τ) hη hmarg hBb hLam i j hf hC
  have hJ := fun i j => integrable_fluxIntegrand hη hBm hBb i j (τ := τ) (Γ' := Γ') hf hC
  have hL : ∀ y, f y * (ξ ⬝ᵥ (rawCoefficient η Bt Lam τ Γ' y *ᵥ ξ)) =
      ∑ i, ∑ j, (ξ i * ξ j) * (f y * rawCoefficient η Bt Lam τ Γ' y i j) := fun y => by
    rw [quadForm_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hR : ∀ q : ℝ × EvolutionAmbientState d,
      η (τ - q.1) * (ξ ⬝ᵥ (Bt q.1 q.2 *ᵥ ξ)) * f q.2 =
      ∑ i, ∑ j, (ξ i * ξ j) * (η (τ - q.1) * Bt q.1 q.2 i j * f q.2) := fun q => by
    rw [quadForm_eq_sum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp_rw [hL, hR]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => (hI i j).const_mul _),
    integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => (hJ i j).const_mul _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ (fun j _ => (hI i j).const_mul _),
    integral_finsetSum _ (fun j _ => (hJ i j).const_mul _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, integral_const_mul,
    integral_mul_rawCoefficient hη hmarg hBm hBb hLam i j hf hC]

include hη hBm hBb in
theorem integrable_quadForm_fluxIntegrand (ξ : PDE.Vec d)
    {f : EvolutionAmbientState d → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ y, |f y| ≤ C) :
    Integrable (fun q : ℝ × EvolutionAmbientState d =>
      η (τ - q.1) * (ξ ⬝ᵥ (Bt q.1 q.2 *ᵥ ξ)) * f q.2) Γ' := by
  have hJ := fun i j => integrable_fluxIntegrand hη hBm hBb i j (τ := τ) (Γ' := Γ') hf hC
  have hR : ∀ q : ℝ × EvolutionAmbientState d,
      η (τ - q.1) * (ξ ⬝ᵥ (Bt q.1 q.2 *ᵥ ξ)) * f q.2 =
      ∑ i, ∑ j, (ξ i * ξ j) * (η (τ - q.1) * Bt q.1 q.2 i j * f q.2) := fun q => by
    rw [quadForm_eq_sum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp_rw [hR]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hJ i j).const_mul _

include hη in
theorem integrable_weight_mul {f : EvolutionAmbientState d → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : ∀ y, |f y| ≤ C) :
    Integrable (fun q : ℝ × EvolutionAmbientState d => η (τ - q.1) * f q.2) Γ' := by
  obtain ⟨Cη, hCη⟩ := hη.exists_bound
  have hηm : Measurable fun q : ℝ × EvolutionAmbientState d => η (τ - q.1) :=
    (hη.continuous.comp (continuous_const.sub continuous_fst)).measurable
  refine integrable_of_bounded_measurable (hηm.mul (hf.comp measurable_snd)) (C := Cη * C)
    fun q => ?_
  rw [abs_mul]
  exact mul_le_mul (hCη _) (hC _) (abs_nonneg _) ((abs_nonneg _).trans (hCη (τ - q.1)))

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
