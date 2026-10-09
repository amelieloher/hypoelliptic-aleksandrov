module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothed.Loewner
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.Matrix

/-!
# Almost-everywhere Loewner bounds of the Radon-Nikodym coefficient

For every fixed direction `ξ`, `λ |ξ|² ≤ ξ · β ξ ≤ Λ |ξ|²` holds `ν^δ_τ`-almost everywhere:
the set integrals of the difference are integrals of the averaged quadratic form of `B`
(`Smoothed/Quadratic.lean`), which has the sign of the Loewner bounds of `B`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

open MeasureTheory
open scoped ENNReal NNReal Matrix MatrixOrder

variable {d : ℕ} {δ : ℝ} {η : ℝ → ℝ} {τ lam Lam : ℝ} {Γ' : Measure (ℝ × EvolutionAmbientState d)}
  {Bt : ℝ → EvolutionAmbientState d → PDE.Mat d} [IsFiniteMeasure Γ']
  (hη : IsMollifier δ η) (hmarg : Γ'.map Prod.fst ≤ volume)
  (hBm : ∀ i j, Measurable fun q : ℝ × EvolutionAmbientState d => Bt q.1 q.2 i j)
  (hBb : ∀ t y i j, |Bt t y i j| ≤ Lam) (hLam : 0 ≤ Lam)

include hη hmarg hBm hBb hLam in
/-- Set integrals of `ξ · β ξ - c |ξ|²` against the averaged slice. -/
theorem setIntegral_quadForm_raw_sub (ξ : PDE.Vec d) (c : ℝ)
    {s : Set (EvolutionAmbientState d)} (hs : MeasurableSet s) :
    ∫ y in s, (ξ ⬝ᵥ (rawCoefficient η Bt Lam τ Γ' y *ᵥ ξ) - c * (ξ ⬝ᵥ ξ))
        ∂averagedSlice η τ Γ' =
      ∫ q, η (τ - q.1) * (ξ ⬝ᵥ (Bt q.1 q.2 *ᵥ ξ) - c * (ξ ⬝ᵥ ξ)) *
        s.indicator (fun _ => (1 : ℝ)) q.2 ∂Γ' := by
  have := isFiniteMeasure_averagedSlice (τ := τ) hη hmarg
  set f : EvolutionAmbientState d → ℝ := s.indicator fun _ => (1 : ℝ) with hfdef
  have hf : Measurable f := measurable_const.indicator hs
  have hC : ∀ y, |f y| ≤ 1 := fun y => by
    by_cases hy : y ∈ s <;> simp [hfdef, hy]
  have hqf : Integrable (fun y => ξ ⬝ᵥ (rawCoefficient η Bt Lam τ Γ' y *ᵥ ξ))
      (averagedSlice η τ Γ') := by
    simp_rw [quadForm_eq_sum]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (integrable_rawCoefficient hη hmarg hBb hLam i j).const_mul _
  have hfq : Integrable (fun y => f y * (ξ ⬝ᵥ (rawCoefficient η Bt Lam τ Γ' y *ᵥ ξ)))
      (averagedSlice η τ Γ') :=
    hqf.bdd_mul hf.aestronglyMeasurable (Filter.Eventually.of_forall fun y => by
      simpa [Real.norm_eq_abs] using hC y)
  have hf1 : Integrable f (averagedSlice η τ Γ') :=
    integrable_of_bounded_measurable' hf hC
  have e1 : ∫ y in s, (ξ ⬝ᵥ (rawCoefficient η Bt Lam τ Γ' y *ᵥ ξ) - c * (ξ ⬝ᵥ ξ))
        ∂averagedSlice η τ Γ' =
      ∫ y, f y * (ξ ⬝ᵥ (rawCoefficient η Bt Lam τ Γ' y *ᵥ ξ) - c * (ξ ⬝ᵥ ξ))
        ∂averagedSlice η τ Γ' := by
    rw [← integral_indicator hs]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    by_cases hy : y ∈ s <;> simp [hfdef, hy]
  have e2 : ∀ y, f y * (ξ ⬝ᵥ (rawCoefficient η Bt Lam τ Γ' y *ᵥ ξ) - c * (ξ ⬝ᵥ ξ)) =
      f y * (ξ ⬝ᵥ (rawCoefficient η Bt Lam τ Γ' y *ᵥ ξ)) - c * (ξ ⬝ᵥ ξ) * f y :=
    fun y => by ring
  have hJ := integrable_quadForm_fluxIntegrand hη hBm hBb ξ (τ := τ) (Γ' := Γ') hf hC
  have hK : Integrable (fun q : ℝ × EvolutionAmbientState d =>
      c * (ξ ⬝ᵥ ξ) * (η (τ - q.1) * f q.2)) Γ' :=
    (integrable_weight_mul hη hf hC (τ := τ) (Γ' := Γ')).const_mul _
  rw [e1]
  simp_rw [e2]
  rw [integral_sub hfq (hf1.const_mul _), integral_const_mul,
    integral_mul_quadForm_raw hη hmarg hBm hBb hLam ξ hf hC, integral_averagedSlice hη hf,
    ← integral_const_mul, ← integral_sub hJ hK]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  simp only; ring

omit [IsFiniteMeasure Γ'] in
include hη hmarg hBb hLam in
theorem integrable_quadForm_raw (ξ : PDE.Vec d) :
    Integrable (fun y => ξ ⬝ᵥ (rawCoefficient η Bt Lam τ Γ' y *ᵥ ξ)) (averagedSlice η τ Γ') := by
  simp_rw [quadForm_eq_sum]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (integrable_rawCoefficient hη hmarg hBb hLam i j).const_mul _

variable (hBl : ∀ t y, lam • (1 : PDE.Mat d) ≤ Bt t y ∧ Bt t y ≤ Lam • (1 : PDE.Mat d))

include hη hmarg hBm hBb hLam hBl in
/-- `λ |ξ|² ≤ ξ · β ξ` almost everywhere. -/
theorem ae_quadForm_lower (ξ : PDE.Vec d) :
    ∀ᵐ y ∂averagedSlice η τ Γ', lam * (ξ ⬝ᵥ ξ) ≤ ξ ⬝ᵥ (rawCoefficient η Bt Lam τ Γ' y *ᵥ ξ) := by
  have := isFiniteMeasure_averagedSlice (τ := τ) hη hmarg
  have hg : Integrable (fun y => ξ ⬝ᵥ (rawCoefficient η Bt Lam τ Γ' y *ᵥ ξ) - lam * (ξ ⬝ᵥ ξ))
      (averagedSlice η τ Γ') :=
    (integrable_quadForm_raw hη hmarg hBb hLam ξ).sub (integrable_const _)
  have h := ae_nonneg_of_forall_setIntegral_nonneg hg fun s hs _ => by
    rw [setIntegral_quadForm_raw_sub hη hmarg hBm hBb hLam ξ lam hs]
    refine integral_nonneg fun q => ?_
    refine mul_nonneg (mul_nonneg (hη.nonneg _) (sub_nonneg.2 ?_)) ?_
    · exact le_quadraticForm_of_smul_one_le (hBl q.1 q.2).1 ξ
    · exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  filter_upwards [h] with y hy
  exact sub_nonneg.1 hy

include hη hmarg hBm hBb hLam hBl in
/-- `ξ · β ξ ≤ Λ |ξ|²` almost everywhere. -/
theorem ae_quadForm_upper (ξ : PDE.Vec d) :
    ∀ᵐ y ∂averagedSlice η τ Γ', ξ ⬝ᵥ (rawCoefficient η Bt Lam τ Γ' y *ᵥ ξ) ≤ Lam * (ξ ⬝ᵥ ξ) := by
  have := isFiniteMeasure_averagedSlice (τ := τ) hη hmarg
  have hg : Integrable (fun y => Lam * (ξ ⬝ᵥ ξ) - ξ ⬝ᵥ (rawCoefficient η Bt Lam τ Γ' y *ᵥ ξ))
      (averagedSlice η τ Γ') :=
    (integrable_const _).sub (integrable_quadForm_raw hη hmarg hBb hLam ξ)
  have h := ae_nonneg_of_forall_setIntegral_nonneg hg fun s hs _ => by
    have e : ∫ y in s, (Lam * (ξ ⬝ᵥ ξ) - ξ ⬝ᵥ (rawCoefficient η Bt Lam τ Γ' y *ᵥ ξ))
          ∂averagedSlice η τ Γ' =
        -∫ y in s, (ξ ⬝ᵥ (rawCoefficient η Bt Lam τ Γ' y *ᵥ ξ) - Lam * (ξ ⬝ᵥ ξ))
          ∂averagedSlice η τ Γ' := by
      rw [← integral_neg]
      exact integral_congr_ae (Filter.Eventually.of_forall fun y => by simp)
    rw [e, setIntegral_quadForm_raw_sub hη hmarg hBm hBb hLam ξ Lam hs, neg_nonneg]
    refine integral_nonpos fun q => ?_
    refine mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (hη.nonneg _)
      (sub_nonpos.2 ?_)) ?_
    · exact quadraticForm_le_of_le_smul_one (hBl q.1 q.2).2 ξ
    · exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  filter_upwards [h] with y hy
  exact sub_nonneg.1 hy

include hη hmarg hBm hBb hLam hBl in
/-- The raw coefficient satisfies the dense-direction bounds almost everywhere. -/
theorem ae_isGoodCoefficient :
    ∀ᵐ y ∂averagedSlice η τ Γ', IsGoodCoefficient lam Lam (rawCoefficient η Bt Lam τ Γ' y) :=
  ae_all_iff.2 fun n => (ae_quadForm_lower hη hmarg hBm hBb hLam hBl (denseDirections d n)).and
    (ae_quadForm_upper hη hmarg hBm hBb hLam hBl (denseDirections d n))

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
