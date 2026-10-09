module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothed.Ae

/-!
# The averaged coefficient `β`

The smoothed Green measure: the Borel symmetric matrix field `β = β_τ` with `(Bν)^δ_τ = β ν^δ_τ`
and `λ I ≤ β ≤ Λ I` everywhere (after modification on a `ν^δ_τ`-null Borel set).
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

open MeasureTheory
open scoped ENNReal NNReal Matrix MatrixOrder

variable {d : ℕ} {δ : ℝ} {η : ℝ → ℝ} {τ lam Lam : ℝ} {Γ' : Measure (ℝ × EvolutionAmbientState d)}
  {Bt : ℝ → EvolutionAmbientState d → PDE.Mat d}

open Classical in
/-- The averaged coefficient `β_τ`: the Radon-Nikodym density of the averaged flux with respect
to the averaged slice, replaced by `λ I` on the (Borel, null) set where the dense-direction
Loewner bounds fail. -/
def averagedCoefficient (η : ℝ → ℝ) (Bt : ℝ → EvolutionAmbientState d → PDE.Mat d)
    (lam Lam τ : ℝ) (Γ' : Measure (ℝ × EvolutionAmbientState d))
    (y : EvolutionAmbientState d) : PDE.Mat d :=
  if IsGoodCoefficient lam Lam (rawCoefficient η Bt Lam τ Γ' y) then
    rawCoefficient η Bt Lam τ Γ' y else lam • (1 : PDE.Mat d)

theorem fluxPosMeasure_symm (hBs : ∀ t y, (Bt t y).IsSymm) (i j : Fin d) :
    fluxPosMeasure η Bt Lam τ i j Γ' = fluxPosMeasure η Bt Lam τ j i Γ' := by
  unfold fluxPosMeasure
  have : fluxWeight η Bt Lam τ i j = fluxWeight η Bt Lam τ j i := by
    funext q
    simp only [fluxWeight, (hBs q.1 q.2).apply i j]
  rw [this]

theorem isSymm_rawCoefficient (hBs : ∀ t y, (Bt t y).IsSymm) (y : EvolutionAmbientState d) :
    (rawCoefficient η Bt Lam τ Γ' y).IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  simp only [rawCoefficient, Matrix.of_apply, fluxPosMeasure_symm (τ := τ) (Γ' := Γ') hBs i j]

theorem measurable_quadForm_raw (ξ : PDE.Vec d) :
    Measurable fun y => ξ ⬝ᵥ (rawCoefficient η Bt Lam τ Γ' y *ᵥ ξ) := by
  simp_rw [quadForm_eq_sum]
  exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
    (measurable_rawCoefficient i j).const_mul _

theorem measurableSet_isGood :
    MeasurableSet {y | IsGoodCoefficient lam Lam (rawCoefficient η Bt Lam τ Γ' y)} := by
  have : {y | IsGoodCoefficient lam Lam (rawCoefficient η Bt Lam τ Γ' y)} =
      ⋂ n, ({y | lam * (denseDirections d n ⬝ᵥ denseDirections d n) ≤
        denseDirections d n ⬝ᵥ (rawCoefficient η Bt Lam τ Γ' y *ᵥ denseDirections d n)} ∩
      {y | denseDirections d n ⬝ᵥ (rawCoefficient η Bt Lam τ Γ' y *ᵥ denseDirections d n) ≤
        Lam * (denseDirections d n ⬝ᵥ denseDirections d n)}) := by
    ext y
    simp [IsGoodCoefficient]
  rw [this]
  exact MeasurableSet.iInter fun n => (measurableSet_le measurable_const
    (measurable_quadForm_raw _)).inter (measurableSet_le (measurable_quadForm_raw _)
    measurable_const)

theorem measurable_averagedCoefficient (i j : Fin d) :
    Measurable fun y => averagedCoefficient η Bt lam Lam τ Γ' y i j := by
  classical
  have : (fun y => averagedCoefficient η Bt lam Lam τ Γ' y i j) = fun y =>
      if IsGoodCoefficient lam Lam (rawCoefficient η Bt Lam τ Γ' y) then
        rawCoefficient η Bt Lam τ Γ' y i j else (lam • (1 : PDE.Mat d)) i j := by
    funext y
    unfold averagedCoefficient
    split_ifs <;> rfl
  rw [this]
  exact Measurable.ite measurableSet_isGood (measurable_rawCoefficient i j) measurable_const

/-- **The averaged coefficient is an admissible coefficient** (everywhere Loewner bounds). -/
theorem isAdmissibleCoefficient_averagedCoefficient
    (hBs : ∀ t y, (Bt t y).IsSymm)
    (hBl : ∀ t y, lam • (1 : PDE.Mat d) ≤ Bt t y ∧ Bt t y ≤ Lam • (1 : PDE.Mat d)) :
    IsAdmissibleCoefficient lam Lam (averagedCoefficient η Bt lam Lam τ Γ') := by
  have hle : lam • (1 : PDE.Mat d) ≤ Lam • (1 : PDE.Mat d) :=
    (hBl 0 0).1.trans (hBl 0 0).2
  refine ⟨measurable_averagedCoefficient, fun y => ?_, fun y => ?_, fun y => ?_⟩
  · unfold averagedCoefficient
    split_ifs
    · exact isSymm_rawCoefficient hBs y
    · exact Matrix.isSymm_one.smul _
  · unfold averagedCoefficient
    split_ifs with h
    · exact (loewner_of_isGood (isSymm_rawCoefficient hBs y) h).1
    · exact le_rfl
  · unfold averagedCoefficient
    split_ifs with h
    · exact (loewner_of_isGood (isSymm_rawCoefficient hBs y) h).2
    · exact hle

variable [IsFiniteMeasure Γ']
  (hη : IsMollifier δ η) (hmarg : Γ'.map Prod.fst ≤ volume)
  (hBm : ∀ i j, Measurable fun q : ℝ × EvolutionAmbientState d => Bt q.1 q.2 i j)
  (hBb : ∀ t y i j, |Bt t y i j| ≤ Lam) (hLam : 0 ≤ Lam)
  (hBl : ∀ t y, lam • (1 : PDE.Mat d) ≤ Bt t y ∧ Bt t y ≤ Lam • (1 : PDE.Mat d))

include hη hmarg hBm hBb hLam hBl in
theorem averagedCoefficient_ae_eq_raw :
    averagedCoefficient η Bt lam Lam τ Γ' =ᵐ[averagedSlice η τ Γ']
      rawCoefficient η Bt Lam τ Γ' := by
  filter_upwards [ae_isGoodCoefficient hη hmarg hBm hBb hLam hBl] with y hy
  simp [averagedCoefficient, hy]

include hη hmarg hBm hBb hLam hBl in
/-- **Radon-Nikodym form of the averaged flux**: `β` integrates against bounded measurable
`f` to the averaged flux, `∫ f β_{ij} dν^δ_τ = ∫ η_δ(τ - t) B_{ij}(t, y') f(y') dΓ'`. -/
theorem integral_mul_averagedCoefficient (i j : Fin d)
    {f : EvolutionAmbientState d → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ y, |f y| ≤ C) :
    ∫ y, f y * averagedCoefficient η Bt lam Lam τ Γ' y i j ∂averagedSlice η τ Γ' =
      ∫ q, η (τ - q.1) * Bt q.1 q.2 i j * f q.2 ∂Γ' := by
  rw [← integral_mul_rawCoefficient hη hmarg hBm hBb hLam i j hf hC]
  refine integral_congr_ae ?_
  filter_upwards [averagedCoefficient_ae_eq_raw hη hmarg hBm hBb hLam hBl] with y hy
  rw [hy]

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
