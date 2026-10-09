module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothed.Slice

/-!
# The Radon-Nikodym coefficient of the averaged flux

The smoothed Green measure: the averaged flux `(Bν)^δ_τ` is absolutely continuous with respect to
`ν^δ_τ`; its density `β` is a Borel symmetric matrix field with `λ I ≤ β ≤ Λ I`
`ν^δ_τ`-almost everywhere.  Here the entries of `β` are the (shifted) Radon-Nikodym derivatives of
the positive measures of `Smoothed/Slice.lean`, and the key bridge
`∫ f β_{ij} dν^δ_τ = ∫ η_δ(τ - t) B_{ij}(t, y') f(y') dΓ'` is proved for bounded measurable `f`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

open MeasureTheory
open scoped ENNReal NNReal

variable {d : ℕ} {δ : ℝ} {η : ℝ → ℝ} {τ Lam : ℝ} {Γ' : Measure (ℝ × EvolutionAmbientState d)}
  {Bt : ℝ → EvolutionAmbientState d → PDE.Mat d}

/-- The unclamped coefficient: entries are the Radon-Nikodym derivatives of the flux measures
(shifted by `-Λ`) with respect to the averaged slice. -/
def rawCoefficient (η : ℝ → ℝ) (Bt : ℝ → EvolutionAmbientState d → PDE.Mat d) (Lam τ : ℝ)
    (Γ' : Measure (ℝ × EvolutionAmbientState d)) (y : EvolutionAmbientState d) : PDE.Mat d :=
  Matrix.of fun i j =>
    ((fluxPosMeasure η Bt Lam τ i j Γ').rnDeriv (averagedSlice η τ Γ') y).toReal - Lam

theorem measurable_rawCoefficient (i j : Fin d) :
    Measurable fun y => rawCoefficient η Bt Lam τ Γ' y i j :=
  (Measure.measurable_rnDeriv _ _).ennreal_toReal.sub_const _

variable [IsFiniteMeasure Γ']
  (hη : IsMollifier δ η) (hmarg : Γ'.map Prod.fst ≤ volume)
  (hBm : ∀ i j, Measurable fun q : ℝ × EvolutionAmbientState d => Bt q.1 q.2 i j)
  (hBb : ∀ t y i j, |Bt t y i j| ≤ Lam)

omit [IsFiniteMeasure Γ'] in
theorem integrable_of_bounded_measurable {μ : Measure (ℝ × EvolutionAmbientState d)}
    [IsFiniteMeasure μ] {g : ℝ × EvolutionAmbientState d → ℝ} (hg : Measurable g) {C : ℝ}
    (hC : ∀ q, |g q| ≤ C) : Integrable g μ :=
  Integrable.of_bound hg.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun q => by simpa [Real.norm_eq_abs] using hC q)

theorem integrable_of_bounded_measurable' {μ : Measure (EvolutionAmbientState d)}
    [IsFiniteMeasure μ] {g : EvolutionAmbientState d → ℝ} (hg : Measurable g) {C : ℝ}
    (hC : ∀ q, |g q| ≤ C) : Integrable g μ :=
  Integrable.of_bound hg.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun q => by simpa [Real.norm_eq_abs] using hC q)

include hη hmarg hBm hBb in
/-- **Bridge**: `β_{ij}` integrates against bounded measurable `f` to the averaged flux. -/
theorem integral_mul_rawCoefficient (hLam : 0 ≤ Lam) (i j : Fin d)
    {f : EvolutionAmbientState d → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ y, |f y| ≤ C) :
    ∫ y, f y * rawCoefficient η Bt Lam τ Γ' y i j ∂averagedSlice η τ Γ' =
      ∫ q, η (τ - q.1) * Bt q.1 q.2 i j * f q.2 ∂Γ' := by
  have := isFiniteMeasure_averagedSlice (τ := τ) hη hmarg
  have := isFiniteMeasure_fluxPosMeasure hη hBb hLam i j (τ := τ) (Γ' := Γ') ‹_›
  have hac := fluxPosMeasure_absolutelyContinuous hη hBb hLam i j (τ := τ) (Γ' := Γ')
  obtain ⟨Cη, hCη⟩ := hη.exists_bound
  have hηm : Measurable fun q : ℝ × EvolutionAmbientState d => η (τ - q.1) :=
    (hη.continuous.comp (continuous_const.sub continuous_fst)).measurable
  have hfq : Measurable fun q : ℝ × EvolutionAmbientState d => f q.2 := hf.comp measurable_snd
  have hI1 : Integrable (fun y => (((fluxPosMeasure η Bt Lam τ i j Γ').rnDeriv
      (averagedSlice η τ Γ') y).toReal * f y)) (averagedSlice η τ Γ') :=
    (integrable_toReal_rnDeriv_mul_iff hac).2 (integrable_of_bounded_measurable' hf hC)
  have hI2 : Integrable (fun y => f y) (averagedSlice η τ Γ') :=
    integrable_of_bounded_measurable' hf hC
  have e1 : ∫ y, f y * rawCoefficient η Bt Lam τ Γ' y i j ∂averagedSlice η τ Γ' =
      ∫ y, f y ∂fluxPosMeasure η Bt Lam τ i j Γ' - Lam * ∫ y, f y ∂averagedSlice η τ Γ' := by
    have : ∀ y, f y * rawCoefficient η Bt Lam τ Γ' y i j =
        (((fluxPosMeasure η Bt Lam τ i j Γ').rnDeriv (averagedSlice η τ Γ') y).toReal * f y)
          - Lam * f y := fun y => by
      simp only [rawCoefficient, Matrix.of_apply]; ring
    simp_rw [this]
    rw [integral_sub hI1 (hI2.const_mul _), integral_const_mul,
      integral_toReal_rnDeriv_mul hac]
  rw [e1, integral_fluxPosMeasure hη hBm hBb i j hf, integral_averagedSlice hη hf,
    ← integral_const_mul, ← integral_sub]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    simp only; ring
  · refine integrable_of_bounded_measurable (((hηm.mul ((hBm i j).add_const Lam)).mul hfq))
      (C := Cη * (2 * Lam) * C) fun q => ?_
    rw [abs_mul, abs_mul]
    have h1 := hCη (τ - q.1)
    have h2 : |Bt q.1 q.2 i j + Lam| ≤ 2 * Lam := by
      have := abs_le.1 (hBb q.1 q.2 i j)
      rw [abs_le]; constructor <;> linarith
    exact mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1))
      (hC _) (abs_nonneg _) (mul_nonneg ((abs_nonneg _).trans h1) (by linarith))
  · exact (integrable_of_bounded_measurable (hηm.mul hfq) (C := Cη * C) fun q => by
      simp only [Pi.mul_apply]
      rw [abs_mul]; exact mul_le_mul (hCη _) (hC _) (abs_nonneg _)
        ((abs_nonneg _).trans (hCη (τ - q.1)))).const_mul _

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
