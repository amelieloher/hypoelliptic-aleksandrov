module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothed.Mollifier
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Calculus
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Time-averaged slices

The smoothed Green measure.  A finite measure `Γ'` on `ℝ × ℝ^{2d}` (the Green measure with the
elapsed time as a real coordinate) is averaged against the mollifier in time:
`ν^δ_τ = ∫ η_δ(τ - s) ν_s ds` is the second marginal of `η_δ(τ - t) dΓ'(t, y')`.  The flux
`(Bν)^δ_τ` has entries `∫ η_δ(τ - s) B_{ij}(s, ·) ν_s ds`; to stay among positive measures the
entries are encoded by the positive measures with density `η_δ (B_{ij} + Λ)`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

open MeasureTheory
open scoped ENNReal NNReal

variable {d : ℕ}

/-- The time weight `η(τ - t)` as a nonnegative number. -/
def timeWeight (η : ℝ → ℝ) (τ : ℝ) (q : ℝ × EvolutionAmbientState d) : ℝ≥0 :=
  (η (τ - q.1)).toNNReal

/-- The positive density `η(τ - t) (B_{ij}(t, y') + Λ)`. -/
def fluxWeight (η : ℝ → ℝ) (Bt : ℝ → EvolutionAmbientState d → PDE.Mat d) (Lam τ : ℝ)
    (i j : Fin d) (q : ℝ × EvolutionAmbientState d) : ℝ≥0 :=
  (η (τ - q.1) * (Bt q.1 q.2 i j + Lam)).toNNReal

/-- The time-averaged slice `ν^δ_τ`. -/
def averagedSlice (η : ℝ → ℝ) (τ : ℝ) (Γ' : Measure (ℝ × EvolutionAmbientState d)) :
    Measure (EvolutionAmbientState d) :=
  (Γ'.withDensity fun q => (timeWeight η τ q : ℝ≥0∞)).map Prod.snd

/-- The positive measure encoding the `(i, j)` entry of the averaged flux, shifted by `Λ`. -/
def fluxPosMeasure (η : ℝ → ℝ) (Bt : ℝ → EvolutionAmbientState d → PDE.Mat d) (Lam τ : ℝ)
    (i j : Fin d) (Γ' : Measure (ℝ × EvolutionAmbientState d)) :
    Measure (EvolutionAmbientState d) :=
  (Γ'.withDensity fun q => (fluxWeight η Bt Lam τ i j q : ℝ≥0∞)).map Prod.snd

variable {δ : ℝ} {η : ℝ → ℝ} {τ : ℝ} {Lam : ℝ} {Γ' : Measure (ℝ × EvolutionAmbientState d)}
  {Bt : ℝ → EvolutionAmbientState d → PDE.Mat d}

theorem measurable_timeWeight (hη : IsMollifier δ η) (τ : ℝ) :
    Measurable (timeWeight η τ : ℝ × EvolutionAmbientState d → ℝ≥0) :=
  (hη.continuous.comp (continuous_const.sub continuous_fst)).measurable.real_toNNReal

theorem coe_timeWeight (hη : IsMollifier δ η) (q : ℝ × EvolutionAmbientState d) :
    (timeWeight η τ q : ℝ) = η (τ - q.1) := by
  simp [timeWeight, hη.nonneg]

/-- Integrals against the averaged slice. -/
theorem integral_averagedSlice (hη : IsMollifier δ η) {f : EvolutionAmbientState d → ℝ}
    (hf : Measurable f) :
    ∫ y, f y ∂averagedSlice η τ Γ' = ∫ q, η (τ - q.1) * f q.2 ∂Γ' := by
  unfold averagedSlice
  rw [integral_map measurable_snd.aemeasurable hf.aestronglyMeasurable,
    integral_withDensity_eq_integral_smul (measurable_timeWeight hη τ)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  simp only [NNReal.smul_def, smul_eq_mul]
  rw [coe_timeWeight hη]

/-- The averaged slice has mass at most one when the time marginal of `Γ'` is dominated by
Lebesgue measure (`ν_s` has mass at most one) and `∫ η = 1`. -/
theorem averagedSlice_univ_le (hη : IsMollifier δ η) (hmarg : Γ'.map Prod.fst ≤ volume) :
    averagedSlice η τ Γ' Set.univ ≤ 1 := by
  unfold averagedSlice
  rw [Measure.map_apply measurable_snd MeasurableSet.univ, Set.preimage_univ,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hw : ∀ q : ℝ × EvolutionAmbientState d,
      (timeWeight η τ q : ℝ≥0∞) = ENNReal.ofReal (η (τ - q.1)) := fun q => rfl
  simp_rw [hw]
  have hmeas : Measurable fun t : ℝ => ENNReal.ofReal (η (τ - t)) :=
    ENNReal.measurable_ofReal.comp
      (hη.continuous.comp (continuous_const.sub continuous_id)).measurable
  have h1 : ∫⁻ q, ENNReal.ofReal (η (τ - q.1)) ∂Γ' =
      ∫⁻ t, ENNReal.ofReal (η (τ - t)) ∂(Γ'.map Prod.fst) :=
    (lintegral_map hmeas measurable_fst).symm
  rw [h1]
  refine (lintegral_mono' hmarg le_rfl).trans ?_
  have hint : Integrable (fun t : ℝ => η (τ - t)) :=
    Integrable.comp_sub_left hη.integrable τ
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun t => hη.nonneg _),
    integral_sub_left_eq_self η volume τ, hη.integral_eq_one]
  simp

theorem isFiniteMeasure_averagedSlice (hη : IsMollifier δ η) (hmarg : Γ'.map Prod.fst ≤ volume) :
    IsFiniteMeasure (averagedSlice η τ Γ') :=
  ⟨lt_of_le_of_lt (averagedSlice_univ_le hη hmarg) ENNReal.one_lt_top⟩

theorem averagedSlice_real_univ_le (hη : IsMollifier δ η) (hmarg : Γ'.map Prod.fst ≤ volume) :
    (averagedSlice η τ Γ').real Set.univ ≤ 1 := by
  have := isFiniteMeasure_averagedSlice (τ := τ) hη hmarg
  have h := averagedSlice_univ_le (τ := τ) hη hmarg
  rw [Measure.real]
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using h)

section Flux

variable (hη : IsMollifier δ η)
  (hBm : ∀ i j, Measurable fun q : ℝ × EvolutionAmbientState d => Bt q.1 q.2 i j)
  (hBb : ∀ t y i j, |Bt t y i j| ≤ Lam)

include hη hBb in
theorem coe_fluxWeight (i j : Fin d) (q : ℝ × EvolutionAmbientState d) :
    (fluxWeight η Bt Lam τ i j q : ℝ) = η (τ - q.1) * (Bt q.1 q.2 i j + Lam) := by
  have h1 : 0 ≤ Bt q.1 q.2 i j + Lam := by
    have := neg_abs_le (Bt q.1 q.2 i j)
    have := hBb q.1 q.2 i j
    linarith
  simp [fluxWeight, mul_nonneg (hη.nonneg _) h1]

include hη hBm in
theorem measurable_fluxWeight (i j : Fin d) :
    Measurable (fluxWeight η Bt Lam τ i j : ℝ × EvolutionAmbientState d → ℝ≥0) := by
  refine Measurable.real_toNNReal (Measurable.mul ?_ ((hBm i j).add_const Lam))
  exact (hη.continuous.comp (continuous_const.sub continuous_fst)).measurable

include hη hBm hBb in
/-- Integrals against the positive flux measure. -/
theorem integral_fluxPosMeasure (i j : Fin d) {f : EvolutionAmbientState d → ℝ}
    (hf : Measurable f) :
    ∫ y, f y ∂fluxPosMeasure η Bt Lam τ i j Γ' =
      ∫ q, η (τ - q.1) * (Bt q.1 q.2 i j + Lam) * f q.2 ∂Γ' := by
  unfold fluxPosMeasure
  rw [integral_map measurable_snd.aemeasurable hf.aestronglyMeasurable,
    integral_withDensity_eq_integral_smul (measurable_fluxWeight hη hBm i j)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  simp only [NNReal.smul_def, smul_eq_mul]
  rw [coe_fluxWeight hη hBb]

include hη hBb in
theorem fluxPosMeasure_apply_le (hLam : 0 ≤ Lam) (i j : Fin d) {s : Set (EvolutionAmbientState d)}
    (hs : MeasurableSet s) :
    fluxPosMeasure η Bt Lam τ i j Γ' s ≤
      ENNReal.ofReal (2 * Lam) * averagedSlice η τ Γ' s := by
  unfold fluxPosMeasure averagedSlice
  rw [Measure.map_apply measurable_snd hs, Measure.map_apply measurable_snd hs,
    withDensity_apply _ (measurable_snd hs), withDensity_apply _ (measurable_snd hs),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun q => ?_
  have h1 : (fluxWeight η Bt Lam τ i j q : ℝ≥0∞) = ENNReal.ofReal (η (τ - q.1) *
      (Bt q.1 q.2 i j + Lam)) := rfl
  have h2 : (timeWeight η τ q : ℝ≥0∞) = ENNReal.ofReal (η (τ - q.1)) := rfl
  rw [h1, h2, ← ENNReal.ofReal_mul (by linarith)]
  refine ENNReal.ofReal_le_ofReal ?_
  have := (abs_le.1 (hBb q.1 q.2 i j)).2
  have := hη.nonneg (τ - q.1)
  nlinarith

include hη hBb in
theorem fluxPosMeasure_le (hLam : 0 ≤ Lam) (i j : Fin d) :
    fluxPosMeasure η Bt Lam τ i j Γ' ≤ ENNReal.ofReal (2 * Lam) • averagedSlice η τ Γ' :=
  Measure.le_iff.2 fun s hs => by
    simpa using fluxPosMeasure_apply_le hη hBb hLam i j hs

include hη hBb in
theorem fluxPosMeasure_absolutelyContinuous (hLam : 0 ≤ Lam) (i j : Fin d) :
    fluxPosMeasure η Bt Lam τ i j Γ' ≪ averagedSlice η τ Γ' :=
  Measure.absolutelyContinuous_of_le_smul (fluxPosMeasure_le hη hBb hLam i j)

include hη hBb in
theorem isFiniteMeasure_fluxPosMeasure (hLam : 0 ≤ Lam) (i j : Fin d)
    (hfin : IsFiniteMeasure (averagedSlice η τ Γ')) :
    IsFiniteMeasure (fluxPosMeasure η Bt Lam τ i j Γ') :=
  haveI := hfin
  haveI : IsFiniteMeasure (ENNReal.ofReal (2 * Lam) • averagedSlice η τ Γ') :=
    Measure.smul_finite _ ENNReal.ofReal_ne_top
  isFiniteMeasure_of_le (ENNReal.ofReal (2 * Lam) • averagedSlice η τ Γ')
    (fluxPosMeasure_le hη hBb hLam i j)

end Flux

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
