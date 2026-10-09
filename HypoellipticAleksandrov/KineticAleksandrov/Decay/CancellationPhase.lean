module

public import Mathlib.MeasureTheory.Measure.Complex
public import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.VectorMeasure.WithDensity

/-!
# Phase projections of positive measures and their variation

Let `N` be a finite positive measure on `α × β` and `ψ : α × β → ℝ` a phase function.
The *phase projection* of `N` is the complex measure `ν` on `α` characterised on every
measurable `E` by `ν E = ∫_{E × β} exp (-i ψ) dN`.  (The Fourier projection of the
Doeblin--Fourier cancellation lemma is the case `ψ (w, z') = ξ · (z' - z₀)`.)

This file contains the two elementary variation estimates behind the cancellation lemma:

* `variation_le_map_fst_of_isPhaseProjection` (companion paper, (3.11)): the variation of
  the phase projection of `N` is bounded by the first marginal of `N`;
* `variation_sub_phaseFactor_smul_le` and `variation_add_le_of_phase_opposite` (companion paper,
  Lemma 3.7): if the mass of `F` is carried by `{|ψ - Φ| ≤ ε}`, the
  phase projection of `F` differs from `exp (-iΦ) • (F.map Prod.fst)` by variation at most
  `ε * F(α × β)`, and two such projections with opposite central phases and a common
  marginal add up to variation at most `2ε Θ`.

Complex measures are `MeasureTheory.ComplexMeasure`, and total variation is
`VectorMeasure.variation` (an `ℝ≥0∞`-valued measure).  No integrability is assumed
beyond finiteness of the positive measures, because the phase has modulus one.
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Decay

open MeasureTheory Set
open scoped ENNReal

/-- The phase factor `exp (-i θ)` of a real phase `θ`. -/
noncomputable def phaseFactor (θ : ℝ) : ℂ := Complex.exp (-Complex.I * (θ : ℂ))

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- `ν` is the phase projection of `N` for the phase `ψ`: on every measurable `E`, `ν E` is
`∫_{E × univ} exp (-i ψ) dN`. -/
def IsPhaseProjection (ψ : α × β → ℝ) (N : Measure (α × β)) (ν : ComplexMeasure α) : Prop :=
  ∀ E : Set α, MeasurableSet E → ν E = ∫ x in E ×ˢ (univ : Set β), phaseFactor (ψ x) ∂N

theorem norm_phaseFactor (θ : ℝ) : ‖phaseFactor θ‖ = 1 := by
  unfold phaseFactor
  rw [show -Complex.I * (θ : ℂ) = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The phase factor is a `1`-Lipschitz function of the phase. -/
theorem norm_phaseFactor_sub_le (θ Φ : ℝ) : ‖phaseFactor θ - phaseFactor Φ‖ ≤ |θ - Φ| := by
  have h : phaseFactor θ - phaseFactor Φ =
      phaseFactor Φ * (Complex.exp (Complex.I * ((-(θ - Φ) : ℝ) : ℂ)) - 1) := by
    unfold phaseFactor
    rw [mul_sub, ← Complex.exp_add, mul_one]
    congr 2
    · push_cast; ring
  rw [h, norm_mul, norm_phaseFactor, one_mul]
  have h2 := Real.norm_exp_I_mul_ofReal_sub_one_le (x := -(θ - Φ))
  rwa [norm_neg, Real.norm_eq_abs] at h2

theorem continuous_phaseFactor : Continuous phaseFactor := by
  unfold phaseFactor
  fun_prop

theorem measurable_phaseFactor_comp {ψ : α × β → ℝ} (hψ : Measurable ψ) :
    Measurable fun x => phaseFactor (ψ x) :=
  continuous_phaseFactor.measurable.comp hψ

theorem integrable_phaseFactor_comp {ψ : α × β → ℝ} (hψ : Measurable ψ)
    (N : Measure (α × β)) [IsFiniteMeasure N] :
    Integrable (fun x => phaseFactor (ψ x)) N :=
  Integrable.of_bound (measurable_phaseFactor_comp hψ).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun _ => (norm_phaseFactor _).le)

/-- The first marginal of a measure of a measurable set is the mass of its cylinder. -/
theorem map_fst_apply_eq {N : Measure (α × β)} {E : Set α} (hE : MeasurableSet E) :
    (N.map Prod.fst) E = N (E ×ˢ (univ : Set β)) := by
  rw [Measure.map_apply measurable_fst hE]
  congr 1
  ext x
  simp

/-- The real mass of a cylinder is the real mass of the first marginal. -/
theorem real_map_fst_apply_eq {N : Measure (α × β)} {E : Set α} (hE : MeasurableSet E) :
    (N.map Prod.fst).real E = N.real (E ×ˢ (univ : Set β)) := by
  simp [Measure.real, map_fst_apply_eq hE]

/-- Norm of the cylinder phase integral: the phase has modulus one. -/
theorem norm_integral_phase_le (ψ : α × β → ℝ) (N : Measure (α × β)) [IsFiniteMeasure N]
    (S : Set (α × β)) :
    ‖∫ x in S, phaseFactor (ψ x) ∂N‖ ≤ N.real S := by
  have := norm_setIntegral_le_of_norm_le_const_ae (μ := N) (s := S)
    (f := fun x => phaseFactor (ψ x)) (C := 1) (measure_lt_top N S)
    (Filter.Eventually.of_forall fun x => (norm_phaseFactor _).le)
  simpa using this

/-- Setwise phase-error estimate: if `F` is carried by `{|ψ - Φ| ≤ ε}` then on every
cylinder the phase integral differs from `exp (-iΦ)` times the mass by at most `ε` times
the mass. -/
theorem norm_integral_phase_sub_le {ψ : α × β → ℝ} (hψ : Measurable ψ)
    {F : Measure (α × β)} [IsFiniteMeasure F] {Φ ε : ℝ}
    (hsupp : ∀ᵐ x ∂F, |ψ x - Φ| ≤ ε) (S : Set (α × β)) :
    ‖(∫ x in S, phaseFactor (ψ x) ∂F) - phaseFactor Φ * (F.real S : ℂ)‖ ≤ ε * F.real S := by
  have hint : IntegrableOn (fun x => phaseFactor (ψ x)) S F :=
    (integrable_phaseFactor_comp hψ F).integrableOn
  have hconst : (∫ _ in S, phaseFactor Φ ∂F) = phaseFactor Φ * (F.real S : ℂ) := by
    rw [setIntegral_const, Complex.real_smul, mul_comm]
  rw [← hconst, ← integral_sub hint (integrableOn_const (measure_lt_top F S).ne)]
  refine norm_setIntegral_le_of_norm_le_const_ae (measure_lt_top F S) ?_
  filter_upwards [ae_restrict_of_ae hsupp] with x hx
  exact (norm_phaseFactor_sub_le _ _).trans hx

/-- A bound on the norm by the real mass is a bound on the extended norm by the mass. -/
theorem enorm_le_measure_of_norm_le_real {γ : Type*} [MeasurableSpace γ] {z : ℂ}
    {μ : Measure γ} [IsFiniteMeasure μ] {s : Set γ} (h : ‖z‖ ≤ μ.real s) : ‖z‖ₑ ≤ μ s := by
  rw [← ofReal_norm]
  exact (ENNReal.ofReal_le_ofReal h).trans_eq (ENNReal.ofReal_toReal (measure_ne_top μ s))

/-- (3.11), setwise form: the phase projection of a finite positive measure is
bounded on each measurable set by the mass of the corresponding cylinder. -/
theorem enorm_apply_le_of_isPhaseProjection {ψ : α × β → ℝ} {N : Measure (α × β)}
    [IsFiniteMeasure N] {ν : ComplexMeasure α} (hν : IsPhaseProjection ψ N ν)
    {E : Set α} (hE : MeasurableSet E) : ‖ν E‖ₑ ≤ N (E ×ˢ (univ : Set β)) := by
  rw [hν E hE]
  exact enorm_le_measure_of_norm_le_real (norm_integral_phase_le ψ N _)

/-- (3.11): the variation measure of the phase projection of a finite positive `N`
is dominated by the first marginal of `N`. -/
theorem variation_le_map_fst_of_isPhaseProjection {ψ : α × β → ℝ} {N : Measure (α × β)}
    [IsFiniteMeasure N] {ν : ComplexMeasure α} (hν : IsPhaseProjection ψ N ν) :
    ν.variation ≤ N.map Prod.fst :=
  VectorMeasure.variation_le_of_forall_enorm_le fun E hE => by
    rw [map_fst_apply_eq hE]
    exact enorm_apply_le_of_isPhaseProjection hν hE

/-- (3.11): `‖N̂‖_TV ≤ N (D × ℝᵈ)`, as an `ℝ≥0∞` inequality for the whole carrier. -/
theorem totalVariation_le_of_isPhaseProjection {ψ : α × β → ℝ} {N : Measure (α × β)}
    [IsFiniteMeasure N] {ν : ComplexMeasure α} (hν : IsPhaseProjection ψ N ν) :
    ν.variation univ ≤ N univ := by
  have h := variation_le_map_fst_of_isPhaseProjection hν univ
  rwa [Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ] at h

/-- (3.11), real form: `‖N̂‖_TV ≤ N (D × ℝᵈ)`. -/
theorem totalVariation_toReal_le_of_isPhaseProjection {ψ : α × β → ℝ}
    {N : Measure (α × β)} [IsFiniteMeasure N] {ν : ComplexMeasure α}
    (hν : IsPhaseProjection ψ N ν) : (ν.variation univ).toReal ≤ N.real univ :=
  ENNReal.toReal_mono (measure_ne_top N _) (totalVariation_le_of_isPhaseProjection hν)

/-- The finite positive measure `Θ` viewed as a complex measure. -/
noncomputable def positiveComplexMeasure (Θ : Measure α) [IsFiniteMeasure Θ] :
    ComplexMeasure α :=
  Θ.toSignedMeasure.toComplexMeasure 0

theorem positiveComplexMeasure_apply (Θ : Measure α) [IsFiniteMeasure Θ] {E : Set α}
    (hE : MeasurableSet E) : positiveComplexMeasure Θ E = (Θ.real E : ℂ) := by
  unfold positiveComplexMeasure
  rw [SignedMeasure.toComplexMeasure_apply, Measure.toSignedMeasure_apply_measurable hE]
  apply Complex.ext <;> simp

/-- A bound `‖z‖ ≤ ε * μ.real s` is a bound `‖z‖ₑ ≤ ofReal ε * μ s`. -/
theorem enorm_le_ofReal_mul_of_norm_le {γ : Type*} [MeasurableSpace γ] {z : ℂ}
    {μ : Measure γ} [IsFiniteMeasure μ] {s : Set γ} {ε : ℝ} (hε : 0 ≤ ε)
    (h : ‖z‖ ≤ ε * μ.real s) : ‖z‖ₑ ≤ ENNReal.ofReal ε * μ s := by
  rw [← ofReal_norm]
  calc ENNReal.ofReal ‖z‖ ≤ ENNReal.ofReal (ε * μ.real s) := ENNReal.ofReal_le_ofReal h
    _ = ENNReal.ofReal ε * μ s := by
      rw [ENNReal.ofReal_mul hε, Measure.real, ENNReal.ofReal_toReal (measure_ne_top μ s)]

/-- Lemma 3.7, first half: if `F` has first marginal `Θ` and is carried
by `{|ψ - Φ| ≤ ε}`, then `‖F̂ - exp (-iΦ) Θ‖_TV ≤ ε Θ(D)`; in fact the variation measure is
dominated by `ε Θ`. -/
theorem variation_sub_phaseFactor_smul_le {ψ : α × β → ℝ} (hψ : Measurable ψ)
    {F : Measure (α × β)} [IsFiniteMeasure F] {Θ : Measure α} [IsFiniteMeasure Θ]
    (hΘ : F.map Prod.fst = Θ) {Φ ε : ℝ} (hε : 0 ≤ ε) (hsupp : ∀ᵐ x ∂F, |ψ x - Φ| ≤ ε)
    {ν : ComplexMeasure α} (hν : IsPhaseProjection ψ F ν) :
    (ν - phaseFactor Φ • positiveComplexMeasure Θ).variation ≤ ENNReal.ofReal ε • Θ := by
  subst hΘ
  refine VectorMeasure.variation_le_of_forall_enorm_le fun E hE => ?_
  have h := norm_integral_phase_sub_le hψ hsupp (E ×ˢ (univ : Set β))
  rw [← real_map_fst_apply_eq hE] at h
  rw [sub_apply, smul_apply, positiveComplexMeasure_apply _ hE, hν E hE, smul_eq_mul,
    Measure.smul_apply, smul_eq_mul]
  exact enorm_le_ofReal_mul_of_norm_le hε h

/-- Lemma 3.7, total-variation form of the first half. -/
theorem totalVariation_sub_phaseFactor_smul_le {ψ : α × β → ℝ} (hψ : Measurable ψ)
    {F : Measure (α × β)} [IsFiniteMeasure F] {Θ : Measure α} [IsFiniteMeasure Θ]
    (hΘ : F.map Prod.fst = Θ) {Φ ε : ℝ} (hε : 0 ≤ ε) (hsupp : ∀ᵐ x ∂F, |ψ x - Φ| ≤ ε)
    {ν : ComplexMeasure α} (hν : IsPhaseProjection ψ F ν) :
    (ν - phaseFactor Φ • positiveComplexMeasure Θ).variation univ ≤
      ENNReal.ofReal ε * Θ univ := by
  simpa using variation_sub_phaseFactor_smul_le hψ hΘ hε hsupp hν univ

/-- Lemma 3.7, second half: for two measures with a common first marginal
`Θ`, carried near phases `Φ₁`, `Φ₂` with `exp (-iΦ₁) + exp (-iΦ₂) = 0`, the sum of the phase
projections has variation measure at most `2ε Θ`. -/
theorem variation_add_le_of_phaseFactor_add_eq_zero {ψ : α × β → ℝ} (hψ : Measurable ψ)
    {F₁ F₂ : Measure (α × β)} [IsFiniteMeasure F₁] [IsFiniteMeasure F₂]
    {Θ : Measure α} [IsFiniteMeasure Θ]
    (hΘ₁ : F₁.map Prod.fst = Θ) (hΘ₂ : F₂.map Prod.fst = Θ) {Φ₁ Φ₂ ε : ℝ} (hε : 0 ≤ ε)
    (hΦ : phaseFactor Φ₁ + phaseFactor Φ₂ = 0)
    (hsupp₁ : ∀ᵐ x ∂F₁, |ψ x - Φ₁| ≤ ε) (hsupp₂ : ∀ᵐ x ∂F₂, |ψ x - Φ₂| ≤ ε)
    {ν₁ ν₂ : ComplexMeasure α} (hν₁ : IsPhaseProjection ψ F₁ ν₁)
    (hν₂ : IsPhaseProjection ψ F₂ ν₂) :
    (ν₁ + ν₂).variation ≤ ENNReal.ofReal (2 * ε) • Θ := by
  have h₁ := variation_sub_phaseFactor_smul_le hψ hΘ₁ hε hsupp₁ hν₁
  have h₂ := variation_sub_phaseFactor_smul_le hψ hΘ₂ hε hsupp₂ hν₂
  have hc : phaseFactor Φ₂ = -phaseFactor Φ₁ := eq_neg_of_add_eq_zero_right hΦ
  have heq : ν₁ + ν₂ = (ν₁ - phaseFactor Φ₁ • positiveComplexMeasure Θ) +
      (ν₂ - phaseFactor Φ₂ • positiveComplexMeasure Θ) := by
    ext E
    simp only [add_apply, sub_apply, smul_apply, smul_eq_mul, hc]
    ring
  rw [heq]
  refine VectorMeasure.variation_add_le.trans ?_
  calc _ ≤ ENNReal.ofReal ε • Θ + ENNReal.ofReal ε • Θ := add_le_add h₁ h₂
    _ = ENNReal.ofReal (2 * ε) • Θ := by
      rw [← add_smul, ← ENNReal.ofReal_add hε hε, two_mul]

/-- Non-vacuity: a finite positive measure and a measurable phase have a phase projection.
The integrability needed by `withDensityᵥ` is supplied by `integrable_phaseFactor_comp`. -/
theorem exists_isPhaseProjection {ψ : α × β → ℝ} (hψ : Measurable ψ)
    (N : Measure (α × β)) [IsFiniteMeasure N] : ∃ ν : ComplexMeasure α, IsPhaseProjection ψ N ν :=
  ⟨(Measure.withDensityᵥ N fun x => phaseFactor (ψ x)).map Prod.fst, fun E hE => by
    rw [VectorMeasure.map_apply _ measurable_fst hE,
      withDensityᵥ_apply (integrable_phaseFactor_comp hψ N) (measurable_fst hE)]
    congr 2
    ext x
    simp⟩

/-- A phase projection is unique: a complex measure is determined by its values on
measurable sets. -/
theorem IsPhaseProjection.unique {ψ : α × β → ℝ} {N : Measure (α × β)}
    {ν ν' : ComplexMeasure α} (hν : IsPhaseProjection ψ N ν)
    (hν' : IsPhaseProjection ψ N ν') : ν = ν' := by
  ext E
  by_cases hE : MeasurableSet E
  · rw [hν E hE, hν' E hE]
  · rw [ν.not_measurable hE, ν'.not_measurable hE]

end HypoellipticAleksandrov.KineticAleksandrov.Decay
