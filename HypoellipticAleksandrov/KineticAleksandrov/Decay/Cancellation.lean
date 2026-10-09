module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.CancellationPhase
public import Mathlib.MeasureTheory.Measure.Sub

/-!
# Doeblin--Fourier cancellation (companion paper, Lemma 3.7)

Companion paper, Lemma 3.7.

Let `M`, `F₁`, `F₂` be finite positive measures on `α × β` (`α` plays the role of the
velocity carrier `D`, `β` of the transported variable `ℝᵈ`) with `F₁ + F₂ ≤ M` and
`F_i.map Prod.fst = Θ`.  Let `ψ : α × β → ℝ` be measurable (for the paper,
`ψ (w, z') = ξ · (z' - z₀)`), `0 ≤ ε < 1`, and `Φ₁ Φ₂` with
`exp (-iΦ₁) + exp (-iΦ₂) = 0`, with `F_i` carried by `{|ψ - Φ_i| ≤ ε}`.  If `ν` is the
phase projection of `M` (`IsPhaseProjection ψ M ν`, i.e. the complex measure
`E ↦ ∫_{E × β} exp (-iψ) dM`), then
`‖ν‖_TV ≤ M(α × β) - 2 (1 - ε) Θ(α)`.

The proof is the source's: the remainder `M - F₁ - F₂` contributes at most its mass
((3.11)), while the two phase projections cancel up to `2ε Θ`
(Lemma 3.7).  We prove the stronger domination
`ν.variation ≤ (M - (F₁ + F₂)).map Prod.fst + ofReal (2ε) • Θ` of variation measures.
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Decay

open MeasureTheory Set
open scoped ENNReal

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Integral of the phase over a set splits along `M = (M - (F₁ + F₂)) + F₁ + F₂`. -/
theorem integral_phase_split {ψ : α × β → ℝ} (hψ : Measurable ψ)
    {M F₁ F₂ : Measure (α × β)} [IsFiniteMeasure M] [IsFiniteMeasure F₁]
    [IsFiniteMeasure F₂] (hF : F₁ + F₂ ≤ M) (S : Set (α × β)) :
    ∫ x in S, phaseFactor (ψ x) ∂M =
      ∫ x in S, phaseFactor (ψ x) ∂(M - (F₁ + F₂)) + ∫ x in S, phaseFactor (ψ x) ∂F₁ +
        ∫ x in S, phaseFactor (ψ x) ∂F₂ := by
  have : IsFiniteMeasure (M - (F₁ + F₂)) := isFiniteMeasure_of_le M Measure.sub_le
  have hM : M = (M - (F₁ + F₂)) + F₁ + F₂ := by
    rw [add_assoc, Measure.sub_add_cancel_of_le hF]
  have hi : ∀ (N : Measure (α × β)) [IsFiniteMeasure N],
      Integrable (fun x => phaseFactor (ψ x)) (N.restrict S) := fun N _ =>
    (integrable_phaseFactor_comp hψ N).restrict
  conv_lhs => rw [hM]
  rw [Measure.restrict_add, Measure.restrict_add,
    integral_add_measure (by exact (hi _).add_measure (hi _)) (hi _),
    integral_add_measure (hi _) (hi _)]

/-- Setwise form of the cancellation estimate. -/
theorem norm_apply_le_cancellation {ψ : α × β → ℝ} (hψ : Measurable ψ)
    {M F₁ F₂ : Measure (α × β)} [IsFiniteMeasure M] [IsFiniteMeasure F₁]
    [IsFiniteMeasure F₂] (hF : F₁ + F₂ ≤ M) {Θ : Measure α}
    (hΘ₁ : F₁.map Prod.fst = Θ) (hΘ₂ : F₂.map Prod.fst = Θ) {Φ₁ Φ₂ ε : ℝ}
    (hΦ : phaseFactor Φ₁ + phaseFactor Φ₂ = 0)
    (hsupp₁ : ∀ᵐ x ∂F₁, |ψ x - Φ₁| ≤ ε) (hsupp₂ : ∀ᵐ x ∂F₂, |ψ x - Φ₂| ≤ ε)
    {ν : ComplexMeasure α} (hν : IsPhaseProjection ψ M ν) {E : Set α} (hE : MeasurableSet E) :
    ‖ν E‖ ≤ (M - (F₁ + F₂)).real (E ×ˢ (univ : Set β)) + 2 * ε * Θ.real E := by
  set S : Set (α × β) := E ×ˢ (univ : Set β) with hS
  have h₁ := norm_integral_phase_sub_le hψ hsupp₁ S
  have h₂ := norm_integral_phase_sub_le hψ hsupp₂ S
  have hr₁ : F₁.real S = Θ.real E := by rw [← hΘ₁, real_map_fst_apply_eq hE]
  have hr₂ : F₂.real S = Θ.real E := by rw [← hΘ₂, real_map_fst_apply_eq hE]
  rw [hr₁] at h₁
  rw [hr₂] at h₂
  have hν' : ν E = (∫ x in S, phaseFactor (ψ x) ∂(M - (F₁ + F₂))) +
      ((∫ x in S, phaseFactor (ψ x) ∂F₁) - phaseFactor Φ₁ * (Θ.real E : ℂ)) +
      ((∫ x in S, phaseFactor (ψ x) ∂F₂) - phaseFactor Φ₂ * (Θ.real E : ℂ)) +
      (phaseFactor Φ₁ + phaseFactor Φ₂) * (Θ.real E : ℂ) := by
    rw [hν E hE, integral_phase_split hψ hF]
    ring
  rw [hΦ, zero_mul, add_zero] at hν'
  have hR := norm_integral_phase_le ψ (M - (F₁ + F₂)) S
  have : IsFiniteMeasure (M - (F₁ + F₂)) := isFiniteMeasure_of_le M Measure.sub_le
  rw [hν']
  calc _ ≤ ‖∫ x in S, phaseFactor (ψ x) ∂(M - (F₁ + F₂))‖ +
        ‖(∫ x in S, phaseFactor (ψ x) ∂F₁) - phaseFactor Φ₁ * (Θ.real E : ℂ)‖ +
        ‖(∫ x in S, phaseFactor (ψ x) ∂F₂) - phaseFactor Φ₂ * (Θ.real E : ℂ)‖ :=
        (norm_add₃_le).trans_eq rfl
    _ ≤ _ := by linarith

/-- **Doeblin--Fourier cancellation (Lemma 3.7), domination form.**  The variation measure
of the phase projection of `M` is dominated by the first marginal of the remainder
`M - (F₁ + F₂)` plus `2ε Θ`. -/
theorem variation_le_remainder_add_of_cancellation {ψ : α × β → ℝ} (hψ : Measurable ψ)
    {M F₁ F₂ : Measure (α × β)} [IsFiniteMeasure M] [IsFiniteMeasure F₁]
    [IsFiniteMeasure F₂] (hF : F₁ + F₂ ≤ M) {Θ : Measure α}
    (hΘ₁ : F₁.map Prod.fst = Θ) (hΘ₂ : F₂.map Prod.fst = Θ) {Φ₁ Φ₂ ε : ℝ} (hε : 0 ≤ ε)
    (hΦ : phaseFactor Φ₁ + phaseFactor Φ₂ = 0)
    (hsupp₁ : ∀ᵐ x ∂F₁, |ψ x - Φ₁| ≤ ε) (hsupp₂ : ∀ᵐ x ∂F₂, |ψ x - Φ₂| ≤ ε)
    {ν : ComplexMeasure α} (hν : IsPhaseProjection ψ M ν) :
    ν.variation ≤ (M - (F₁ + F₂)).map Prod.fst + ENNReal.ofReal (2 * ε) • Θ := by
  have : IsFiniteMeasure (M - (F₁ + F₂)) := isFiniteMeasure_of_le M Measure.sub_le
  have : IsFiniteMeasure Θ := hΘ₁ ▸ inferInstance
  refine VectorMeasure.variation_le_of_forall_enorm_le fun E hE => ?_
  have h := norm_apply_le_cancellation hψ hF hΘ₁ hΘ₂ hΦ hsupp₁ hsupp₂ hν hE
  rw [← real_map_fst_apply_eq hE] at h
  rw [Measure.add_apply, Measure.smul_apply, smul_eq_mul, ← ofReal_norm]
  calc ENNReal.ofReal ‖ν E‖
      ≤ ENNReal.ofReal (((M - (F₁ + F₂)).map Prod.fst).real E +
        2 * ε * Θ.real E) := ENNReal.ofReal_le_ofReal h
    _ = _ := by
      rw [Measure.real, Measure.real,
        ENNReal.ofReal_add ENNReal.toReal_nonneg (by positivity),
        ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_toReal (measure_ne_top _ _), ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- **Doeblin--Fourier cancellation (Lemma 3.7)**, additive `ℝ≥0∞` form:
`‖ν‖_TV + 2 (1 - ε) Θ(α) ≤ M(α × β)`. -/
theorem totalVariation_add_le_of_cancellation {ψ : α × β → ℝ} (hψ : Measurable ψ)
    {M F₁ F₂ : Measure (α × β)} [IsFiniteMeasure M] [IsFiniteMeasure F₁]
    [IsFiniteMeasure F₂] (hF : F₁ + F₂ ≤ M) {Θ : Measure α}
    (hΘ₁ : F₁.map Prod.fst = Θ) (hΘ₂ : F₂.map Prod.fst = Θ) {Φ₁ Φ₂ ε : ℝ} (hε : 0 ≤ ε)
    (hε₁ : ε ≤ 1) (hΦ : phaseFactor Φ₁ + phaseFactor Φ₂ = 0)
    (hsupp₁ : ∀ᵐ x ∂F₁, |ψ x - Φ₁| ≤ ε) (hsupp₂ : ∀ᵐ x ∂F₂, |ψ x - Φ₂| ≤ ε)
    {ν : ComplexMeasure α} (hν : IsPhaseProjection ψ M ν) :
    ν.variation univ + ENNReal.ofReal (2 * (1 - ε)) * Θ univ ≤ M univ := by
  have h := variation_le_remainder_add_of_cancellation hψ hF hΘ₁ hΘ₂ hε hΦ hsupp₁ hsupp₂ hν
    univ
  rw [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ] at h
  have hM : M univ = (M - (F₁ + F₂)) univ + Θ univ + Θ univ := by
    have h := congrArg (fun m : Measure (α × β) => m univ) (Measure.sub_add_cancel_of_le hF)
    have hu : ∀ F : Measure (α × β), F.map Prod.fst = Θ → F univ = Θ univ := fun F hF' => by
      rw [← hF', Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ]
    simp only [Measure.add_apply] at h
    rw [← h, hu F₁ hΘ₁, hu F₂ hΘ₂, add_assoc]
  calc ν.variation univ + ENNReal.ofReal (2 * (1 - ε)) * Θ univ
      ≤ ((M - (F₁ + F₂)) univ + ENNReal.ofReal (2 * ε) * Θ univ) +
        ENNReal.ofReal (2 * (1 - ε)) * Θ univ := by gcongr
    _ = (M - (F₁ + F₂)) univ + (ENNReal.ofReal (2 * ε) + ENNReal.ofReal (2 * (1 - ε))) *
        Θ univ := by rw [add_assoc, add_mul]
    _ = (M - (F₁ + F₂)) univ + 2 * Θ univ := by
      rw [← ENNReal.ofReal_add (by positivity) (by linarith)]
      have : 2 * ε + 2 * (1 - ε) = 2 := by ring
      rw [this]
      simp
    _ = M univ := by rw [hM, two_mul, add_assoc]

/-- **Doeblin--Fourier cancellation (companion paper, Lemma 3.7).**  With the hypotheses of
Lemma Lemma 3.7 (the phase projection `ν` of `M` being the complex measure
`E ↦ ∫_{E × β} exp (-iψ) dM`):
`‖ν‖_TV ≤ M(α × β) - 2 (1 - ε) Θ(α)`. -/
theorem totalVariation_toReal_le_of_cancellation {ψ : α × β → ℝ} (hψ : Measurable ψ)
    {M F₁ F₂ : Measure (α × β)} [IsFiniteMeasure M] [IsFiniteMeasure F₁]
    [IsFiniteMeasure F₂] (hF : F₁ + F₂ ≤ M) {Θ : Measure α}
    (hΘ₁ : F₁.map Prod.fst = Θ) (hΘ₂ : F₂.map Prod.fst = Θ) {Φ₁ Φ₂ ε : ℝ} (hε : 0 ≤ ε)
    (hε₁ : ε < 1) (hΦ : phaseFactor Φ₁ + phaseFactor Φ₂ = 0)
    (hsupp₁ : ∀ᵐ x ∂F₁, |ψ x - Φ₁| ≤ ε) (hsupp₂ : ∀ᵐ x ∂F₂, |ψ x - Φ₂| ≤ ε)
    {ν : ComplexMeasure α} (hν : IsPhaseProjection ψ M ν) :
    (ν.variation univ).toReal ≤ M.real univ - 2 * (1 - ε) * Θ.real univ := by
  have : IsFiniteMeasure Θ := hΘ₁ ▸ inferInstance
  have h := totalVariation_add_le_of_cancellation hψ hF hΘ₁ hΘ₂ hε hε₁.le hΦ hsupp₁ hsupp₂ hν
  have hfin : ν.variation univ ≠ ∞ :=
    ne_top_of_le_ne_top (measure_ne_top M univ) (le_self_add.trans h)
  have h2 := ENNReal.toReal_mono (measure_ne_top M univ) h
  rw [ENNReal.toReal_add hfin (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)] at h2
  simp only [Measure.real] at h2 ⊢
  linarith

end HypoellipticAleksandrov.KineticAleksandrov.Decay
