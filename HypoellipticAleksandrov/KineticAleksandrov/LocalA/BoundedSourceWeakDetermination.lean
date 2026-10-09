module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceWeakIntegrability
import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.UniquenessMeasure
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! # Finite measures determined by the smooth Duhamel identity -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set
open scoped ENNReal
variable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}

/-- Positive test weights vanish outside every set containing their closed support. -/
theorem sourcePositiveMeasure_compl_eq_zero
    (Ψ : ℝ × EvolutionAmbientState d → ℝ) {U : Set (ℝ × EvolutionAmbientState d)}
    (hU : MeasurableSet U) (hs : tsupport Ψ ⊆ U) : sourcePositiveMeasure Ψ Uᶜ = 0 := by
  rw [sourcePositiveMeasure, withDensity_apply _ hU.compl]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem hU.compl] with q hq
  have hz : Ψ q = 0 := image_eq_zero_of_notMem_tsupport (fun h => hq (hs h))
  rw [hz, max_self, ENNReal.ofReal_zero]
  rfl

/-- Negating a compact weight preserves its closed support. -/
theorem tsupport_neg_weight (Ψ : ℝ × EvolutionAmbientState d → ℝ) :
    tsupport (fun q => -Ψ q) = tsupport Ψ := by
  apply congrArg closure
  ext q
  change (-Ψ q ≠ 0) ↔ (Ψ q ≠ 0)
  exact neg_ne_zero

/-- The two positive source measures in a signed weak identity. -/
def weakSourcePositiveMeasure (K : MovingFiberKernel Ω γ)
    (Λ Ψ : ℝ × EvolutionAmbientState d → ℝ) (a T : ℝ) :
    Measure (ℝ × EvolutionAmbientState d) :=
  boundedSourceActionMeasure K (sourcePositiveStartMeasure Λ) a T + sourcePositiveMeasure Ψ

/-- The negative source measure uses the negative weights, without source-value cutoffs. -/
def weakSourceNegativeMeasure (K : MovingFiberKernel Ω γ)
    (Λ Ψ : ℝ × EvolutionAmbientState d → ℝ) (a T : ℝ) :
    Measure (ℝ × EvolutionAmbientState d) :=
  weakSourcePositiveMeasure K (fun q => -Λ q) (fun q => -Ψ q) a T

/-- Smooth compact-source identities determine the corresponding finite source measures.
The consumer supplies this identity from the proved smooth Duhamel theorem. -/
theorem weakSourceMeasures_eq_of_smooth_identity
    (K : MovingFiberKernel Ω γ) (hΩ : IsOpen Ω) (hγ : Continuous γ)
    (Λ Ψ : ℝ × EvolutionAmbientState d → ℝ)
    (hΛ : Continuous Λ) (hΛc : HasCompactSupport Λ)
    (hΨ : Continuous Ψ) (hΨc : HasCompactSupport Ψ)
    (a T : ℝ) (haT : a < T) (hfloor : ∀ q, Λ q ≠ 0 → a ≤ q.1)
    (hΛU : tsupport Λ ⊆ boundedSourcePast Ω γ T)
    (hΨU : tsupport Ψ ⊆ boundedSourcePast Ω γ T)
    (hidentity : ∀ φ : ℝ × EvolutionAmbientState d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ boundedSourcePast Ω γ T → (∀ q, 0 ≤ φ q ∧ φ q ≤ 1) →
      (∫ q, Λ q * duhamelPotential K T (φ ∘ KineticPoint.equivProd d)
        ⟨q.1, q.2.1, q.2.2⟩) = -(∫ q, Ψ q * φ q)) :
    weakSourcePositiveMeasure K Λ Ψ a T = weakSourceNegativeMeasure K Λ Ψ a T := by
  have hΛstart := sourcePositiveStartMeasure_isFinite Λ hΛ hΛc
  have hΛnstart := sourcePositiveStartMeasure_isFinite (fun q => -Λ q) hΛ.neg hΛc.neg
  have hΨfin := sourcePositiveMeasure_isFinite Ψ hΨ hΨc
  have hΨnfin := sourcePositiveMeasure_isFinite (fun q => -Ψ q) hΨ.neg hΨc.neg
  let μ := boundedSourceActionMeasure K (sourcePositiveStartMeasure Λ) a T
  let μn := boundedSourceActionMeasure K (sourcePositiveStartMeasure (fun q => -Λ q)) a T
  have hfin : IsFiniteMeasure μ := by dsimp only [μ]; infer_instance
  have hnfin : IsFiniteMeasure μn := by dsimp only [μn]; infer_instance
  change μ + sourcePositiveMeasure Ψ = μn + sourcePositiveMeasure (fun q => -Ψ q)
  have hU := measurableSet_boundedSourcePast hΩ.measurableSet hγ T
  apply measure_eq_of_smooth_integral_eq (isOpen_boundedSourcePast hΩ hγ T)
  · rw [Measure.add_apply, boundedSourceActionMeasure_compl_past K hΩ.measurableSet hγ,
      sourcePositiveMeasure_compl_eq_zero Ψ hU hΨU, add_zero]
  · rw [Measure.add_apply, boundedSourceActionMeasure_compl_past K hΩ.measurableSet hγ,
      sourcePositiveMeasure_compl_eq_zero (fun q => -Ψ q) hU
        (by rw [tsupport_neg_weight]; exact hΨU), add_zero]
  intro φ hφ hφc hφU hφr
  have hφb : ∀ q, |φ q| ≤ 1 := fun q => by
    rw [abs_of_nonneg (hφr q).1]
    exact (hφr q).2
  have hφm := hφ.continuous.measurable
  have hφμ := integrable_bounded_real μ φ hφm 1 hφb
  have hφμn := integrable_bounded_real μn φ hφm 1 hφb
  have hφΨ := integrable_bounded_real (sourcePositiveMeasure Ψ) φ hφm 1 hφb
  have hφΨn := integrable_bounded_real (sourcePositiveMeasure (fun q => -Ψ q)) φ hφm 1 hφb
  rw [integral_add_measure hφμ hφΨ, integral_add_measure hφμn hφΨn]
  let g := φ ∘ KineticPoint.equivProd d
  have hgm : Measurable g := hφm.comp (KineticPoint.measurable_equivProd d)
  have hgb : ∀ p, |g p| ≤ 1 := fun p => hφb _
  have hfloorN : ∀ q, -Λ q ≠ 0 → a ≤ q.1 := fun q hq => hfloor q (neg_ne_zero.mp hq)
  have hact := integral_boundedSourceAction_positive_potential K hΩ.measurableSet hγ
    Λ hΛ hΛc a T hfloor g hgm 1 zero_le_one hgb
  have hactn := integral_boundedSourceAction_positive_potential K hΩ.measurableSet hγ
    (fun q => -Λ q) hΛ.neg hΛc.neg a T hfloorN g hgm 1 zero_le_one hgb
  have hbase := integral_sourcePositiveMeasure Ψ hΨ.measurable φ
  have hbasen := integral_sourcePositiveMeasure (fun q => -Ψ q) hΨ.neg.measurable φ
  have hWm : Measurable (fun q : ℝ × EvolutionAmbientState d =>
      duhamelPotential K T g ⟨q.1, q.2.1, q.2.2⟩) :=
    (measurable_duhamelPotential K hΩ.measurableSet hγ T g hgm).comp
      (KineticPoint.measurable_equivProd_symm d)
  have hWb : ∀ q, Λ q ≠ 0 →
      |duhamelPotential K T g ⟨q.1, q.2.1, q.2.2⟩| ≤ T - a := by
    intro q hq
    have ht := (hΛU (subset_tsupport Λ hq)).1
    have hbnd := abs_duhamelPotential_le K g 1 zero_le_one hgb
      ⟨q.1, q.2.1, q.2.2⟩ T ht.le
    have hpoint : |duhamelPotential K T g ⟨q.1, q.2.1, q.2.2⟩| ≤ T - q.1 := by
      simpa only [mul_one] using hbnd
    exact hpoint.trans (sub_le_sub_left (hfloor q hq) T)
  have hsub := integral_positive_negative_weight_sub Λ hΛ hΛc _ hWm
    (T - a) (sub_nonneg.mpr haT.le) hWb
  have hsubbase := integral_positive_negative_weight_sub Ψ hΨ hΨc φ hφm
    1 zero_le_one (fun q _ => hφb q)
  have hid := hidentity φ hφ hφc hφU hφr
  change (∫ q, φ q ∂μ) = _ at hact
  change (∫ q, φ q ∂μn) = _ at hactn
  rw [hact, hactn, hbase, hbasen]
  linarith only [hsub, hsubbase, hid]

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
