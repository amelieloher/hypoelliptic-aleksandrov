module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceWeakWeights

/-! # Integrability of compact weak-test weights -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set
open scoped ENNReal
variable {d : ℕ}

/-- A measurable function bounded on a compact test's support is integrable with that weight. -/
theorem integrable_compact_weight_bounded
    (Λ : ℝ × EvolutionAmbientState d → ℝ) (hΛ : Continuous Λ)
    (hc : HasCompactSupport Λ) (f : ℝ × EvolutionAmbientState d → ℝ)
    (hf : Measurable f) (C : ℝ) (_hC : 0 ≤ C)
    (hb : ∀ q, Λ q ≠ 0 → |f q| ≤ C) : Integrable (fun q => Λ q * f q) := by
  have hi : Integrable (fun q => C * ‖Λ q‖) :=
    (hΛ.integrable_of_hasCompactSupport hc).norm.const_mul C
  apply hi.mono' (hΛ.measurable.mul hf).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro q
  change ‖Λ q * f q‖ ≤ C * ‖Λ q‖
  rw [norm_mul, Real.norm_eq_abs (f q)]
  by_cases hq : Λ q = 0
  · simp only [hq, norm_zero, zero_mul, mul_zero, le_refl]
  · exact (mul_le_mul_of_nonneg_left (hb q hq) (norm_nonneg _)).trans_eq (mul_comm _ _)

/-- A bounded source's potential is integrable against any compact interior test weight. -/
theorem integrable_duhamelPotential_weight
    {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}
    (K : MovingFiberKernel Ω γ) (hΩ : MeasurableSet Ω) (hγ : Continuous γ)
    (Λ : ℝ × EvolutionAmbientState d → ℝ) (hΛ : Continuous Λ)
    (hc : HasCompactSupport Λ) (a T : ℝ) (haT : a < T)
    (hfloor : ∀ q, Λ q ≠ 0 → a ≤ q.1)
    (hU : tsupport Λ ⊆ boundedSourcePast Ω γ T)
    (g : KineticPoint d → ℝ) (hg : Measurable g)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ p, |g p| ≤ M) :
    Integrable (fun q => Λ q * duhamelPotential K T g ⟨q.1, q.2.1, q.2.2⟩) := by
  apply integrable_compact_weight_bounded Λ hΛ hc _
    ((measurable_duhamelPotential K hΩ hγ T g hg).comp
      (KineticPoint.measurable_equivProd_symm d)) ((T - a) * M)
    (mul_nonneg (sub_nonneg.mpr haT.le) hM)
  intro q hq
  have ht : q.1 < T := (hU (subset_tsupport Λ hq)).1
  exact (abs_duhamelPotential_le K g M hM hb ⟨q.1, q.2.1, q.2.2⟩ T ht.le).trans
    (mul_le_mul_of_nonneg_right (sub_le_sub_left (hfloor q hq) T) hM)

/-- Positive-part weights remain continuous with compact support. -/
theorem positive_weight_compact (Λ : ℝ × EvolutionAmbientState d → ℝ)
    (hΛ : Continuous Λ) (hc : HasCompactSupport Λ) :
    Continuous (fun q => max (Λ q) 0) ∧ HasCompactSupport (fun q => max (Λ q) 0) :=
  ⟨hΛ.max continuous_const, hc.comp_left (g := fun r : ℝ => max r 0) (max_self 0)⟩

/-- Positive-part weights have no larger closed support than their original test. -/
theorem tsupport_positive_weight_subset (Λ : ℝ × EvolutionAmbientState d → ℝ) :
    tsupport (fun q => max (Λ q) 0) ⊆ tsupport Λ := by
  apply closure_mono
  intro q hq
  by_contra h
  have hz : Λ q = 0 := by
    by_contra hne
    exact h hne
  exact hq (by simp only [hz, max_self])

/-- Positive and negative compact weights recover the signed weighted integral. -/
theorem integral_positive_negative_weight_sub
    (Λ : ℝ × EvolutionAmbientState d → ℝ) (hΛ : Continuous Λ)
    (hc : HasCompactSupport Λ) (f : ℝ × EvolutionAmbientState d → ℝ)
    (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ q, Λ q ≠ 0 → |f q| ≤ C) :
    (∫ q, max (Λ q) 0 * f q) - (∫ q, max (-Λ q) 0 * f q) = ∫ q, Λ q * f q := by
  obtain ⟨hpcont, hpcomp⟩ := positive_weight_compact Λ hΛ hc
  obtain ⟨hncont, hncomp⟩ := positive_weight_compact (fun q => -Λ q) hΛ.neg hc.neg
  have hp : Integrable (fun q => max (Λ q) 0 * f q) :=
    integrable_compact_weight_bounded _ hpcont hpcomp f hf C hC (fun q hq => by
      apply hb q
      intro hz
      exact hq (by simp only [hz, max_self]))
  have hn : Integrable (fun q => max (-Λ q) 0 * f q) :=
    integrable_compact_weight_bounded _ hncont hncomp f hf C hC (fun q hq => by
      apply hb q
      intro hz
      exact hq (by simp only [hz, neg_zero, max_self]))
  rw [← integral_sub hp hn]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro q
  change max (Λ q) 0 * f q - max (-Λ q) 0 * f q = Λ q * f q
  rw [← sub_mul, max_zero_sub_max_neg_zero_eq_self]

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
