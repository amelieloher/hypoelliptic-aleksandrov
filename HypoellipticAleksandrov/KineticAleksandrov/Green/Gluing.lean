module

public import HypoellipticAleksandrov.KineticAleksandrov.Green.SlabDensity

/-!
# Gluing the slab densities (Theorem 2.4)

If `Γ_μ^∞` has a Lebesgue density `G_T` on every slab `(T,2T) × ℝ^d × ℝ^d` (`T > 0`), then it
has one global density `G` on `(0,∞) × ℝ^d × ℝ^d`, and `G = G_T` almost everywhere on the slab
`T`.  The slabs `T ∈ ℚ_{>0}` cover the positive elapsed times, so `Γ ≪ Leb`, `Γ` is σ-finite,
and `G` is the Radon-Nikodym derivative; uniqueness of densities on the finite slab measures
identifies `G` with every `G_T`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Green

open MeasureTheory Set
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal NNReal

instance greenLebesgue_sigmaFinite (d : ℕ) : SigmaFinite (greenLebesgue d) := by
  unfold greenLebesgue; infer_instance

/-- Every point with positive time lies in a slab with rational parameter. -/
lemma exists_rat_slab {d : ℕ} (p : GreenCarrier d) :
    ∃ r : ℚ, 0 < (r : ℝ) ∧ p ∈ slabSet (d := d) (r : ℝ) := by
  have hp : 0 < p.1.1 := p.1.2.1
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show p.1.1 / 2 < p.1.1 by linarith)
  refine ⟨r, by linarith, ?_⟩
  simp only [slabSet, slabTimeSet, mem_preimage, mem_ofPred_eq]
  constructor <;> linarith

/-- Slabs with non-positive parameter are empty. -/
lemma slabSet_eq_empty {d : ℕ} {T : ℝ} (hT : T ≤ 0) : slabSet (d := d) T = ∅ := by
  ext p
  have := p.1.2.1
  simp only [slabSet, slabTimeSet, mem_preimage, mem_ofPred_eq, mem_empty_iff_false, iff_false]
  rintro ⟨h1, h2⟩
  linarith

/-- Slab gluing: local slab densities give one global density, equal to each of them a.e. -/
theorem exists_global_density {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}
    (K : MovingFiberKernel Ω γ) (σ₀ : ℝ) (μ : Measure (EvolutionState Ω γ σ₀))
    [IsFiniteMeasure μ] (Γ : Measure (GreenCarrier d)) (hΓ : IsGreenMeasure K σ₀ ⊤ μ Γ)
    (Gl : ℝ → GreenCarrier d → ℝ≥0∞)
    (hGm : ∀ T : ℝ, 0 < T → Measurable (Gl T))
    (hGl : ∀ T : ℝ, 0 < T →
      Γ.restrict (slabSet T) = ((greenLebesgue d).restrict (slabSet T)).withDensity (Gl T)) :
    ∃ G : GreenCarrier d → ℝ≥0∞, Measurable G ∧ Γ = (greenLebesgue d).withDensity G ∧
      ∀ T : ℝ, 0 < T → ∀ᵐ p ∂((greenLebesgue d).restrict (slabSet T)), G p = Gl T p := by
  have hMfin : μ univ < ⊤ := measure_lt_top μ _
  have hslab_fin : ∀ T : ℝ, 0 < T → Γ (slabSet T) < ⊤ := fun T hT =>
    (green_slab_le K σ₀ μ Γ hΓ hT).trans_lt (ENNReal.mul_lt_top hMfin ENNReal.ofReal_lt_top)
  have hsf : SigmaFinite Γ := by
    refine Measure.sigmaFinite_of_countable (S := Set.range fun r : ℚ => slabSet (d := d) (r : ℝ))
      (Set.countable_range _) ?_ ?_
    · rintro _ ⟨r, rfl⟩
      by_cases hr : 0 < (r : ℝ)
      · exact hslab_fin _ hr
      · show Γ (slabSet (d := d) (r : ℝ)) < ⊤
        rw [slabSet_eq_empty (not_lt.1 hr)]; simp
    · ext p
      simp only [mem_sUnion, mem_range, mem_univ, iff_true]
      obtain ⟨r, -, hr⟩ := exists_rat_slab p
      exact ⟨_, ⟨r, rfl⟩, hr⟩
  have hac : Γ ≪ greenLebesgue d := by
    intro A hA
    have hA' : MeasurableSet (toMeasurable (greenLebesgue d) A) := measurableSet_toMeasurable _ _
    have h0 : greenLebesgue d (toMeasurable (greenLebesgue d) A) = 0 := by
      rwa [measure_toMeasurable]
    refine measure_mono_null (subset_toMeasurable (greenLebesgue d) A) ?_
    set B := toMeasurable (greenLebesgue d) A
    have hcov : B ⊆ ⋃ r : ℚ, (B ∩ slabSet (d := d) (r : ℝ)) := by
      intro p hp
      obtain ⟨r, -, hr⟩ := exists_rat_slab p
      exact mem_iUnion.2 ⟨r, hp, hr⟩
    refine measure_mono_null hcov (measure_iUnion_null fun r => ?_)
    by_cases hr : 0 < (r : ℝ)
    · have h1 : (Γ.restrict (slabSet (r : ℝ))) B = 0 := by
        rw [hGl _ hr, withDensity_apply _ hA', Measure.restrict_restrict hA']
        have : (greenLebesgue d).restrict (B ∩ slabSet (r : ℝ)) = 0 :=
          Measure.restrict_eq_zero.2 (measure_mono_null inter_subset_left h0)
        rw [this]; simp
      rwa [Measure.restrict_apply hA'] at h1
    · rw [slabSet_eq_empty (not_lt.1 hr)]; simp
  refine ⟨(Γ.rnDeriv (greenLebesgue d)), Measure.measurable_rnDeriv _ _,
    (Measure.withDensity_rnDeriv_eq _ _ hac).symm, ?_⟩
  intro T hT
  have hmeas := measurableSet_slabSet (d := d) T
  have hrest : Γ.restrict (slabSet T) =
      ((greenLebesgue d).restrict (slabSet T)).withDensity (Γ.rnDeriv (greenLebesgue d)) := by
    conv_lhs => rw [← Measure.withDensity_rnDeriv_eq Γ (greenLebesgue d) hac]
    exact restrict_withDensity hmeas _
  have h1 := hrest.symm.trans (hGl T hT)
  have hfin : ∫⁻ p, Γ.rnDeriv (greenLebesgue d) p ∂((greenLebesgue d).restrict (slabSet T))
      ≠ ⊤ := by
    rw [← setLIntegral_univ, ← withDensity_apply _ MeasurableSet.univ, ← hrest,
      Measure.restrict_apply_univ]
    exact (hslab_fin T hT).ne
  exact (withDensity_eq_iff (Measure.measurable_rnDeriv _ _).aemeasurable
    (hGm T hT).aemeasurable hfin).1 h1

end HypoellipticAleksandrov.KineticAleksandrov.Green
