module

public import HypoellipticAleksandrov.KineticAleksandrov.Green.SlabFourierGreen

/-!
# The `(τ, w)`-marginal on the slab (first sentence of Lemma 5.1, (5.1))

From the Proposition 4.2 conclusion (premise `ParabolicOccupationConclusion`) with `ρ` the velocity
marginal of `μ` and `S = 2T`: the `(τ,w)`-marginal of `Γ` on `T < τ < 2T` has a density with
`L^γ` norm at most `C_γ 2^{β_γ} M T^{β_γ}`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Green

open MeasureTheory Set
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal NNReal ProbabilityTheory

/-- `L^γ` norms of a time-shifted occupation density on the slab. -/
lemma eLpNorm_slabShift_le {d : ℕ} (g : ℝ × PDE.Vec d → ℝ) (hgm : Measurable g)
    (hgn : ∀ q, 0 ≤ g q) (s T S γ Cn : ℝ) (hT : 0 ≤ T) (hs : 0 ≤ T - s) (hTS : 2 * T - s ≤ S)
    (hbound : eLpNorm g (ENNReal.ofReal γ)
      (volume.restrict (Ioo (0 : ℝ) S ×ˢ (univ : Set (PDE.Vec d)))) ≤ ENNReal.ofReal Cn) :
    eLpNorm (fun y => ENNReal.ofReal (g (slabShift d s y))) (ENNReal.ofReal γ) (slabBase d T) ≤
      ENNReal.ofReal Cn := by
  have hemb := measurableEmbedding_slabShift d s
  have h1 : eLpNorm (fun y => ENNReal.ofReal (g (slabShift d s y))) (ENNReal.ofReal γ)
      (slabBase d T) = eLpNorm g (ENNReal.ofReal γ) ((slabBase d T).map (slabShift d s)) := by
    rw [hemb.eLpNorm_map_measure]
    have hm1 : Measurable (fun y => ENNReal.ofReal (g (slabShift d s y))) :=
      ENNReal.measurable_ofReal.comp (hgm.comp hemb.measurable)
    refine eLpNorm_congr_enorm_ae hm1.aestronglyMeasurable
      (hgm.comp hemb.measurable).aestronglyMeasurable (Filter.Eventually.of_forall (fun y => ?_))
    rw [Function.comp_apply, enorm_eq_self, Real.enorm_of_nonneg (hgn _)]
  rw [h1, map_slabBase_slabShift d T s hT]
  refine le_trans (eLpNorm_mono_measure _ (Measure.restrict_mono ?_ le_rfl)) hbound
  intro q hq
  simp only [mem_prod, mem_Ioo, mem_univ, and_true] at hq ⊢
  constructor <;> linarith [hq.1, hq.2]


/-- The occupation-kernel integral over the slab sections of `E`, as a function of `v`. -/
lemma measurable_slab_occupation {d : ℕ}
    (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d))) (σ₁ s T : ℝ)
    {E : Set (SlabBase d)} (hE : MeasurableSet E) :
    Measurable (fun v : PDE.Vec d => ∫⁻ τ in slabTimeSet T,
      occupationKernel K σ₁ (τ.1 - s) v {w | (τ, w) ∈ E} ∂elapsedVolume ⊤) := by
  have hE' : MeasurableSet {z : (PDE.Vec d × ElapsedTime ⊤) × PDE.Vec d | (z.1.2, z.2) ∈ E} :=
    hE.preimage (by fun_prop)
  have hm := measurable_occupationKernel_sectionGen K σ₁
    (f := fun x : PDE.Vec d × ElapsedTime ⊤ => x.2.1 - s) (u := fun x => x.1)
    (by fun_prop) (by fun_prop) hE'
  exact hm.lintegral_prod_right'

/-- Slab mass of the Green measure in terms of the occupation kernel of the velocity marginal. -/
theorem green_slab_marginal_eq {d : ℕ}
    (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
    (hcov : IsTranslationCovariantEvolution (wholeSpace d) (fun _ => 0) MeasurableSet.univ K)
    (σ₀ : ℝ) (μ : Measure (EvolutionState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) σ₀))
    [IsFiniteMeasure μ] (Γ : Measure (GreenCarrier d)) (hΓ : IsGreenMeasure K σ₀ ⊤ μ Γ)
    (T : ℝ) {E : Set (SlabBase d)} (hE : MeasurableSet E) :
    Γ {p | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T} =
      ∫⁻ v, (∫⁻ τ in slabTimeSet T, occupationKernel K σ₀ τ.1 v {w | (τ, w) ∈ E}
        ∂elapsedVolume ⊤) ∂μ.map (fun p => p.1.1) := by
  have hSE : {p : GreenCarrier d | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T} =
      (fun p : GreenCarrier d => (p.1, p.2.1)) ⁻¹' E ∩ slabSet T := by
    ext p; simp [slabSet, slabTimeSet]
  have hSEm : MeasurableSet
      {p : GreenCarrier d | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T} := by
    rw [hSE]
    exact (hE.preimage (by fun_prop)).inter (measurableSet_slabSet T)
  have hmapm : Measurable (fun p : EvolutionState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) σ₀ =>
      p.1.1) := measurable_fst.comp measurable_subtype_coe
  rw [← lintegral_indicator_one hSEm, hΓ _ (measurable_one.indicator hSEm),
    lintegral_map (measurable_slab_occupation K σ₀ 0 T hE |> fun h => by simpa using h) hmapm]
  refine lintegral_congr (fun p => ?_)
  rw [← lintegral_indicator (measurableSet_slabTimeSet T)]
  refine lintegral_congr (fun τ => ?_)
  by_cases hτ : τ ∈ slabTimeSet T
  · rw [indicator_of_mem hτ]
    have hsec : MeasurableSet {w' : PDE.Vec d | (τ, w') ∈ E} := measurable_prodMk_left hE
    have hfun : (fun w : EvolutionAmbientState d =>
        {p : GreenCarrier d | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T}.indicator
          (1 : GreenCarrier d → ℝ≥0∞) (τ, w)) =
        {w : EvolutionAmbientState d | w.1 ∈ {w' : PDE.Vec d | (τ, w') ∈ E}}.indicator
          (1 : EvolutionAmbientState d → ℝ≥0∞) := by
      funext w
      by_cases h : (τ, w.1) ∈ E
      · have h1 : (τ, w) ∈ {p : GreenCarrier d | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T} :=
          ⟨h, hτ.1, hτ.2⟩
        have h2 : w ∈ {w : EvolutionAmbientState d | w.1 ∈ {w' : PDE.Vec d | (τ, w') ∈ E}} := h
        rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2]
        rfl
      · have h1 : (τ, w) ∉ {p : GreenCarrier d | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T} :=
          fun h' => h h'.1
        have h2 : w ∉ {w : EvolutionAmbientState d | w.1 ∈ {w' : PDE.Vec d | (τ, w') ∈ E}} := h
        rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
    have hli := lintegral_indicator_one (μ := K.master (elapsedQuery σ₀ p τ))
      (s := {w : EvolutionAmbientState d | w.1 ∈ {w' : PDE.Vec d | (τ, w') ∈ E}})
      (measurable_fst hsec)
    rw [hfun, hli, ← K.firstMarginal_apply _ {w' : PDE.Vec d | (τ, w') ∈ E} hsec]
    have hq : elapsedQuery σ₀ p τ =
        wholeSpaceQuery σ₀ (σ₀ + τ.1) (le_add_of_nonneg_right τ.2.1.le) p.1.1 p.1.2 := rfl
    rw [hq, firstMarginal_startingPosition K hcov, occupationKernel_of_nonneg K σ₀ τ.1 τ.2.1.le]
  · rw [indicator_of_notMem hτ]
    have hz : ∀ w : EvolutionAmbientState d,
        {p : GreenCarrier d | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T}.indicator
          (1 : GreenCarrier d → ℝ≥0∞) (τ, w) = 0 :=
      fun w => Set.indicator_of_notMem (fun h => hτ ⟨h.2.1, h.2.2⟩) _
    exact (lintegral_congr hz).trans lintegral_zero


lemma one_le_slabGamma0 {d : ℕ} (hd : 0 < d) : 1 ≤ slabGamma0 d := by
  unfold slabGamma0
  have : (0 : ℝ) < d := by exact_mod_cast hd
  rw [le_div_iff₀ this]
  linarith

/-- The `ofReal` arithmetic of the marginal bound. -/
lemma ofReal_marginal_bound (C a M b : ℝ) (hC : 0 ≤ C) (hM : 0 ≤ M) (T : ℝ) (hT : 0 ≤ T)
    (β : ℝ) (hb : b = (2 * T) ^ β) (ha : a = (2 : ℝ) ^ β) :
    ENNReal.ofReal (C * M * b) =
      ENNReal.ofReal (C * a) * ENNReal.ofReal M * ENNReal.ofReal (T ^ β) := by
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  rw [hb, ha, Real.mul_rpow h2 hT, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul
    (by positivity)]
  congr 1
  ring

/-- **Lemma 5.1, first sentence ((5.1)).**  The `(τ,w)`-marginal of the Green
measure on `T < τ < 2T` has a density with `‖g‖_{L^γ} ≤ C_γ 2^{β_γ} M T^{β_γ}`. -/
theorem slab_marginal_density {d : ℕ} (hd : 0 < d)
    (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
    (hcov : IsTranslationCovariantEvolution (wholeSpace d) (fun _ => 0) MeasurableSet.univ K)
    (C : ℝ → ℝ) (hocc : OccupationBoundedBy K C)
    (σ₀ : ℝ) (μ : Measure (EvolutionState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) σ₀))
    [IsFiniteMeasure μ] (Γ : Measure (GreenCarrier d)) (hΓ : IsGreenMeasure K σ₀ ⊤ μ Γ)
    {T : ℝ} (hT : 0 < T) :
    ∃ g : SlabBase d → ℝ≥0∞, Measurable g ∧
      (∀ E : Set (SlabBase d), MeasurableSet E →
        Γ {p | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T} = ∫⁻ y in E, g y ∂slabBase d T) ∧
      ∀ γ : ℝ, 1 ≤ γ → γ ≤ slabGamma0 d →
        eLpNorm g (ENNReal.ofReal γ) (slabBase d T) ≤
          ENNReal.ofReal (C γ * (2 : ℝ) ^ slabBeta d γ) * μ univ *
            ENNReal.ofReal (T ^ slabBeta d γ) := by
  have hmapm : Measurable (fun p : EvolutionState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) σ₀ =>
      p.1.1) := measurable_fst.comp measurable_subtype_coe
  have : IsFiniteMeasure (μ.map (fun p : EvolutionState (wholeSpace d)
      (fun _ => (0 : PDE.Vec d)) σ₀ => p.1.1)) := Measure.isFiniteMeasure_map _ _
  obtain ⟨g, hg, hnorm⟩ := hocc.2 (μ.map (fun p => p.1.1)) σ₀ (2 * T) (by linarith)
  have hint : Integrable g (volume.restrict (Ioo (0 : ℝ) (2 * T) ×ˢ (univ : Set (PDE.Vec d)))) := by
    have := (hnorm 1 le_rfl (one_le_slabGamma0 hd)).1
    rw [ENNReal.ofReal_one] at this
    exact memLp_one_iff_integrable.1 this
  refine ⟨fun y => ENNReal.ofReal (g (slabShift d 0 y)), ?_, ?_, ?_⟩
  · exact ENNReal.measurable_ofReal.comp (hg.1.comp (measurable_slabShift d 0))
  · intro E hE
    rw [green_slab_marginal_eq K hcov σ₀ μ Γ hΓ T hE]
    have := slab_occupation_identity K σ₀ 0 T (2 * T) hT.le hT (by linarith) (by linarith)
      (μ.map (fun p => p.1.1)) g hg hint hE
    simp only [sub_zero] at this
    exact this.symm
  · intro γ hγ1 hγ2
    obtain ⟨hmem, hbd⟩ := hnorm γ hγ1 hγ2
    have hCn : 0 ≤ C γ := hocc.1 γ hγ1 hγ2
    set Cn : ℝ := C γ * ((μ.map (fun p => p.1.1)) univ).toReal * (2 * T) ^ slabBeta d γ with hCn_def
    have hbd' : eLpNorm g (ENNReal.ofReal γ)
        (volume.restrict (Ioo (0 : ℝ) (2 * T) ×ˢ (univ : Set (PDE.Vec d)))) ≤
          ENNReal.ofReal Cn := by
      rw [← ENNReal.ofReal_toReal hmem.eLpNorm_ne_top]
      exact ENNReal.ofReal_le_ofReal hbd
    have := eLpNorm_slabShift_le g hg.1 hg.2.1 0 T (2 * T) γ Cn hT.le (by linarith)
      (by linarith) hbd'
    refine this.trans (le_of_eq ?_)
    rw [hCn_def, Measure.map_apply hmapm MeasurableSet.univ, preimage_univ]
    rw [ofReal_marginal_bound (C γ) ((2 : ℝ) ^ slabBeta d γ) ((μ univ).toReal)
      ((2 * T) ^ slabBeta d γ) hCn ENNReal.toReal_nonneg T hT.le (slabBeta d γ) rfl rfl,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]

end HypoellipticAleksandrov.KineticAleksandrov.Green
