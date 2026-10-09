module

public import HypoellipticAleksandrov.KineticAleksandrov.Green.SlabFourierMarginal
public import HypoellipticAleksandrov.KineticAleksandrov.Green.SlabFourierEvolved

/-!
# Lemma 5.1: domination of the Fourier marginal

Half-time evolution `η_T^ξ` of `μ` (velocity Fourier measure at time `σ₀ + T/2`) and the domination
`|∫_{T<τ<2T} e^{-iξ·z} Φ(τ,w) dΓ| ≤ ∫_T^{2T} ∫ |Φ| g(τ - T/2, w)`, where `g` is the occupation
density of `|η_T^ξ|`.  Only composition and translation covariance of the kernel and the total
variation domination are used.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Green

open MeasureTheory Set
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal NNReal ProbabilityTheory

variable {d : ℕ} (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d)))

/-- Initial phase `e^{-iξ·z₁}` at the half time. -/
def halfPhase (d : ℕ) (ξ : PDE.Vec d) (r : ℝ) :
    EvolutionState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) r → ℂ :=
  fun w => fourierPhase ξ 0 w.1

/-- Velocity coordinate of a half-time state. -/
def halfVelocity (d : ℕ) (r : ℝ) :
    EvolutionState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) r → PDE.Vec d := fun w => w.1.1

lemma measurable_halfPhase (ξ : PDE.Vec d) (r : ℝ) : Measurable (halfPhase d ξ r) :=
  (continuous_fourierPhase ξ 0).measurable.comp measurable_subtype_coe

lemma norm_halfPhase (ξ : PDE.Vec d) (r : ℝ) (w) : ‖halfPhase d ξ r w‖ = 1 :=
  norm_fourierPhase ξ 0 w.1

lemma measurable_halfVelocity (r : ℝ) : Measurable (halfVelocity d r) :=
  measurable_fst.comp measurable_subtype_coe

/-- The half-time fibre kernel. -/
def halfKernel (σ₀ r : ℝ) (hσr : σ₀ ≤ r) :
    ProbabilityTheory.Kernel (EvolutionState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) σ₀)
      (EvolutionState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) r) :=
  K.fiberKernel MeasurableSet.univ σ₀ r hσr

instance halfKernel_isFiniteKernel (σ₀ r : ℝ) (hσr : σ₀ ≤ r) :
    ProbabilityTheory.IsFiniteKernel (halfKernel K σ₀ r hσr) :=
  fiberKernel_isFiniteKernel K MeasurableSet.univ σ₀ r hσr


/-- Queries at equal times coincide. -/
lemma wholeSpaceQuery_congr (σ a b : ℝ) (h₁ : σ ≤ a) (h₂ : σ ≤ b) (hab : a = b)
    (v z : PDE.Vec d) : wholeSpaceQuery σ a h₁ v z = wholeSpaceQuery σ b h₂ v z := by
  subst hab; rfl

/-- The displacement phase integrated over a `v`-slab: `e^{-iξ·z}` times the Fourier kernel. -/
lemma master_phase_integral
    (hcov : IsTranslationCovariantEvolution (wholeSpace d) (fun _ => 0) MeasurableSet.univ K)
    (σ τ : ℝ) (hστ : σ ≤ τ) (ξ v z : PDE.Vec d) {E : Set (PDE.Vec d)} (hE : MeasurableSet E) :
    ∫ w, (E ×ˢ (univ : Set (PDE.Vec d))).indicator (fourierPhase ξ 0) w
        ∂K.master (wholeSpaceQuery σ τ hστ v z) =
      fourierPhase ξ 0 (v, z) * fourierKernel K σ τ hστ ξ v E := by
  rw [← fourierKernel_eq_startingPosition K hcov σ τ hστ ξ v z,
    fourierProjection_spec K (wholeSpaceQuery σ τ hστ v z) ξ E hE, ← integral_const_mul,
    ← integral_indicator (hE.prod MeasurableSet.univ)]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
  by_cases hw : w ∈ E ×ˢ (univ : Set (PDE.Vec d))
  · simp only [Set.indicator_of_mem hw]
    exact fourierPhase_factor ξ 0 (v, z) w
  · simp only [Set.indicator_of_notMem hw]

/-- The fibre measure of the half-time evolution is the Fourier kernel times a unimodular phase. -/
lemma fibreMeasure_halfKernel
    (hcov : IsTranslationCovariantEvolution (wholeSpace d) (fun _ => 0) MeasurableSet.univ K)
    (σ₀ r : ℝ) (hσr : σ₀ ≤ r) (ξ : PDE.Vec d)
    (x : EvolutionState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) σ₀)
    {E : Set (PDE.Vec d)} (hE : MeasurableSet E) :
    fibreMeasure (halfKernel K σ₀ r hσr) (halfPhase d ξ r) (halfVelocity d r) x E =
      fourierPhase ξ 0 x.1 * fourierKernel K σ₀ r hσr ξ x.1.1 E := by
  rw [fibreMeasure_apply _ _ _ (measurable_halfPhase ξ r) (norm_halfPhase ξ r)
    (measurable_halfVelocity r) x hE]
  let G : EvolutionAmbientState d → ℂ := (E ×ˢ univ).indicator (fourierPhase ξ 0)
  have hG : Measurable G := (continuous_fourierPhase ξ 0).measurable.indicator
    (hE.prod MeasurableSet.univ)
  have h1 : ∀ y : EvolutionState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) r,
      (halfVelocity d r ⁻¹' E).indicator (halfPhase d ξ r) y = G y.1 := by
    intro y
    by_cases hy : y.1.1 ∈ E
    · have h2 : y ∈ halfVelocity d r ⁻¹' E := hy
      have h3 : y.1 ∈ E ×ˢ (univ : Set (PDE.Vec d)) := ⟨hy, mem_univ _⟩
      rw [Set.indicator_of_mem h2]
      simp only [G, Set.indicator_of_mem h3]
      rfl
    · have h2 : y ∉ halfVelocity d r ⁻¹' E := hy
      have h3 : y.1 ∉ E ×ˢ (univ : Set (PDE.Vec d)) := fun h => hy h.1
      rw [Set.indicator_of_notMem h2]
      simp only [G, Set.indicator_of_notMem h3]
  simp_rw [h1]
  have h4 : ∫ y, G y.1 ∂(halfKernel K σ₀ r hσr) x =
      ∫ w, G w ∂K.master (evolutionQueryOfState (wholeSpace d) (fun _ => 0) σ₀ r hσr x) := by
    rw [← K.map_fiberKernel_eq_master MeasurableSet.univ σ₀ r hσr x,
      integral_map measurable_subtype_coe.aemeasurable hG.aestronglyMeasurable]
    rfl
  rw [h4]
  exact master_phase_integral K hcov σ₀ r hσr ξ x.1.1 x.1.2 hE


/-- Each fibre of the half-time evolution has the total variation of the Fourier kernel. -/
lemma fibreMeasure_variation_le
    (hcov : IsTranslationCovariantEvolution (wholeSpace d) (fun _ => 0) MeasurableSet.univ K)
    (σ₀ r : ℝ) (hσr : σ₀ ≤ r) (ξ : PDE.Vec d)
    (x : EvolutionState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) σ₀) :
    (fibreMeasure (halfKernel K σ₀ r hσr) (halfPhase d ξ r) (halfVelocity d r) x).variation univ ≤
      totalVariationNorm (fourierKernel K σ₀ r hσr ξ x.1.1) := by
  have hle : (fibreMeasure (halfKernel K σ₀ r hσr) (halfPhase d ξ r)
      (halfVelocity d r) x).variation ≤ (fourierKernel K σ₀ r hσr ξ x.1.1).variation := by
    refine VectorMeasure.variation_le_of_forall_enorm_le (fun E hE => ?_)
    have h1 : ‖fourierPhase ξ 0 x.1‖ₑ = 1 := by
      rw [← ofReal_norm, norm_fourierPhase]; simp
    rw [fibreMeasure_halfKernel K hcov σ₀ r hσr ξ x hE, enorm_mul, h1, one_mul]
    exact VectorMeasure.enorm_measure_le_variation _ E
  exact Measure.le_iff.1 hle univ MeasurableSet.univ


/-- The phase `e^{-iξ·z'}` cut to the velocity set `E`. -/
def phaseSection (d : ℕ) (ξ : PDE.Vec d) (E : Set (PDE.Vec d)) : EvolutionAmbientState d → ℂ :=
  (E ×ˢ (univ : Set (PDE.Vec d))).indicator (fourierPhase ξ 0)

lemma measurable_phaseSection (ξ : PDE.Vec d) {E : Set (PDE.Vec d)} (hE : MeasurableSet E) :
    Measurable (phaseSection d ξ E) :=
  (continuous_fourierPhase ξ 0).measurable.indicator (hE.prod MeasurableSet.univ)

lemma norm_phaseSection_le (ξ : PDE.Vec d) (E : Set (PDE.Vec d)) (w : EvolutionAmbientState d) :
    ‖phaseSection d ξ E w‖ ≤ 1 := by
  unfold phaseSection
  by_cases hw : w ∈ E ×ˢ (univ : Set (PDE.Vec d))
  · rw [Set.indicator_of_mem hw, norm_fourierPhase]
  · rw [Set.indicator_of_notMem hw, norm_zero]; exact zero_le_one

/-- **Composition and covariance at the half time.** -/
theorem slab_pairing
    (hcov : IsTranslationCovariantEvolution (wholeSpace d) (fun _ => 0) MeasurableSet.univ K)
    (hcomp : K.HasComposition MeasurableSet.univ) (σ₀ : ℝ)
    (μ : Measure (EvolutionState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) σ₀))
    [IsFiniteMeasure μ] (r : ℝ) (hσr : σ₀ ≤ r) (ξ : PDE.Vec d) (τ : ElapsedTime ⊤)
    (hrτ : r ≤ σ₀ + τ.1) {E : Set (PDE.Vec d)} (hE : MeasurableSet E) :
    ∫ p, ∫ w, phaseSection d ξ E w ∂K.master (elapsedQuery σ₀ p τ) ∂μ =
      ∫ x, ∫ y, fourierKernel K r (σ₀ + τ.1) hrτ ξ (halfVelocity d r y) E * halfPhase d ξ r y
        ∂halfKernel K σ₀ r hσr x ∂μ := by
  refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
  dsimp only
  have hq : elapsedQuery σ₀ p τ = evolutionQueryOfState (wholeSpace d) (fun _ => 0) σ₀ (σ₀ + τ.1)
      (le_add_of_nonneg_right τ.2.1.le) p := rfl
  rw [hq, master_integral_composition K MeasurableSet.univ hcomp σ₀ r (σ₀ + τ.1) hσr hrτ p
    (phaseSection d ξ E) (measurable_phaseSection ξ hE) ⟨1, norm_phaseSection_le ξ E⟩]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
  dsimp only
  have hq' : evolutionQueryOfState (wholeSpace d) (fun _ => 0) r (σ₀ + τ.1) hrτ y =
      wholeSpaceQuery r (σ₀ + τ.1) hrτ y.1.1 y.1.2 := rfl
  rw [hq']
  have := master_phase_integral K hcov r (σ₀ + τ.1) hrτ ξ y.1.1 y.1.2 hE
  rw [mul_comm]
  exact this


/-- The half time `σ₀ + T/2`. -/
lemma le_halfTime (σ₀ T : ℝ) (hT : 0 ≤ T) : σ₀ ≤ σ₀ + T / 2 :=
  le_add_of_nonneg_right (by positivity)

/-- The complex velocity measure `η_T^ξ` of the half-time evolution of `μ`. -/
def halfMeasure (σ₀ T : ℝ) (hT : 0 ≤ T)
    (μ : Measure (EvolutionState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) σ₀)) (ξ : PDE.Vec d) :
    VectorMeasure (PDE.Vec d) ℂ :=
  evolvedMeasure μ (halfKernel K σ₀ (σ₀ + T / 2) (le_halfTime σ₀ T hT))
    (halfPhase d ξ (σ₀ + T / 2)) (halfVelocity d (σ₀ + T / 2))

/-- At a time `τ` in the slab, `occupationKernel` from the half time is the velocity marginal. -/
lemma occupationKernel_half (σ₀ T : ℝ) (τ : ℝ) (hτ : T < τ) (hT : 0 < T) (v : PDE.Vec d) :
    occupationKernel K (σ₀ + T / 2) (τ - T / 2) v =
      K.firstMarginal (wholeSpaceQuery (σ₀ + T / 2) (σ₀ + τ)
        (by linarith) v 0) := by
  rw [occupationKernel_of_nonneg K _ _ (by linarith) v]
  rw [wholeSpaceQuery_congr (σ₀ + T / 2) _ (σ₀ + τ) _ (by linarith) (by ring) v 0]

/-- **Per-section bound.**  For `τ` in the slab, the section integral is dominated by the occupation
of `|η_T^ξ|`. -/
theorem slab_section_bound
    (hcov : IsTranslationCovariantEvolution (wholeSpace d) (fun _ => 0) MeasurableSet.univ K)
    (hcomp : K.HasComposition MeasurableSet.univ) (σ₀ : ℝ)
    (μ : Measure (EvolutionState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) σ₀))
    [IsFiniteMeasure μ] {T : ℝ} (hT : 0 < T) (ξ : PDE.Vec d) (τ : ElapsedTime ⊤)
    (hτ : T < τ.1) {E : Set (PDE.Vec d)} (hE : MeasurableSet E) :
    ‖∫ p, ∫ w, phaseSection d ξ E w ∂K.master (elapsedQuery σ₀ p τ) ∂μ‖ₑ ≤
      ∫⁻ v, occupationKernel K (σ₀ + T / 2) (τ.1 - T / 2) v E
        ∂(halfMeasure K σ₀ T hT.le μ ξ).variation := by
  have hrτ : σ₀ + T / 2 ≤ σ₀ + τ.1 := by linarith
  rw [slab_pairing K hcov hcomp σ₀ μ (σ₀ + T / 2) (le_halfTime σ₀ T hT.le) ξ τ hrτ hE]
  have hb : ∃ C : ℝ, ∀ v : PDE.Vec d,
      ‖fourierKernel K (σ₀ + T / 2) (σ₀ + τ.1) hrτ ξ v E‖ ≤ C :=
    ⟨1, fun v => fourierKernel_apply_norm_le_one K _ _ hrτ ξ v E⟩
  refine (evolved_integral_enorm_le μ (halfKernel K σ₀ (σ₀ + T / 2) (le_halfTime σ₀ T hT.le))
    (halfPhase d ξ (σ₀ + T / 2)) (halfVelocity d (σ₀ + T / 2)) (measurable_halfPhase ξ _)
    (norm_halfPhase ξ _) (measurable_halfVelocity _)
    (fun v => fourierKernel K (σ₀ + T / 2) (σ₀ + τ.1) hrτ ξ v E)
    (measurable_fourierKernel_apply K _ _ hrτ ξ E hE) hb).trans ?_
  refine lintegral_mono (fun v => ?_)
  rw [occupationKernel_half K σ₀ T τ.1 hτ hT v]
  refine (VectorMeasure.enorm_measure_le_variation _ E).trans ?_
  exact Measure.le_iff.1 (fourierKernel_variation_le K _ _ hrτ ξ v) E hE


/-- The Fourier phase on the Green carrier. -/
def greenPhase (d : ℕ) (ξ : PDE.Vec d) (p : GreenCarrier d) : ℂ :=
  Complex.exp (-((PDE.vecDot ξ p.2.2 : ℝ) * Complex.I))

lemma greenPhase_eq (ξ : PDE.Vec d) (τ : ElapsedTime ⊤) (w : EvolutionAmbientState d) :
    greenPhase d ξ (τ, w) = fourierPhase ξ 0 w := by
  unfold greenPhase fourierPhase
  rw [sub_zero, neg_mul, mul_comm]

lemma measurable_greenPhase (ξ : PDE.Vec d) : Measurable (greenPhase d ξ) := by
  unfold greenPhase PDE.vecDot
  fun_prop

lemma norm_greenPhase (ξ : PDE.Vec d) (p : GreenCarrier d) : ‖greenPhase d ξ p‖ = 1 := by
  rw [greenPhase_eq ξ p.1 p.2]
  exact norm_fourierPhase ξ 0 p.2

/-- The slab set of a measurable `E ⊆ SlabBase`. -/
lemma slabPreimage_eq {d : ℕ} (T : ℝ) (E : Set (SlabBase d)) :
    {p : GreenCarrier d | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T} =
      (fun p : GreenCarrier d => (p.1, p.2.1)) ⁻¹' E ∩ slabSet T := by
  ext p; simp [slabSet, slabTimeSet]

lemma measurableSet_slabPreimage {d : ℕ} (T : ℝ) {E : Set (SlabBase d)} (hE : MeasurableSet E) :
    MeasurableSet {p : GreenCarrier d | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T} := by
  rw [slabPreimage_eq]
  exact (hE.preimage (by fun_prop)).inter (measurableSet_slabSet T)

/-- **Domination of the Fourier marginal (`#fourier-domination`, inequality for sets).** -/
theorem slab_domination_ineq
    (hcov : IsTranslationCovariantEvolution (wholeSpace d) (fun _ => 0) MeasurableSet.univ K)
    (hcomp : K.HasComposition MeasurableSet.univ) (σ₀ : ℝ)
    (μ : Measure (EvolutionState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) σ₀))
    [IsFiniteMeasure μ] (Γ : Measure (GreenCarrier d)) (hΓ : IsGreenMeasure K σ₀ ⊤ μ Γ)
    {T : ℝ} (hT : 0 < T) (ξ : PDE.Vec d) {E : Set (SlabBase d)} (hE : MeasurableSet E) :
    ‖∫ p in {p : GreenCarrier d | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T},
        greenPhase d ξ p ∂Γ‖ₑ ≤
      ∫⁻ v, (∫⁻ τ in slabTimeSet T, occupationKernel K (σ₀ + T / 2) (τ.1 - T / 2) v
          {w | (τ, w) ∈ E} ∂elapsedVolume ⊤) ∂(halfMeasure K σ₀ T hT.le μ ξ).variation := by
  set ρ := (halfMeasure K σ₀ T hT.le μ ξ).variation with hρ
  have hρfin : IsFiniteMeasure ρ :=
    evolved_variation_finite μ _ _ _ (measurable_halfPhase ξ _) (norm_halfPhase ξ _)
  have hSEm := measurableSet_slabPreimage T hE
  set SE : Set (GreenCarrier d) := {p | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T} with hSE
  have hSEsub : SE ⊆ slabSet T := by
    intro p hp; exact ⟨hp.2.1, hp.2.2⟩
  have hf1m : Measurable (SE.indicator (greenPhase d ξ)) :=
    (measurable_greenPhase ξ).indicator hSEm
  have hf1b : ∀ p, ‖SE.indicator (greenPhase d ξ) p‖ ≤ 1 := by
    intro p
    by_cases hp : p ∈ SE
    · rw [Set.indicator_of_mem hp, norm_greenPhase]
    · rw [Set.indicator_of_notMem hp, norm_zero]; exact zero_le_one
  have hf1s : ∀ p, p ∉ slabSet T → SE.indicator (greenPhase d ξ) p = 0 :=
    fun p hp => Set.indicator_of_notMem (fun h => hp (hSEsub h)) _
  rw [← integral_indicator hSEm,
    green_integral K σ₀ μ Γ hΓ hT _ hf1m hf1b hf1s]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  have hmeas : Measurable (fun x : ElapsedTime ⊤ × PDE.Vec d =>
      occupationKernel K (σ₀ + T / 2) (x.1.1 - T / 2) x.2 {w | (x.1, w) ∈ E}) := by
    have hE' : MeasurableSet {z : (ElapsedTime ⊤ × PDE.Vec d) × PDE.Vec d | (z.1.1, z.2) ∈ E} :=
      hE.preimage (by fun_prop)
    exact measurable_occupationKernel_sectionGen K (σ₀ + T / 2)
      (f := fun x : ElapsedTime ⊤ × PDE.Vec d => x.1.1 - T / 2) (u := fun x => x.2)
      (by fun_prop) (by fun_prop) hE'
  calc ∫⁻ τ, ‖∫ p, ∫ w, SE.indicator (greenPhase d ξ) (τ, w) ∂K.master (elapsedQuery σ₀ p τ) ∂μ‖ₑ
        ∂elapsedVolume ⊤
      ≤ ∫⁻ τ, (slabTimeSet T).indicator (fun τ => ∫⁻ v, occupationKernel K (σ₀ + T / 2)
          (τ.1 - T / 2) v {w | (τ, w) ∈ E} ∂ρ) τ ∂elapsedVolume ⊤ := by
        refine lintegral_mono (fun τ => ?_)
        by_cases hτ : τ ∈ slabTimeSet T
        · rw [Set.indicator_of_mem hτ]
          have hsec : MeasurableSet {w' : PDE.Vec d | (τ, w') ∈ E} := measurable_prodMk_left hE
          have hfun : ∀ w : EvolutionAmbientState d, SE.indicator (greenPhase d ξ) (τ, w) =
              phaseSection d ξ {w' : PDE.Vec d | (τ, w') ∈ E} w := by
            intro w
            unfold phaseSection
            by_cases hw : (τ, w.1) ∈ E
            · have h1 : (τ, w) ∈ SE := ⟨hw, hτ.1, hτ.2⟩
              have h2 : w ∈ ({w' : PDE.Vec d | (τ, w') ∈ E} ×ˢ (univ : Set (PDE.Vec d))) :=
                ⟨hw, mem_univ _⟩
              rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2, greenPhase_eq]
            · have h1 : (τ, w) ∉ SE := fun h => hw h.1
              have h2 : w ∉ ({w' : PDE.Vec d | (τ, w') ∈ E} ×ˢ (univ : Set (PDE.Vec d))) :=
                fun h => hw h.1
              rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
          simp_rw [hfun]
          exact slab_section_bound K hcov hcomp σ₀ μ hT ξ τ hτ.1 hsec
        · rw [Set.indicator_of_notMem hτ]
          have hz : ∀ w : EvolutionAmbientState d, SE.indicator (greenPhase d ξ) (τ, w) = 0 :=
            fun w => Set.indicator_of_notMem (fun h => hτ ⟨h.2.1, h.2.2⟩) _
          simp [hz]
    _ = ∫⁻ τ in slabTimeSet T, ∫⁻ v, occupationKernel K (σ₀ + T / 2) (τ.1 - T / 2) v
          {w | (τ, w) ∈ E} ∂ρ ∂elapsedVolume ⊤ :=
        lintegral_indicator (measurableSet_slabTimeSet T) _
    _ = _ := by
        refine lintegral_lintegral_swap ?_
        exact hmeas.aemeasurable

end HypoellipticAleksandrov.KineticAleksandrov.Green
