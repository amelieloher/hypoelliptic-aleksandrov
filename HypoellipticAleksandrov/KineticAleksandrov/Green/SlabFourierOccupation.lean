module

public import HypoellipticAleksandrov.KineticAleksandrov.Green.SlabFourierPremises
public import HypoellipticAleksandrov.KineticAleksandrov.Green.SlabFourierEmbedding
import Mathlib.Probability.Kernel.MeasurableIntegral

/-!
# From bounded-Borel occupation densities to set identities

`SlabOccupationDensity` (the characterization (4.2), tested on bounded Borel `φ`) is
specialised to indicators `φ = 1_A` and converted to an identity of lower Lebesgue integrals
on the real line:
`∫⁻ q in A, ofReal (g q) = ∫⁻ v ∂ρ, ∫⁻ t in (0,S), P_{σ₀,σ₀+t}(v){w | (t,w) ∈ A}`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Green

open MeasureTheory Set
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal NNReal

lemma occupationKernel_of_nonneg {d : ℕ}
    (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
    (σ t : ℝ) (ht : 0 ≤ t) (v : PDE.Vec d) :
    occupationKernel K σ t v =
      K.firstMarginal (wholeSpaceQuery σ (σ + t) (le_add_of_nonneg_right ht) v 0) := by
  unfold occupationKernel
  have hc : ∀ (a b : ℝ) (h₁ : σ ≤ a) (h₂ : σ ≤ b), a = b →
      wholeSpaceQuery σ a h₁ v 0 = wholeSpaceQuery σ b h₂ v 0 := by
    rintro a b h₁ h₂ rfl; rfl
  rw [hc _ _ _ _ (by rw [max_eq_left ht])]

lemma measurable_occupationQuery {d : ℕ} (σ : ℝ) :
    Measurable (fun x : ℝ × PDE.Vec d =>
      wholeSpaceQuery σ (σ + max x.1 0) (le_add_of_nonneg_right (le_max_right x.1 0)) x.2 0) := by
  apply Measurable.subtype_mk
  fun_prop

instance firstMarginal_isFiniteKernel {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}
    (K : MovingFiberKernel Ω γ) : ProbabilityTheory.IsFiniteKernel K.firstMarginal := by
  unfold MovingFiberKernel.firstMarginal
  infer_instance

instance occupationKernel_isFiniteMeasure {d : ℕ}
    (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d))) (σ t : ℝ) (v : PDE.Vec d) :
    IsFiniteMeasure (occupationKernel K σ t v) := by
  unfold occupationKernel; infer_instance

lemma occupationKernel_univ_le {d : ℕ}
    (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d))) (σ t : ℝ) (v : PDE.Vec d) :
    occupationKernel K σ t v univ ≤ 1 := by
  unfold occupationKernel
  rw [MovingFiberKernel.firstMarginal, ProbabilityTheory.Kernel.fst_apply,
    Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ]
  exact K.mass_le_one _

lemma measurable_occupationKernel_section {d : ℕ}
    (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d))) (σ : ℝ)
    {A : Set (ℝ × PDE.Vec d)} (hA : MeasurableSet A) :
    Measurable (fun x : ℝ × PDE.Vec d => occupationKernel K σ x.1 x.2 {w | (x.1, w) ∈ A}) := by
  let κ : ProbabilityTheory.Kernel (ℝ × PDE.Vec d) (PDE.Vec d) :=
    K.firstMarginal.comap _ (measurable_occupationQuery σ)
  have hS : MeasurableSet {z : (ℝ × PDE.Vec d) × PDE.Vec d | (z.1.1, z.2) ∈ A} :=
    hA.preimage (by fun_prop)
  exact ProbabilityTheory.Kernel.measurable_kernel_prodMk_left (κ := κ) hS

/-- Bounded Borel indicator of a measurable set. -/
def indicatorBB {α : Type*} [MeasurableSpace α] {A : Set α} (hA : MeasurableSet A) :
    BoundedBorel α :=
  ⟨A.indicator (fun _ => (1 : ℝ)), measurable_const.indicator hA, 1, zero_le_one,
    fun x => by by_cases hx : x ∈ A <;> simp [hx]⟩

lemma indicatorBB_apply {α : Type*} [MeasurableSpace α] {A : Set α} (hA : MeasurableSet A)
    (x : α) : indicatorBB hA x = A.indicator (fun _ => (1 : ℝ)) x := rfl

lemma integral_indicatorBB_occupation {d : ℕ}
    (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d))) (σ t : ℝ) (v : PDE.Vec d)
    {A : Set (ℝ × PDE.Vec d)} (hA : MeasurableSet A) :
    ∫ w, indicatorBB hA (t, w) ∂occupationKernel K σ t v =
      (occupationKernel K σ t v {w | (t, w) ∈ A}).toReal := by
  have hs : MeasurableSet {w : PDE.Vec d | (t, w) ∈ A} := measurable_prodMk_left hA
  have hf : (fun w => indicatorBB hA (t, w)) =
      {w : PDE.Vec d | (t, w) ∈ A}.indicator (fun _ => (1 : ℝ)) := by
    funext w; simp [indicatorBB_apply, Set.indicator]
  rw [hf, integral_indicator_const _ hs]
  simp [measureReal_def]


lemma elapsed_finite_set (S : ℝ) (hS : 0 < S) :
    {τ : ℝ | 0 < τ ∧ ENNReal.ofReal τ < ENNReal.ofReal S} = Ioo 0 S := by
  ext τ
  simp only [mem_ofPred_eq, mem_Ioo, ENNReal.ofReal_lt_ofReal_iff hS]

lemma integral_elapsed_finite (S : ℝ) (hS : 0 < S) (F : ℝ → ℝ) :
    ∫ τ : ElapsedTime (ENNReal.ofReal S), F τ.1 ∂elapsedVolume (ENNReal.ofReal S) =
      ∫ t in Ioo 0 S, F t := by
  have h := integral_subtype_comap (μ := (volume : Measure ℝ))
    (measurableSet_elapsedTime (ENNReal.ofReal S)) F
  refine Eq.trans h ?_
  rw [elapsed_finite_set S hS]

lemma lintegral_elapsed_finite (S : ℝ) (hS : 0 < S) (F : ℝ → ℝ≥0∞) :
    ∫⁻ τ : ElapsedTime (ENNReal.ofReal S), F τ.1 ∂elapsedVolume (ENNReal.ofReal S) =
      ∫⁻ t in Ioo 0 S, F t := by
  have h := lintegral_subtype_comap (μ := (volume : Measure ℝ))
    (measurableSet_elapsedTime (ENNReal.ofReal S)) F
  refine Eq.trans h ?_
  rw [elapsed_finite_set S hS]

/-- The right-hand side of (4.2) for an indicator, as a real number. -/
lemma occupation_rhs_indicator {d : ℕ}
    (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d))) (σ S : ℝ) (hS : 0 < S)
    (ρ : Measure (PDE.Vec d)) [IsFiniteMeasure ρ] {A : Set (ℝ × PDE.Vec d)}
    (hA : MeasurableSet A) :
    (∫ v, ∫ τ : ElapsedTime (ENNReal.ofReal S), ∫ w, indicatorBB hA (τ.1, w)
        ∂K.firstMarginal (wholeSpaceQuery σ (σ + τ.1)
          (le_add_of_nonneg_right τ.2.1.le) v 0)
        ∂elapsedVolume (ENNReal.ofReal S) ∂ρ) =
      (∫⁻ v, (∫⁻ t in Ioo 0 S, occupationKernel K σ t v {w | (t, w) ∈ A}) ∂ρ).toReal := by
  have hmeas := measurable_occupationKernel_section K σ hA
  have h1 : ∀ v, (∫ τ : ElapsedTime (ENNReal.ofReal S), ∫ w, indicatorBB hA (τ.1, w)
        ∂K.firstMarginal (wholeSpaceQuery σ (σ + τ.1)
          (le_add_of_nonneg_right τ.2.1.le) v 0) ∂elapsedVolume (ENNReal.ofReal S)) =
      (∫⁻ t in Ioo 0 S, occupationKernel K σ t v {w | (t, w) ∈ A}).toReal := by
    intro v
    have h2 : ∀ τ : ElapsedTime (ENNReal.ofReal S),
        (∫ w, indicatorBB hA (τ.1, w) ∂K.firstMarginal (wholeSpaceQuery σ (σ + τ.1)
          (le_add_of_nonneg_right τ.2.1.le) v 0)) =
        (fun t : ℝ => (occupationKernel K σ t v {w | (t, w) ∈ A}).toReal) τ.1 := by
      intro τ
      rw [← occupationKernel_of_nonneg K σ τ.1 τ.2.1.le v]
      exact integral_indicatorBB_occupation K σ τ.1 v hA
    refine (integral_congr_ae (Filter.Eventually.of_forall h2)).trans ?_
    refine (integral_elapsed_finite S hS
      (fun t : ℝ => (occupationKernel K σ t v {w | (t, w) ∈ A}).toReal)).trans ?_
    refine integral_toReal ?_ ?_
    · exact ((hmeas.comp (measurable_id.prodMk measurable_const))).aemeasurable
    · refine Filter.Eventually.of_forall (fun t => ?_)
      exact (measure_lt_top _ _)
  simp_rw [h1]
  refine integral_toReal ?_ ?_
  · refine Measurable.aemeasurable ?_
    exact (hmeas.comp measurable_swap).lintegral_prod_right'
  · refine Filter.Eventually.of_forall (fun v => ?_)
    calc ∫⁻ t in Ioo 0 S, occupationKernel K σ t v {w | (t, w) ∈ A}
        ≤ ∫⁻ t in Ioo 0 S, 1 := by
          refine lintegral_mono (fun t => ?_)
          exact (measure_mono (subset_univ _)).trans (occupationKernel_univ_le K σ t v)
      _ < ⊤ := by
          rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter,
            Real.volume_Ioo]
          simp


/-- **Occupation identity for sets.**  (4.2) tested on `1_A`, as lower integrals. -/
theorem occupation_set_identity {d : ℕ}
    (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d))) (σ S : ℝ) (hS : 0 < S)
    (ρ : Measure (PDE.Vec d)) [IsFiniteMeasure ρ] (g : ℝ × PDE.Vec d → ℝ)
    (hg : SlabOccupationDensity K σ S ρ g)
    (hint : Integrable g (volume.restrict (Ioo (0 : ℝ) S ×ˢ (univ : Set (PDE.Vec d)))))
    {A : Set (ℝ × PDE.Vec d)} (hA : MeasurableSet A)
    (hAS : A ⊆ Ioo (0 : ℝ) S ×ˢ (univ : Set (PDE.Vec d))) :
    ∫⁻ q in A, ENNReal.ofReal (g q) =
      ∫⁻ v, (∫⁻ t in Ioo 0 S, occupationKernel K σ t v {w | (t, w) ∈ A}) ∂ρ := by
  obtain ⟨hgm, hgn, hchar⟩ := hg
  have h := hchar (indicatorBB hA)
  rw [occupation_rhs_indicator K σ S hS ρ hA] at h
  set R : Set (ℝ × PDE.Vec d) := Ioo (0 : ℝ) S ×ˢ (univ : Set (PDE.Vec d)) with hR
  have hrestr : (volume.restrict R).restrict A = volume.restrict A := by
    rw [Measure.restrict_restrict hA, inter_eq_left.2 hAS]
  have hL : (∫ q, indicatorBB hA q * g q ∂volume.restrict R) =
      (∫⁻ q in A, ENNReal.ofReal (g q)).toReal := by
    have h1 : (fun q => indicatorBB hA q * g q) = A.indicator g := by
      funext q; by_cases hq : q ∈ A <;> simp [indicatorBB_apply, Set.indicator, hq]
    rw [h1, integral_indicator hA, hrestr]
    exact integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hgn)
      hgm.aestronglyMeasurable
  rw [hL] at h
  have hfin1 : ∫⁻ q in A, ENNReal.ofReal (g q) ≠ ⊤ := by
    have hle : ∫⁻ q in A, ENNReal.ofReal (g q) ≤ ∫⁻ q, ‖g q‖ₑ ∂volume.restrict R := by
      rw [← hrestr]
      refine (lintegral_mono' Measure.restrict_le_self le_rfl).trans (lintegral_mono (fun q => ?_))
      simpa [Real.enorm_eq_ofReal_abs] using ENNReal.ofReal_le_ofReal (le_abs_self (g q))
    exact ne_top_of_le_ne_top hint.hasFiniteIntegral.ne hle
  have hfin2 : (∫⁻ v, (∫⁻ t in Ioo 0 S, occupationKernel K σ t v {w | (t, w) ∈ A}) ∂ρ) ≠ ⊤ := by
    have hle : (∫⁻ v, (∫⁻ t in Ioo 0 S, occupationKernel K σ t v {w | (t, w) ∈ A}) ∂ρ) ≤
        ∫⁻ _v, ENNReal.ofReal S ∂ρ := by
      refine lintegral_mono (fun v => ?_)
      calc ∫⁻ t in Ioo 0 S, occupationKernel K σ t v {w | (t, w) ∈ A}
          ≤ ∫⁻ t in Ioo 0 S, 1 := by
            refine lintegral_mono (fun t => ?_)
            exact (measure_mono (subset_univ _)).trans (occupationKernel_univ_le K σ t v)
        _ = ENNReal.ofReal S := by
            rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter,
              Real.volume_Ioo, sub_zero, one_mul]
    refine ne_top_of_le_ne_top ?_ hle
    rw [lintegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  exact (ENNReal.toReal_eq_toReal_iff' hfin1 hfin2).1 h


/-- Measurability of the occupation kernel evaluated on a measurable family of sections. -/
lemma measurable_occupationKernel_sectionGen {d : ℕ} {γ : Type*} [MeasurableSpace γ]
    (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d))) (σ : ℝ)
    {f : γ → ℝ} (hf : Measurable f) {u : γ → PDE.Vec d} (hu : Measurable u)
    {E : Set (γ × PDE.Vec d)} (hE : MeasurableSet E) :
    Measurable (fun x : γ => occupationKernel K σ (f x) (u x) {w | (x, w) ∈ E}) := by
  have hq : Measurable (fun x : γ =>
      wholeSpaceQuery σ (σ + max (f x) 0)
        (le_add_of_nonneg_right (le_max_right (f x) 0)) (u x) 0) := by
    apply Measurable.subtype_mk
    fun_prop
  let κ : ProbabilityTheory.Kernel γ (PDE.Vec d) := K.firstMarginal.comap _ hq
  exact ProbabilityTheory.Kernel.measurable_kernel_prodMk_left (κ := κ) hE


lemma lintegral_slabTime (T : ℝ) (hT : 0 ≤ T) (F : ℝ → ℝ≥0∞) :
    ∫⁻ τ in slabTimeSet T, F τ.1 ∂elapsedVolume ⊤ = ∫⁻ t in Ioo T (2 * T), F t := by
  have he : MeasurableEmbedding (Subtype.val : ElapsedTime ⊤ → ℝ) :=
    MeasurableEmbedding.subtype_coe (measurableSet_elapsedTime ⊤)
  rw [← map_slabTime T hT, he.lintegral_map]

lemma lintegral_Ioo_sub (a b s : ℝ) (H : ℝ → ℝ≥0∞) :
    ∫⁻ t in Ioo a b, H (t - s) = ∫⁻ t in Ioo (a - s) (b - s), H t := by
  have he : MeasurableEmbedding (fun t : ℝ => t - s) := (Homeomorph.subRight s).measurableEmbedding
  rw [← map_sub_restrict_Ioo a b s, he.lintegral_map]

lemma slabBase_ae_slab (d : ℕ) (T s : ℝ) (hT : 0 ≤ T) :
    ∀ᵐ y ∂slabBase d T, y.1.1 ∈ Ioo T (2 * T) := by
  have hB : MeasurableSet (Ioo (T - s) (2 * T - s) ×ˢ (univ : Set (PDE.Vec d))) :=
    measurableSet_Ioo.prod MeasurableSet.univ
  have h0 : slabBase d T ((slabShift d s) ⁻¹' (Ioo (T - s) (2 * T - s) ×ˢ univ)ᶜ) = 0 := by
    rw [← Measure.map_apply (measurable_slabShift d s) hB.compl, map_slabBase_slabShift d T s hT,
      Measure.restrict_apply hB.compl]
    simp
  rw [ae_iff]
  refine measure_mono_null (fun y hy => ?_) h0
  simp only [mem_ofPred_eq, mem_preimage, mem_compl_iff, mem_prod, mem_Ioo, mem_univ, and_true,
    slabShift] at hy ⊢
  intro h
  exact hy ⟨by linarith [h.1], by linarith [h.2]⟩


/-- The real-line set carried by `E ⊆ SlabBase`: shift and cut to the slab. -/
def slabImage (d : ℕ) (T s : ℝ) (E : Set (SlabBase d)) : Set (ℝ × PDE.Vec d) :=
  slabShift d s '' E ∩ (Ioo (T - s) (2 * T - s) ×ˢ (univ : Set (PDE.Vec d)))

lemma measurableSet_slabImage {d : ℕ} (T s : ℝ) {E : Set (SlabBase d)} (hE : MeasurableSet E) :
    MeasurableSet (slabImage d T s E) :=
  ((measurableEmbedding_slabShift d s).measurableSet_image.2 hE).inter
    (measurableSet_Ioo.prod MeasurableSet.univ)

lemma preimage_slabImage {d : ℕ} (T s : ℝ) (E : Set (SlabBase d)) :
    slabShift d s ⁻¹' slabImage d T s E = E ∩ {y | y.1.1 ∈ Ioo T (2 * T)} := by
  ext y
  simp only [slabImage, mem_preimage, mem_inter_iff, mem_image, mem_prod, mem_Ioo, mem_univ,
    and_true, mem_ofPred_eq, slabShift]
  constructor
  · rintro ⟨⟨y', hy', hyy'⟩, h1, h2⟩
    have : y' = y := (measurableEmbedding_slabShift d s).injective hyy'
    subst this
    exact ⟨hy', by linarith, by linarith⟩
  · rintro ⟨hy, h1, h2⟩
    exact ⟨⟨y, hy, rfl⟩, by linarith, by linarith⟩

lemma section_shift_image {d : ℕ} (s : ℝ) (E : Set (SlabBase d)) (τ : ElapsedTime ⊤) :
    {w | (τ.1 - s, w) ∈ slabShift d s '' E} = {w | (τ, w) ∈ E} := by
  ext w
  constructor
  · intro ⟨y, hy, hyψ⟩
    have h1 : y.1.1 - s = τ.1 - s := congrArg Prod.fst hyψ
    have h2 : y.2 = w := congrArg Prod.snd hyψ
    have h3 : y.1 = τ := Subtype.ext (by linarith)
    have h4 : y = (τ, w) := Prod.ext h3 h2
    rwa [h4] at hy
  · intro hw
    exact ⟨(τ, w), hw, rfl⟩

lemma section_slabImage {d : ℕ} (T s : ℝ) (E : Set (SlabBase d)) (t : ℝ) :
    {w | (t, w) ∈ slabImage d T s E} =
      if t ∈ Ioo (T - s) (2 * T - s) then {w | (t, w) ∈ slabShift d s '' E} else ∅ := by
  by_cases ht : t ∈ Ioo (T - s) (2 * T - s)
  · ext w
    simp [slabImage, ht, mem_prod]
  · ext w
    simp [slabImage, ht, mem_prod]

/-- **Occupation identity on the slab.**  If `g` is the occupation density (at horizon `S`, start
time `σ₁`) of `ρ`, then for measurable `E ⊆ SlabBase`, the `slabBase`-mass of `E` under the density
`ofReal (g ∘ slabShift s)` equals the occupation of `ρ` over the slab sections of `E`. -/
theorem slab_occupation_identity {d : ℕ}
    (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d))) (σ₁ s T S : ℝ)
    (hs : s ≤ T) (hT : 0 < T) (hTS : 2 * T - s ≤ S) (hS : 0 < S)
    (ρ : Measure (PDE.Vec d)) [IsFiniteMeasure ρ] (g : ℝ × PDE.Vec d → ℝ)
    (hg : SlabOccupationDensity K σ₁ S ρ g)
    (hint : Integrable g (volume.restrict (Ioo (0 : ℝ) S ×ˢ (univ : Set (PDE.Vec d)))))
    {E : Set (SlabBase d)} (hE : MeasurableSet E) :
    ∫⁻ y in E, ENNReal.ofReal (g (slabShift d s y)) ∂slabBase d T =
      ∫⁻ v, (∫⁻ τ in slabTimeSet T, occupationKernel K σ₁ (τ.1 - s) v {w | (τ, w) ∈ E}
        ∂elapsedVolume ⊤) ∂ρ := by
  have hA := measurableSet_slabImage T s hE
  have hAB : slabImage d T s E ⊆ Ioo (T - s) (2 * T - s) ×ˢ (univ : Set (PDE.Vec d)) :=
    inter_subset_right
  have hAS : slabImage d T s E ⊆ Ioo (0 : ℝ) S ×ˢ (univ : Set (PDE.Vec d)) := by
    intro q hq
    have := hAB hq
    simp only [mem_prod, mem_Ioo, mem_univ, and_true] at this ⊢
    constructor <;> linarith [this.1, this.2]
  have hid := occupation_set_identity K σ₁ S hS ρ g hg hint hA hAS
  -- left side
  have hL : ∫⁻ q in slabImage d T s E, ENNReal.ofReal (g q) =
      ∫⁻ y in E, ENNReal.ofReal (g (slabShift d s y)) ∂slabBase d T := by
    have hmap := map_slabBase_slabShift d T s hT.le
    have h1 : ∫⁻ q in slabImage d T s E, ENNReal.ofReal (g q) =
        ∫⁻ q in slabImage d T s E, ENNReal.ofReal (g q) ∂(slabBase d T).map (slabShift d s) := by
      rw [hmap, Measure.restrict_restrict hA, inter_eq_left.2 hAB]
    have hm : Measurable (fun q : ℝ × PDE.Vec d => ENNReal.ofReal (g q)) :=
      ENNReal.measurable_ofReal.comp hg.1
    rw [h1, setLIntegral_map hA hm (measurable_slabShift d s), preimage_slabImage]
    have hae : (E ∩ {y : SlabBase d | y.1.1 ∈ Ioo T (2 * T)}) =ᵐ[slabBase d T] E := by
      refine Filter.eventuallyEqSet_iff.2 ?_
      filter_upwards [slabBase_ae_slab d T s hT.le] with y hy
      exact ⟨fun h => h.1, fun h => ⟨h, hy⟩⟩
    rw [Measure.restrict_congr_set hae]
  rw [hL] at hid
  rw [hid]
  refine lintegral_congr (fun v => ?_)
  have hBt : MeasurableSet (Ioo (T - s) (2 * T - s)) := measurableSet_Ioo
  have hBsub : Ioo (T - s) (2 * T - s) ⊆ Ioo (0 : ℝ) S := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  set H : ℝ → ℝ≥0∞ := fun t =>
    occupationKernel K σ₁ t v {w | (t, w) ∈ slabShift d s '' E} with hH
  have h1 : ∀ t : ℝ, occupationKernel K σ₁ t v {w | (t, w) ∈ slabImage d T s E} =
      (Ioo (T - s) (2 * T - s)).indicator H t := by
    intro t
    rw [section_slabImage]
    by_cases ht : t ∈ Ioo (T - s) (2 * T - s) <;> simp [hH, ht]
  simp_rw [h1]
  rw [lintegral_indicator hBt, Measure.restrict_restrict hBt, inter_eq_left.2 hBsub,
    ← lintegral_Ioo_sub T (2 * T) s H, ← lintegral_slabTime T hT.le (fun t => H (t - s))]
  refine lintegral_congr (fun τ => ?_)
  simp only [hH, section_shift_image]

end HypoellipticAleksandrov.KineticAleksandrov.Green
