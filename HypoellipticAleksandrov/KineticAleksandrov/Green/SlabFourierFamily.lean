module

public import HypoellipticAleksandrov.KineticAleksandrov.Green.SlabFourierDomination
public import HypoellipticAleksandrov.KineticAleksandrov.Green.SlabFourierIntegral
public import Mathlib.Probability.Kernel.RadonNikodym
public import Mathlib.Probability.Kernel.WithDensity

/-!
# A jointly measurable family of Fourier densities

The densities `k^ξ` of Lemma 5.1 can be chosen so that `(ξ, y) ↦ k^ξ(y)` is Borel; this is
what makes `ξ ↦ ‖k^ξ‖_{L^γ}` measurable (`#frequency-integral`).  Construction: the four positive
channels `ofReal(±Re e^{-iξ·z})`, `ofReal(±Im e^{-iξ·z})` give finite kernels `ξ ↦ κ_j^ξ` on the
slab base, each dominated by the marginal of `Γ`; their kernel Radon-Nikodym derivatives with
respect to the finite reference measure `m' = w · slabBase` (`w = e^{-|y|^{2/3}} > 0`) are jointly
measurable (`ProbabilityTheory.Kernel.rnDeriv`).
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Green

open MeasureTheory ProbabilityTheory Set
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal NNReal

variable {d : ℕ}

/-- The positive weight `w(τ, y) = exp(-|y|^{2/3})` making `w · slabBase` finite. -/
def slabWeight (d : ℕ) (y : SlabBase d) : ℝ≥0∞ := decayProfile d 1 y.2

lemma measurable_slabWeight (d : ℕ) : Measurable (slabWeight d) :=
  (measurable_decayProfile d 1).comp measurable_snd

lemma slabWeight_pos (y : SlabBase d) : 0 < slabWeight d y :=
  ENNReal.ofReal_pos.2 (Real.exp_pos _)

lemma slabWeight_lt_top (y : SlabBase d) : slabWeight d y < ⊤ := ENNReal.ofReal_lt_top

/-- The finite reference measure `m' = w · slabBase`. -/
def slabRef (d : ℕ) (T : ℝ) : Measure (SlabBase d) := (slabBase d T).withDensity (slabWeight d)

lemma isFiniteMeasure_slabRef (hd : 0 < d) {T : ℝ} (hT : 0 < T) :
    IsFiniteMeasure (slabRef d T) := by
  refine ⟨?_⟩
  rw [slabRef, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have h : ∫⁻ y, slabWeight d y ∂slabBase d T =
      (∫⁻ _τ : ElapsedTime ⊤, (1 : ℝ≥0∞) ∂(elapsedVolume ⊤).restrict (slabTimeSet T)) *
        ∫⁻ ζ, decayProfile d 1 ζ := by
    unfold slabBase slabWeight
    have := lintegral_prod_mul (μ := (elapsedVolume ⊤).restrict (slabTimeSet T))
      (ν := (volume : Measure (PDE.Vec d))) (f := fun _ => (1 : ℝ≥0∞))
      (g := decayProfile d 1) aemeasurable_const (measurable_decayProfile d 1).aemeasurable
    simpa only [one_mul] using this
  rw [h, lintegral_const, one_mul, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    elapsedVolume_slabTimeSet hT]
  exact ENNReal.mul_lt_top (by simp)
    (lintegral_decayProfile_lt_top hd one_pos)


/-- The `ℝ≥0∞`-valued density `ofReal (F (e^{-iξ·z'}))` on the Green carrier. -/
def phaseDensity (d : ℕ) (F : ℂ → ℝ) (ξ : PDE.Vec d) (p : GreenCarrier d) : ℝ≥0∞ :=
  ENNReal.ofReal (F (greenPhase d ξ p))

lemma measurable_greenPhase_joint (d : ℕ) :
    Measurable (fun x : PDE.Vec d × GreenCarrier d => greenPhase d x.1 x.2) := by
  unfold greenPhase PDE.vecDot
  fun_prop

lemma measurable_phaseDensity {F : ℂ → ℝ} (hF : Measurable F) :
    Measurable (Function.uncurry (phaseDensity d F)) :=
  ENNReal.measurable_ofReal.comp (hF.comp (measurable_greenPhase_joint d))

/-- The kernel `ξ ↦` pushforward of `φ_ξ`-channel `F` times `Γ|slab` to the slab base. -/
def phaseKernel (d : ℕ) (T : ℝ) (Γ : Measure (GreenCarrier d)) [IsFiniteMeasure
    (Γ.restrict (slabSet (d := d) T))] (F : ℂ → ℝ) : Kernel (PDE.Vec d) (SlabBase d) :=
  (Kernel.withDensity (Kernel.const (PDE.Vec d) (Γ.restrict (slabSet T)))
    (phaseDensity d F)).map (fun p : GreenCarrier d => (p.1, p.2.1))

section

variable {T : ℝ} {Γ : Measure (GreenCarrier d)} [IsFiniteMeasure (Γ.restrict (slabSet (d := d) T))]
  {F : ℂ → ℝ}

lemma phaseKernel_apply (hF : Measurable F) (ξ : PDE.Vec d) {E : Set (SlabBase d)}
    (hE : MeasurableSet E) :
    phaseKernel d T Γ F ξ E =
      ∫⁻ p in {p : GreenCarrier d | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T},
        phaseDensity d F ξ p ∂Γ := by
  have hπ : Measurable (fun p : GreenCarrier d => (p.1, p.2.1)) := by fun_prop
  unfold phaseKernel
  rw [Kernel.map_apply' _ hπ _ hE, Kernel.withDensity_apply' _ (measurable_phaseDensity hF),
    Kernel.const_apply, Measure.restrict_restrict (hπ hE), slabPreimage_eq T E, inter_comm]

lemma phaseKernel_le (hF : Measurable F) (hFb : ∀ z : ℂ, ‖z‖ = 1 → F z ≤ 1) (ξ : PDE.Vec d)
    {E : Set (SlabBase d)} (hE : MeasurableSet E) :
    phaseKernel d T Γ F ξ E ≤
      Γ {p : GreenCarrier d | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T} := by
  rw [phaseKernel_apply hF ξ hE]
  calc ∫⁻ p in {p : GreenCarrier d | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T},
        phaseDensity d F ξ p ∂Γ
      ≤ ∫⁻ _p in {p : GreenCarrier d | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T}, 1 ∂Γ := by
        refine lintegral_mono (fun p => ?_)
        unfold phaseDensity
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (hFb _ (norm_greenPhase ξ p))
    _ = _ := by rw [setLIntegral_const, one_mul]

theorem phaseKernel_isFiniteKernel (hFb : ∀ z : ℂ, ‖z‖ = 1 → F z ≤ 1) :
    IsFiniteKernel (phaseKernel d T Γ F) := by
  have h : IsFiniteKernel (Kernel.withDensity (Kernel.const (PDE.Vec d) (Γ.restrict (slabSet T)))
      (phaseDensity d F)) := by
    refine Kernel.isFiniteKernel_withDensity_of_bounded _ (B := 1) ENNReal.one_ne_top
      (fun ξ p => ?_)
    unfold phaseDensity
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (hFb _ (norm_greenPhase ξ p))
  unfold phaseKernel
  infer_instance


/-- **One real channel.**  A jointly measurable family `r^ξ ≥ 0` of densities, on the slab base,
of the measures `E ↦ ∫_{S_E} ofReal (F (e^{-iξ·z'})) dΓ`. -/
theorem exists_channel (hd : 0 < d) (hT : 0 < T) (hF : Measurable F)
    (hFb : ∀ z : ℂ, ‖z‖ = 1 → F z ≤ 1) (g : SlabBase d → ℝ≥0∞)
    (hg : ∀ E : Set (SlabBase d), MeasurableSet E →
      Γ {p | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T} = ∫⁻ y in E, g y ∂slabBase d T) :
    ∃ r : PDE.Vec d → SlabBase d → ℝ, Measurable (Function.uncurry r) ∧ (∀ ξ y, 0 ≤ r ξ y) ∧
      ∀ ξ, Integrable (r ξ) (slabBase d T) ∧ ∀ E : Set (SlabBase d), MeasurableSet E →
        ∫ y in E, r ξ y ∂slabBase d T =
          (∫⁻ p in {p : GreenCarrier d | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T},
            ENNReal.ofReal (F (greenPhase d ξ p)) ∂Γ).toReal := by
  have hmfin := isFiniteMeasure_slabRef hd hT
  have hκfin := phaseKernel_isFiniteKernel (d := d) (T := T) (Γ := Γ) (F := F) hFb
  set κ := phaseKernel d T Γ F with hκ
  let η : Kernel (PDE.Vec d) (SlabBase d) := Kernel.const (PDE.Vec d) (slabRef d T)
  have hac : ∀ ξ, κ ξ ≪ η ξ := by
    intro ξ s hs
    rw [Kernel.const_apply] at hs
    obtain ⟨t, hst, ht, hnull⟩ := exists_measurable_superset_of_null hs
    refine measure_mono_null hst ?_
    have h1 : slabBase d T t = 0 := by
      rw [slabRef, withDensity_apply _ ht] at hnull
      have h2 := (lintegral_eq_zero_iff' (measurable_slabWeight d).aemeasurable).1 hnull
      have h3 : ∀ᵐ x ∂(slabBase d T).restrict t, False :=
        h2.mono (fun x hx => (slabWeight_pos x).ne' hx)
      rw [Filter.eventually_false_iff_eq_bot, ae_eq_bot] at h3
      have := congrArg (fun μ => μ univ) h3
      simpa using this
    have h2 := phaseKernel_le (T := T) (Γ := Γ) hF hFb ξ ht
    rw [hg t ht, setLIntegral_measure_zero _ _ h1] at h2
    exact nonpos_iff_eq_zero.1 h2
  have hset : ∀ (ξ : PDE.Vec d) (E : Set (SlabBase d)), MeasurableSet E →
      ∫⁻ y in E, slabWeight d y * κ.rnDeriv η ξ y ∂slabBase d T = κ ξ E := by
    intro ξ E hE
    have hr : Measurable (fun y => κ.rnDeriv η ξ y) :=
      (Kernel.measurable_rnDeriv κ η).comp (measurable_const.prodMk measurable_id)
    have h1 := setLIntegral_withDensity_eq_setLIntegral_mul (slabBase d T)
      (measurable_slabWeight d) hr hE
    have h2 := Kernel.setLIntegral_rnDeriv (hac ξ) hE
    rw [Kernel.const_apply] at h2
    exact h1.symm.trans h2
  refine ⟨fun ξ y => (slabWeight d y * κ.rnDeriv η ξ y).toReal, ?_,
    fun ξ y => ENNReal.toReal_nonneg,
    fun ξ => ?_⟩
  · exact ENNReal.measurable_toReal.comp (((measurable_slabWeight d).comp measurable_snd).mul
      (Kernel.measurable_rnDeriv κ η))
  · have hr : Measurable (fun y => κ.rnDeriv η ξ y) :=
      (Kernel.measurable_rnDeriv κ η).comp (measurable_const.prodMk measurable_id)
    have hmeas : Measurable (fun y => slabWeight d y * κ.rnDeriv η ξ y) :=
      (measurable_slabWeight d).mul hr
    have hfin : ∫⁻ y, slabWeight d y * κ.rnDeriv η ξ y ∂slabBase d T ≠ ⊤ := by
      have := hset ξ univ MeasurableSet.univ
      rw [Measure.restrict_univ] at this
      rw [this]
      exact measure_ne_top _ _
    refine ⟨integrable_toReal_of_lintegral_ne_top hmeas.aemeasurable hfin, fun E hE => ?_⟩
    have hfinE : ∫⁻ y in E, slabWeight d y * κ.rnDeriv η ξ y ∂slabBase d T ≠ ⊤ := by
      rw [hset ξ E hE]; exact measure_ne_top _ _
    rw [integral_toReal hmeas.aemeasurable (ae_lt_top hmeas hfinE), hset ξ E hE,
      hκ, phaseKernel_apply (T := T) (Γ := Γ) hF ξ hE]
    rfl

end

/-- **A jointly Borel family of Fourier densities.**  For every `ξ` the function `k^ξ` is a density
of the complex measure `E ↦ ∫_{(τ,w)∈E, T<τ<2T} e^{-iξ·z'} dΓ`, and `(ξ, y) ↦ k^ξ(y)` is Borel. -/
theorem exists_measurable_fourier_family (hd : 0 < d) {T : ℝ} (hT : 0 < T)
    (Γ : Measure (GreenCarrier d)) [IsFiniteMeasure (Γ.restrict (slabSet (d := d) T))]
    (g : SlabBase d → ℝ≥0∞)
    (hg : ∀ E : Set (SlabBase d), MeasurableSet E →
      Γ {p | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T} = ∫⁻ y in E, g y ∂slabBase d T) :
    ∃ k : PDE.Vec d → SlabBase d → ℂ, Measurable (Function.uncurry k) ∧
      ∀ ξ, Integrable (k ξ) (slabBase d T) ∧ ∀ E : Set (SlabBase d), MeasurableSet E →
        ∫ y in E, k ξ y ∂slabBase d T =
          ∫ p in {p : GreenCarrier d | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T},
            greenPhase d ξ p ∂Γ := by
  have hre : ∀ z : ℂ, ‖z‖ = 1 → z.re ≤ 1 :=
    fun z hz => (le_abs_self _).trans ((Complex.abs_re_le_norm z).trans hz.le)
  have hnre : ∀ z : ℂ, ‖z‖ = 1 → -z.re ≤ 1 :=
    fun z hz => (neg_le_abs _).trans ((Complex.abs_re_le_norm z).trans hz.le)
  have him : ∀ z : ℂ, ‖z‖ = 1 → z.im ≤ 1 :=
    fun z hz => (le_abs_self _).trans ((Complex.abs_im_le_norm z).trans hz.le)
  have hnim : ∀ z : ℂ, ‖z‖ = 1 → -z.im ≤ 1 :=
    fun z hz => (neg_le_abs _).trans ((Complex.abs_im_le_norm z).trans hz.le)
  obtain ⟨r1, hm1, -, h1⟩ := exists_channel (Γ := Γ) (F := fun z : ℂ => z.re) hd hT
    Complex.measurable_re hre g hg
  obtain ⟨r2, hm2, -, h2⟩ := exists_channel (Γ := Γ) (F := fun z : ℂ => -z.re) hd hT
    Complex.measurable_re.neg hnre g hg
  obtain ⟨r3, hm3, -, h3⟩ := exists_channel (Γ := Γ) (F := fun z : ℂ => z.im) hd hT
    Complex.measurable_im him g hg
  obtain ⟨r4, hm4, -, h4⟩ := exists_channel (Γ := Γ) (F := fun z : ℂ => -z.im) hd hT
    Complex.measurable_im.neg hnim g hg
  refine ⟨fun ξ y => ((r1 ξ y - r2 ξ y : ℝ) : ℂ) + ((r3 ξ y - r4 ξ y : ℝ) : ℂ) * Complex.I,
    ?_, fun ξ => ⟨?_, fun E hE => ?_⟩⟩
  · exact ((Complex.measurable_ofReal.comp (hm1.sub hm2)).add
      ((Complex.measurable_ofReal.comp (hm3.sub hm4)).mul_const Complex.I))
  · exact (((h1 ξ).1.sub (h2 ξ).1).ofReal).add
      (((h3 ξ).1.sub (h4 ξ).1).ofReal.mul_const Complex.I)
  · have hki : Integrable (fun y => ((r1 ξ y - r2 ξ y : ℝ) : ℂ) +
        ((r3 ξ y - r4 ξ y : ℝ) : ℂ) * Complex.I) (slabBase d T) :=
      (((h1 ξ).1.sub (h2 ξ).1).ofReal).add
        (((h3 ξ).1.sub (h4 ξ).1).ofReal.mul_const Complex.I)
    have hSEm := measurableSet_slabPreimage T hE
    have hsub : {p : GreenCarrier d | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T} ⊆
        slabSet T := fun p hp => ⟨hp.2.1, hp.2.2⟩
    have hΓE : IsFiniteMeasure (Γ.restrict
        {p : GreenCarrier d | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T}) :=
      isFiniteMeasure_of_le (Γ.restrict (slabSet (d := d) T)) (Measure.restrict_mono hsub le_rfl)
    have hφ : Integrable (greenPhase d ξ) (Γ.restrict
        {p : GreenCarrier d | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T}) :=
      integrable_phase_finite _ _ (measurable_greenPhase ξ) (norm_greenPhase ξ)
    apply Complex.ext
    · have e1 := integral_re (hki.restrict (s := E))
      have e2 := integral_re hφ
      simp only [RCLike.re_eq_complex_re] at e1 e2
      rw [← e1, ← e2]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
      rw [integral_sub (h1 ξ).1.integrableOn (h2 ξ).1.integrableOn, (h1 ξ).2 E hE, (h2 ξ).2 E hE]
      exact (integral_eq_lintegral_pos_part_sub_lintegral_neg_part hφ.re).symm
    · have e1 := integral_im (hki.restrict (s := E))
      have e2 := integral_im hφ
      simp only [RCLike.im_eq_complex_im] at e1 e2
      rw [← e1, ← e2]
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.I_re, mul_zero, Complex.ofReal_re, Complex.I_im, mul_one, zero_add, add_zero]
      rw [integral_sub (h3 ξ).1.integrableOn (h4 ξ).1.integrableOn, (h3 ξ).2 E hE, (h4 ξ).2 E hE]
      exact (integral_eq_lintegral_pos_part_sub_lintegral_neg_part hφ.im).symm

end HypoellipticAleksandrov.KineticAleksandrov.Green
