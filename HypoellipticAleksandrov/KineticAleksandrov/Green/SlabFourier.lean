module

public import HypoellipticAleksandrov.KineticAleksandrov.Green.SlabFourierBound
public import HypoellipticAleksandrov.KineticAleksandrov.Green.SlabFourierFamily
public import HypoellipticAleksandrov.KineticAleksandrov.Green.SlabFourierCovariance
public import HypoellipticAleksandrov.KineticAleksandrov.Green.SlabFourierIntegral
public import HypoellipticAleksandrov.KineticAleksandrov.Green.Main

/-!
# Lemma 5.1 (case W), conditional on Proposition 4.2 and Proposition 3.1

The conclusion `SlabFourierBounds` of Lemma 5.1 of the companion paper for the Green measure of
a realized case-W evolution.  The two not-yet-proved predecessors enter only through their
conclusions (`Green.SlabFourierPremises`): the occupation estimate and the decay estimate.
Everything else of the source proof (marginal density, half-time evolution and composition,
domination by the shifted occupation density, Radon-Nikodym density `k^ξ`, the scaling
`ζ = T^{3/2} ξ`) is proved.

* `slabFourierBounds_of_occupation_decay_kernel` / `..._meas_..._kernel`: per realized
  `(K, hcov, hcomp)` and constants (the `meas` version also returns jointly Borel `k^ξ`).
* `slabFourierBounds_of_occupation_decay` / `..._meas_...`: the family-level headline, exactly
  the `hbounds` of `TheoremA.green_density_bound_of_slabFourierBounds`: constants chosen first
  (depending only on `d` and the constants of the two premises), then every coefficient with
  bounds `λ, Λ`, realization, `σ₀`, finite `μ`, Green measure and `T > 0`.
* `slab_frequency_integral`: the frequency integral bound (measurable and `≤ C_γ M T^{β_γ-3d/2}`).
* `green_density_of_occupation_decay`: Theorem 2.4 (case W) conditional on Proposition 4.2,
  Proposition 3.1.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Green

open MeasureTheory Set
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal NNReal ProbabilityTheory

/-- The Gauss-type constant `∫ exp(-c|ζ|^{2/3}) dζ` of the frequency integral. -/
def slabFreqConstant (d : ℕ) (c : ℝ) : ℝ := (∫⁻ ζ, decayProfile d c ζ).toReal

/-- The structural constant `K₁(γ) = 2^{β_γ} (1 + C)(1 + (2π)^{-d} A_{c/2})`. -/
def slabK1 (d : ℕ) (Cdec cdec γ : ℝ) : ℝ :=
  (2 : ℝ) ^ slabBeta d γ * (1 + Cdec) *
    (1 + ((2 * Real.pi) ^ d)⁻¹ * slabFreqConstant d (cdec / 2))

/-- The constants `C_γ` of Lemma 5.1: `C_γ^{occ} · K₁(γ)`. -/
def slabConstant' (d : ℕ) (Cocc : ℝ → ℝ) (Cdec cdec : ℝ) (γ : ℝ) : ℝ≥0 :=
  Real.toNNReal (Cocc γ * slabK1 d Cdec cdec γ)

lemma slabK1_nonneg {d : ℕ} {Cdec : ℝ} (hCdec : 0 < Cdec) (cdec γ : ℝ) :
    0 ≤ slabK1 d Cdec cdec γ := by
  unfold slabK1 slabFreqConstant
  positivity

lemma one_le_slabK1_factor {d : ℕ} {Cdec : ℝ} (hCdec : 0 < Cdec) (cdec : ℝ) :
    1 ≤ (1 + Cdec) * (1 + ((2 * Real.pi) ^ d)⁻¹ * slabFreqConstant d (cdec / 2)) := by
  have : 0 ≤ ((2 * Real.pi) ^ d)⁻¹ * slabFreqConstant d (cdec / 2) := by
    unfold slabFreqConstant; positivity
  nlinarith


/-- Real arithmetic of the frequency integral. -/
lemma freq_arith (Co Cd a M t1 t2 A q : ℝ) (hCo : 0 ≤ Co) (hCd : 0 ≤ Cd) (ha : 0 ≤ a)
    (hM : 0 ≤ M) (ht1 : 0 ≤ t1) (ht2 : 0 ≤ t2) (hA : 0 ≤ A) (hq : 0 ≤ q) :
    q * ((Co * Cd * a) * M * t1 * (t2 * A)) ≤
      (Co * (a * (1 + Cd) * (1 + q * A))) * M * (t1 * t2) := by
  have hP : 0 ≤ Co * a * M * t1 * t2 := by positivity
  have key : q * Cd * A ≤ (1 + Cd) * (1 + q * A) := by
    nlinarith [mul_nonneg hq hA, mul_nonneg hCd (mul_nonneg hq hA)]
  calc q * ((Co * Cd * a) * M * t1 * (t2 * A)) = (Co * a * M * t1 * t2) * (q * Cd * A) := by ring
    _ ≤ (Co * a * M * t1 * t2) * ((1 + Cd) * (1 + q * A)) := mul_le_mul_of_nonneg_left key hP
    _ = _ := by ring

/-- The frequency-integral arithmetic in `ℝ≥0∞`. -/
lemma freq_ennreal (Co Cd a M t1 t2 A q K1 s : ℝ) (hCo : 0 ≤ Co) (hCd : 0 ≤ Cd) (ha : 0 ≤ a)
    (hM : 0 ≤ M) (ht1 : 0 ≤ t1) (ht2 : 0 ≤ t2) (hA : 0 ≤ A) (hq : 0 ≤ q)
    (hK : K1 = a * (1 + Cd) * (1 + q * A)) (hs : s = t1 * t2) :
    ENNReal.ofReal q * (ENNReal.ofReal (Co * Cd * a) * ENNReal.ofReal M * ENNReal.ofReal t1 *
        (ENNReal.ofReal t2 * ENNReal.ofReal A)) ≤
      ENNReal.ofReal (Co * K1) * ENNReal.ofReal M * ENNReal.ofReal s := by
  have h1 : 0 ≤ Co * Cd * a := by positivity
  have h2 : 0 ≤ Co * Cd * a * M := by positivity
  have h3 : 0 ≤ Co * Cd * a * M * t1 := by positivity
  have h4 : 0 ≤ t2 * A := by positivity
  have hK0 : 0 ≤ K1 := by rw [hK]; positivity
  rw [← ENNReal.ofReal_mul ht2, ← ENNReal.ofReal_mul h1, ← ENNReal.ofReal_mul h2,
    ← ENNReal.ofReal_mul h3, ← ENNReal.ofReal_mul hq, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hK, hs]
  exact freq_arith Co Cd a M t1 t2 A q hCo hCd ha hM ht1 ht2 hA hq

/-- The Fourier part of `SlabFourierBounds` for an explicit family `k` of densities: integrable
densities of the Fourier marginals, the decay bound, and the integrated height bound. -/
def SlabFourierBoundsFamily (d : ℕ) (C : ℝ → ℝ≥0) (c : ℝ) (M : ℝ≥0∞) (T : ℝ)
    (Γ : Measure (GreenCarrier d)) (k : PDE.Vec d → SlabBase d → ℂ) : Prop :=
  (∀ ξ, Integrable (k ξ) (slabBase d T) ∧
    ∀ E : Set (SlabBase d), MeasurableSet E →
      ∫ y in E, k ξ y ∂slabBase d T =
        ∫ p in {p : GreenCarrier d | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T},
          Complex.exp (-((PDE.vecDot ξ p.2.2 : ℝ) * Complex.I)) ∂Γ) ∧
  ∀ γ : ℝ, 1 ≤ γ → γ ≤ slabGamma0 d →
    (∀ ξ, eLpNorm (k ξ) (ENNReal.ofReal γ) (slabBase d T) ≤
      (C γ : ℝ≥0∞) * M * ENNReal.ofReal (T ^ slabBeta d γ) *
        ENNReal.ofReal (Real.exp (-(c * T * PDE.vecEuclideanNorm ξ ^ ((2 : ℝ) / 3))))) ∧
    ENNReal.ofReal (((2 * Real.pi) ^ d)⁻¹) *
        ∫⁻ ξ, eLpNorm (k ξ) (ENNReal.ofReal γ) (slabBase d T) ≤
      (C γ : ℝ≥0∞) * M * ENNReal.ofReal (T ^ (slabBeta d γ - 3 * (d : ℝ) / 2))

/-- For a jointly Borel family, `ξ ↦ ‖k^ξ‖_{L^γ}` is Borel (`#frequency-integral`). -/
theorem measurable_eLpNorm_family {d : ℕ} {α : Type*} [MeasurableSpace α] (m : Measure α)
    [SFinite m]
    (k : PDE.Vec d → α → ℂ) (hk : Measurable (Function.uncurry k)) {γ : ℝ} (hγ : 1 ≤ γ) :
    Measurable (fun ξ => eLpNorm (k ξ) (ENNReal.ofReal γ) m) := by
  have hγ0 : 0 < γ := by linarith
  have h1 : ∀ ξ, eLpNorm (k ξ) (ENNReal.ofReal γ) m =
      (∫⁻ y, ‖k ξ y‖ₑ ^ γ ∂m) ^ (1 / γ) := by
    intro ξ
    have hξ : Measurable (k ξ) := hk.comp (measurable_const.prodMk measurable_id)
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hγ0) ENNReal.ofReal_ne_top
      hξ.aestronglyMeasurable, ENNReal.toReal_ofReal hγ0.le]
  simp_rw [h1]
  have h2 : Measurable (fun x : PDE.Vec d × α => ‖k x.1 x.2‖ₑ ^ γ) :=
    (hk.enorm).pow_const γ
  exact (h2.lintegral_prod_right').pow_const _

/-- **Lemma 5.1.**  For a jointly Borel family of Fourier densities
obeying the decay bound, the frequency integral of the `L^γ` norms is measurable and obeys the
height bound `(2π)^{-d} ∫ ‖k^ξ‖_{L^γ} dξ ≤ C_γ M T^{β_γ - 3d/2}`. -/
theorem slab_frequency_integral {d : ℕ} {C : ℝ → ℝ≥0} {c : ℝ} {M : ℝ≥0∞} {T : ℝ}
    {Γ : Measure (GreenCarrier d)} {k : PDE.Vec d → SlabBase d → ℂ}
    (hk : Measurable (Function.uncurry k)) (hf : SlabFourierBoundsFamily d C c M T Γ k) :
    ∀ γ : ℝ, 1 ≤ γ → γ ≤ slabGamma0 d →
      Measurable (fun ξ => eLpNorm (k ξ) (ENNReal.ofReal γ) (slabBase d T)) ∧
        ENNReal.ofReal (((2 * Real.pi) ^ d)⁻¹) *
            ∫⁻ ξ, eLpNorm (k ξ) (ENNReal.ofReal γ) (slabBase d T) ≤
          (C γ : ℝ≥0∞) * M * ENNReal.ofReal (T ^ (slabBeta d γ - 3 * (d : ℝ) / 2)) :=
  fun γ h1 h2 => ⟨measurable_eLpNorm_family _ k hk h1, (hf.2 γ h1 h2).2⟩

/-- **Lemma 5.1 for one realized kernel**, conditional on the occupation and decay
estimates for that kernel (constants `Cocc`, `Cdec`, `cdec`).  The Fourier densities can be taken
jointly Borel in `(ξ, y)`, so that `ξ ↦ ‖k^ξ‖_{L^γ}` is measurable. -/
theorem slabFourierBounds_meas_of_occupation_decay_kernel {d : ℕ} (hd : 0 < d)
    (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
    (hcov : IsTranslationCovariantEvolution (wholeSpace d) (fun _ => 0) MeasurableSet.univ K)
    (hcomp : K.HasComposition MeasurableSet.univ)
    (Cocc : ℝ → ℝ) (hocc : OccupationBoundedBy K Cocc)
    (Cdec cdec : ℝ) (hCdec : 0 < Cdec) (hcdec : 0 < cdec) (hdec : FourierDecayBoundedBy K Cdec cdec)
    (σ₀ : ℝ) (μ : Measure (EvolutionState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) σ₀))
    [IsFiniteMeasure μ] (Γ : Measure (GreenCarrier d)) (hΓ : IsGreenMeasure K σ₀ ⊤ μ Γ)
    {T : ℝ} (hT : 0 < T) :
    SlabFourierBounds d (slabConstant' d Cocc Cdec cdec) (cdec / 2) (μ univ) T Γ ∧
      ∃ k : PDE.Vec d → SlabBase d → ℂ, Measurable (Function.uncurry k) ∧
        SlabFourierBoundsFamily d (slabConstant' d Cocc Cdec cdec) (cdec / 2) (μ univ) T Γ k := by
  obtain ⟨g, hgm, hgE, hgnorm⟩ := slab_marginal_density hd K hcov Cocc hocc σ₀ μ Γ hΓ hT
  have hΓfin : IsFiniteMeasure (Γ.restrict (slabSet (d := d) T)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact (green_slab_le K σ₀ μ Γ hΓ hT).trans_lt
      (ENNReal.mul_lt_top (measure_lt_top _ _) ENNReal.ofReal_lt_top)
  obtain ⟨kf, hkm, hkf⟩ := exists_measurable_fourier_family hd hT Γ g hgE
  have hk : ∀ (ξ : PDE.Vec d) (γ : ℝ), 1 ≤ γ → γ ≤ slabGamma0 d →
      eLpNorm (kf ξ) (ENNReal.ofReal γ) (slabBase d T) ≤
        ENNReal.ofReal (Cocc γ * Cdec * (2 : ℝ) ^ slabBeta d γ) * μ univ *
          ENNReal.ofReal (T ^ slabBeta d γ) *
          ENNReal.ofReal (Real.exp
            (-((cdec / 2) * T * PDE.vecEuclideanNorm ξ ^ ((2 : ℝ) / 3)))) :=
    fun ξ => slab_fourier_density_bound K hd hcov hcomp Cocc hocc Cdec cdec hCdec hdec σ₀ μ Γ hΓ
      hT ξ (kf ξ) (hkf ξ).1 (hkf ξ).2
  have hCγ : ∀ γ : ℝ, 1 ≤ γ → γ ≤ slabGamma0 d →
      (slabConstant' d Cocc Cdec cdec γ : ℝ≥0∞) = ENNReal.ofReal (Cocc γ * slabK1 d Cdec cdec γ) :=
    fun _ _ _ => rfl
  have hfin : ∫⁻ ζ, decayProfile d (cdec / 2) ζ < ⊤ :=
    lintegral_decayProfile_lt_top hd (by linarith)
  have hAeq : ∫⁻ ζ, decayProfile d (cdec / 2) ζ = ENNReal.ofReal (slabFreqConstant d (cdec / 2)) :=
    (ENNReal.ofReal_toReal hfin.ne).symm
  have hA0 : 0 ≤ slabFreqConstant d (cdec / 2) := ENNReal.toReal_nonneg
  set M : ℝ := (μ univ).toReal with hMdef
  have hM : μ univ = ENNReal.ofReal M := (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
  have hq0 : (0 : ℝ) ≤ ((2 * Real.pi) ^ d)⁻¹ := by positivity
  have hF1 := one_le_slabK1_factor (d := d) hCdec cdec
  have hF2 : Cdec ≤ (1 + Cdec) * (1 + ((2 * Real.pi) ^ d)⁻¹ * slabFreqConstant d (cdec / 2)) := by
    nlinarith [mul_nonneg hq0 hA0]
  have hK1 : ∀ γ : ℝ, slabK1 d Cdec cdec γ =
      (2 : ℝ) ^ slabBeta d γ * ((1 + Cdec) *
        (1 + ((2 * Real.pi) ^ d)⁻¹ * slabFreqConstant d (cdec / 2))) := fun γ => by
    unfold slabK1; ring
  have hfam : SlabFourierBoundsFamily d (slabConstant' d Cocc Cdec cdec) (cdec / 2) (μ univ) T Γ
      kf := by
    refine ⟨fun ξ => ⟨(hkf ξ).1, (hkf ξ).2⟩, fun γ h1 h2 => ⟨fun ξ => ?_, ?_⟩⟩
    · have hC0 : 0 ≤ Cocc γ := hocc.1 γ h1 h2
      have h2b := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (slabBeta d γ)
      refine (hk ξ γ h1 h2).trans ?_
      rw [hCγ γ h1 h2]
      have hle : ENNReal.ofReal (Cocc γ * Cdec * (2 : ℝ) ^ slabBeta d γ) ≤
          ENNReal.ofReal (Cocc γ * slabK1 d Cdec cdec γ) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hK1]
        nlinarith [mul_nonneg hC0 h2b, mul_nonneg hC0 hCdec.le]
      exact mul_le_mul' (mul_le_mul' (mul_le_mul' hle le_rfl) le_rfl) le_rfl
    · have hC0 : 0 ≤ Cocc γ := hocc.1 γ h1 h2
      have h2b := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (slabBeta d γ)
      have ht1 : 0 ≤ T ^ slabBeta d γ := Real.rpow_nonneg hT.le _
      have ht2 : 0 ≤ T ^ (-(3 * (d : ℝ) / 2)) := Real.rpow_nonneg hT.le _
      set D : ℝ≥0∞ := ENNReal.ofReal (Cocc γ * Cdec * (2 : ℝ) ^ slabBeta d γ) * μ univ *
        ENNReal.ofReal (T ^ slabBeta d γ) with hD
      have hDtop : D ≠ ⊤ := by
        rw [hD]
        exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
          ENNReal.ofReal_ne_top
      have hscale := lintegral_decayProfile_scaling d (cdec / 2) T hT
      calc ENNReal.ofReal (((2 * Real.pi) ^ d)⁻¹) *
            ∫⁻ ξ, eLpNorm (kf ξ) (ENNReal.ofReal γ) (slabBase d T)
          ≤ ENNReal.ofReal (((2 * Real.pi) ^ d)⁻¹) *
            ∫⁻ ξ : PDE.Vec d, D * ENNReal.ofReal (Real.exp
              (-((cdec / 2) * T * PDE.vecEuclideanNorm ξ ^ ((2 : ℝ) / 3)))) :=
            mul_le_mul' le_rfl (lintegral_mono (fun ξ => hk ξ γ h1 h2))
        _ = ENNReal.ofReal (((2 * Real.pi) ^ d)⁻¹) *
            (D * (ENNReal.ofReal (T ^ (-(3 * (d : ℝ) / 2))) *
              ENNReal.ofReal (slabFreqConstant d (cdec / 2)))) := by
            rw [lintegral_const_mul' D _ hDtop, hscale, hAeq]
        _ ≤ _ := by
            rw [hCγ γ h1 h2, hD, hM]
            have hrp : T ^ (slabBeta d γ - 3 * (d : ℝ) / 2) =
                T ^ slabBeta d γ * T ^ (-(3 * (d : ℝ) / 2)) := by
              rw [← Real.rpow_add hT, sub_eq_add_neg]
            rw [hrp]
            exact freq_ennreal (Cocc γ) Cdec ((2 : ℝ) ^ slabBeta d γ) M (T ^ slabBeta d γ)
              (T ^ (-(3 * (d : ℝ) / 2))) (slabFreqConstant d (cdec / 2)) (((2 * Real.pi) ^ d)⁻¹)
              (slabK1 d Cdec cdec γ) _ hC0 hCdec.le h2b hM0 ht1 ht2 hA0 hq0
              (by unfold slabK1; ring) rfl
  refine ⟨⟨⟨g, hgm.aemeasurable, hgE, fun γ h1 h2 => ?_⟩, kf, hfam⟩, kf, hkm, hfam⟩
  · have hC0 : 0 ≤ Cocc γ := hocc.1 γ h1 h2
    have h2b := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (slabBeta d γ)
    refine (hgnorm γ h1 h2).trans ?_
    rw [hCγ γ h1 h2]
    have hle : ENNReal.ofReal (Cocc γ * (2 : ℝ) ^ slabBeta d γ) ≤
        ENNReal.ofReal (Cocc γ * slabK1 d Cdec cdec γ) := by
      refine ENNReal.ofReal_le_ofReal ?_
      rw [hK1]
      nlinarith [mul_nonneg hC0 h2b]
    exact mul_le_mul' (mul_le_mul' hle le_rfl) le_rfl

/-- **Lemma 5.1 for one realized kernel** (plain `SlabFourierBounds` form). -/
theorem slabFourierBounds_of_occupation_decay_kernel {d : ℕ} (hd : 0 < d)
    (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
    (hcov : IsTranslationCovariantEvolution (wholeSpace d) (fun _ => 0) MeasurableSet.univ K)
    (hcomp : K.HasComposition MeasurableSet.univ)
    (Cocc : ℝ → ℝ) (hocc : OccupationBoundedBy K Cocc)
    (Cdec cdec : ℝ) (hCdec : 0 < Cdec) (hcdec : 0 < cdec) (hdec : FourierDecayBoundedBy K Cdec cdec)
    (σ₀ : ℝ) (μ : Measure (EvolutionState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) σ₀))
    [IsFiniteMeasure μ] (Γ : Measure (GreenCarrier d)) (hΓ : IsGreenMeasure K σ₀ ⊤ μ Γ)
    {T : ℝ} (hT : 0 < T) :
    SlabFourierBounds d (slabConstant' d Cocc Cdec cdec) (cdec / 2) (μ univ) T Γ :=
  (slabFourierBounds_meas_of_occupation_decay_kernel hd K hcov hcomp Cocc hocc Cdec cdec hCdec
    hcdec hdec σ₀ μ Γ hΓ hT).1

/-- **Lemma 5.1 (case W), family level.**  Conditional on the conclusions of Proposition 4.2
(`ParabolicOccupationFamily`) and Proposition 3.1 (`FourierDecayFamily`) for the coefficient bounds
`λ, Λ`: there are constants `C_γ, c` (depending only on `d` and the constants of the two premises)
such that for every Section 2 coefficient `B` with these bounds, every realizing evolution `(S, K)`
of `(B, id)`, every `σ₀`, finite `μ`, Green measure `Γ` of `μ` (infinite horizon) and `T > 0`,
`SlabFourierBounds d C c (μ univ) T Γ` holds, with Fourier densities `k^ξ` that are jointly Borel
in `(ξ, y)` (so `ξ ↦ ‖k^ξ‖_{L^γ}` is measurable, see `measurable_eLpNorm_family`).  The translation
covariance and composition clauses needed by the proof are derived from the realization
(`isTranslationCovariant_of_realizes`). -/
theorem slabFourierBounds_meas_of_occupation_decay {d : ℕ} (hd : 1 ≤ d) (lam Lam : ℝ)
    (hocc : ParabolicOccupationFamily d lam Lam) (hdec : FourierDecayFamily d lam Lam) :
    ∃ (C : ℝ → ℝ≥0) (c : ℝ), ∀ (B : CoefficientField d),
      IsSectionTwoCoefficient lam Lam B →
      ∀ (S : TerminalOperatorFamily (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
        (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d))),
      RealizesTerminalEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d)) MeasurableSet.univ
        (zIndependentCoefficient B) (identityDrift d) S K →
      ∀ (σ₀ : ℝ) (μ : Measure (EvolutionState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) σ₀))
        [IsFiniteMeasure μ] (Γ : Measure (GreenCarrier d)), IsGreenMeasure K σ₀ ⊤ μ Γ →
      ∀ T : ℝ, 0 < T → SlabFourierBounds d C c (μ univ) T Γ ∧
        ∃ k : PDE.Vec d → SlabBase d → ℂ, Measurable (Function.uncurry k) ∧
          SlabFourierBoundsFamily d C c (μ univ) T Γ k := by
  obtain ⟨Cocc, hoc⟩ := hocc
  obtain ⟨Cdec, cdec, hCdec, hcdec, hdc⟩ := hdec
  refine ⟨slabConstant' d Cocc Cdec cdec, cdec / 2, fun B hB S K hreal σ₀ μ _ Γ hΓ T hT => ?_⟩
  exact slabFourierBounds_meas_of_occupation_decay_kernel (Nat.pos_of_ne_zero (by omega)) K
    (isTranslationCovariant_of_realizes B S K hreal) hreal.2.2.2 Cocc (hoc B hB S K hreal)
    Cdec cdec hCdec hcdec (hdc B hB S K hreal) σ₀ μ Γ hΓ hT

/-- **Lemma 5.1 (case W), family level, in the form consumed by Theorem 1.1.**  Exactly the
conclusion of `slabFourierBounds_meas_of_occupation_decay` without the measurability clause: the
`hbounds` premise of `Green.green_density_of_slab_marginals` and of
`TheoremA.green_density_bound_of_slabFourierBounds`. -/
theorem slabFourierBounds_of_occupation_decay {d : ℕ} (hd : 1 ≤ d) (lam Lam : ℝ)
    (hocc : ParabolicOccupationFamily d lam Lam) (hdec : FourierDecayFamily d lam Lam) :
    ∃ (C : ℝ → ℝ≥0) (c : ℝ), ∀ (B : CoefficientField d),
      IsSectionTwoCoefficient lam Lam B →
      ∀ (S : TerminalOperatorFamily (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
        (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d))),
      RealizesTerminalEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d)) MeasurableSet.univ
        (zIndependentCoefficient B) (identityDrift d) S K →
      ∀ (σ₀ : ℝ) (μ : Measure (EvolutionState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) σ₀))
        [IsFiniteMeasure μ] (Γ : Measure (GreenCarrier d)), IsGreenMeasure K σ₀ ⊤ μ Γ →
      ∀ T : ℝ, 0 < T → SlabFourierBounds d C c (μ univ) T Γ := by
  obtain ⟨C, c, h⟩ := slabFourierBounds_meas_of_occupation_decay hd lam Lam hocc hdec
  exact ⟨C, c, fun B hB S K hreal σ₀ μ _ Γ hΓ T hT => (h B hB S K hreal σ₀ μ Γ hΓ T hT).1⟩

/-- **Theorem 2.4 (case W), conditional on Proposition 4.2 and Proposition 3.1 only.**  Feeding the
family headline to `green_density_of_slab_marginals`: the structural constants `C_γ, c` come first,
and for every realized evolution the finite-horizon Green measure has the stated `L^q` density
bound. -/
theorem green_density_of_occupation_decay {d : ℕ} (hd : 1 ≤ d) (lam Lam : ℝ)
    (hocc : ParabolicOccupationFamily d lam Lam) (hdec : FourierDecayFamily d lam Lam) :
    ∃ C : ℝ → ℝ≥0, ∀ (B : CoefficientField d), IsSectionTwoCoefficient lam Lam B →
      ∀ (S : TerminalOperatorFamily (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
        (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d))),
      RealizesTerminalEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d)) MeasurableSet.univ
        (zIndependentCoefficient B) (identityDrift d) S K →
      ∀ (σ₀ : ℝ) (μ : Measure (EvolutionState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) σ₀))
        [IsFiniteMeasure μ] (Γ : Measure (GreenCarrier d)), IsGreenMeasure K σ₀ ⊤ μ Γ →
      ∀ {q S' : ℝ}, 1 < q → q < 1 + 1 / (2 * (d : ℝ)) → 0 < S' →
      ∀ ΓS : Measure (ElapsedTime (ENNReal.ofReal S') × EvolutionAmbientState d),
        IsGreenMeasure K σ₀ (ENNReal.ofReal S') μ ΓS →
      ∃ G : ElapsedTime (ENNReal.ofReal S') × EvolutionAmbientState d → ℝ≥0∞, Measurable G ∧
        ΓS = ((elapsedVolume (ENNReal.ofReal S')).prod
          (volume : Measure (EvolutionAmbientState d))).withDensity G ∧
        eLpNorm G (ENNReal.ofReal q) ((elapsedVolume (ENNReal.ofReal S')).prod
          (volume : Measure (EvolutionAmbientState d))) ≤
          (greenConstant d q C : ℝ≥0∞) * μ univ *
            ENNReal.ofReal (S' ^ (greenDelta d q / q)) := by
  obtain ⟨C, c, hb⟩ := slabFourierBounds_of_occupation_decay hd lam Lam hocc hdec
  refine ⟨C, fun B hB S K hreal σ₀ μ _ Γ hΓ q S' hq hqd hS ΓS hΓS => ?_⟩
  exact green_density_of_slab_marginals C c K σ₀ μ Γ hΓ
    (fun T hT => hb B hB S K hreal σ₀ μ Γ hΓ T hT) hq hqd hS ΓS hΓS

end HypoellipticAleksandrov.KineticAleksandrov.Green
