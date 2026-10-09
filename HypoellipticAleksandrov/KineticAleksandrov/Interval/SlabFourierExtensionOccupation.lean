module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.SlabFourierExtensionMarginal

/-! # Occupation estimates on the zero-extension carrier

Ambient initial measures are pulled back to the interval subtype. The constructed
interval density is extended by zero, preserving every occupation norm bound.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open Set MeasureTheory HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Decay
open HypoellipticAleksandrov.KineticAleksandrov.Green
open scoped ENNReal

/-- The proved interval occupation constants also bound its zero-extension carrier. -/
theorem intervalExtension_occupation
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam) :
    ∃ C : ℝ → ℝ,
    ∀ (m Lb : ℝ), 0 < m → m ≤ Lb →
    ∀ (a c : ℝ) (_hac : a < c) (B : CoefficientField 1) (b : PDE.Vec 1 → PDE.Vec 1),
    SourceSetting lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b →
    ∀ (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
      (S : TerminalOperatorFamily (PDE.oneDimensionalAxisBox a c) stationary)
      (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary),
    RealizesTerminalEvolution (PDE.oneDimensionalAxisBox a c) stationary hJ
      (zIndependentCoefficient B) b S K → OccupationBoundedBy (intervalExtension hJ K) C := by
  obtain ⟨C, hC, hocc⟩ := interval_occupation hH hLE lam Lam hlam hlamLam
  refine ⟨C, ?_⟩
  intro m Lb hm hmLb a c hac B b hs hJ S K hr
  refine ⟨fun γ hγ1 hγ2 => hC γ hγ1 (by norm_num [slabGamma0] at hγ2; exact hγ2), ?_⟩
  intro ρ _ σ T hT
  let ρj : Measure (PDE.oneDimensionalAxisBox a c) := Measure.comap Subtype.val ρ
  have hρj : ρj univ ≤ ρ univ := intervalInitial_comap_mass_le hJ ρ
  have : IsFiniteMeasure ρj := ⟨hρj.trans_lt (measure_lt_top ρ univ)⟩
  obtain ⟨g, hgm, hg0, hchar, hb⟩ :=
    hocc m Lb hm hmLb a c hac B b hs hJ S K hr σ T hT ρj
  have hp := (interval_evolution_clauses hH hLE hac B b hs hJ S K hr).2.1
  let U : Set (TimeVelocity 1) := Ioo 0 T ×ˢ PDE.oneDimensionalAxisBox a c
  let gw := U.indicator g
  have hU : MeasurableSet U := measurableSet_Ioo.prod hJ
  have hUR : U ⊆ Ioo (0 : ℝ) T ×ˢ univ := prod_mono Subset.rfl (subset_univ _)
  have hgw : Measurable gw := hgm.indicator hU
  have hgw0 : ∀ p, 0 ≤ gw p := fun p => by
    by_cases hp : p ∈ U
    · simpa only [gw, indicator_of_mem hp] using hg0 p
    · simp only [gw, indicator_of_notMem hp, le_refl]
  refine ⟨gw, ⟨hgw, hgw0, ?_⟩, ?_⟩
  · intro φ
    have hfun : (fun p => φ p * gw p) = U.indicator (fun p => φ p * g p) := by
      funext p
      by_cases hp : p ∈ U <;> simp [gw, hp]
    rw [hfun, integral_indicator hU, Measure.restrict_restrict_of_subset hUR, hchar φ]
    let F : PDE.Vec 1 → ℝ := fun v =>
      ∫ t : ElapsedTime (ENNReal.ofReal T), ∫ w, φ (t.1, w)
        ∂(intervalExtension hJ K).firstMarginal
          (wholeSpaceQuery σ (σ + t.1) (le_add_of_nonneg_right t.2.1.le) v 0)
        ∂elapsedVolume (ENNReal.ofReal T)
    have hFzero : ∀ v, v ∉ PDE.oneDimensionalAxisBox a c → F v = 0 := by
      intro v hv
      dsimp only [F]
      simp_rw [intervalExtension_first_outside hJ K σ _ _ v hv]
      simp only [integral_zero_measure, integral_zero]
    change _ = ∫ v, F v ∂ρ
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hFzero,
      ← integral_subtype_comap hJ F]
    apply integral_congr_ae
    refine Filter.Eventually.of_forall fun v => ?_
    dsimp only [F]
    apply integral_congr_ae
    refine Filter.Eventually.of_forall fun t => ?_
    dsimp only
    rw [intervalExtension_first_inside,
      interval_firstMarginal_eq_parabolic hJ K B hp]
  · intro γ hγ1 hγ2
    have hγ2' : γ ≤ 2 := by norm_num [slabGamma0] at hγ2; exact hγ2
    obtain ⟨hgLp, hgBound⟩ := hb γ hγ1 hγ2'
    have hnorm : eLpNorm gw (ENNReal.ofReal γ)
        (volume.restrict (Ioo (0 : ℝ) T ×ˢ univ)) =
        eLpNorm g (ENNReal.ofReal γ) (volume.restrict U) := by
      dsimp only [gw]
      rw [eLpNorm_indicator_eq_eLpNorm_restrict hU,
        Measure.restrict_restrict_of_subset hUR]
    have hgwLp : MemLp gw (ENNReal.ofReal γ)
        (volume.restrict (Ioo (0 : ℝ) T ×ˢ univ)) := by
      change eLpNorm gw _ _ < ⊤
      rw [hnorm]
      exact hgLp.eLpNorm_lt_top
    refine ⟨hgwLp, ?_⟩
    have hbd : eLpNorm gw (ENNReal.ofReal γ)
        (volume.restrict (Ioo (0 : ℝ) T ×ˢ univ)) ≤
        ENNReal.ofReal (C γ * (ρ univ).toReal * T ^ slabBeta 1 γ) := by
      rw [hnorm]
      have hB := hgBound.trans (mul_le_mul'
        (mul_le_mul' le_rfl hρj) le_rfl)
      have hβ : slabBeta 1 γ = 3 / (2 * γ) - 1 / 2 := by
        norm_num [slabBeta]
      rw [hβ, ENNReal.ofReal_mul (mul_nonneg (hC γ hγ1 hγ2') ENNReal.toReal_nonneg),
        ENNReal.ofReal_mul (hC γ hγ1 hγ2'),
        ENNReal.ofReal_toReal (measure_ne_top ρ univ)]
      exact hB
    have hpos : 0 ≤ C γ * (ρ univ).toReal * T ^ slabBeta 1 γ :=
      mul_nonneg (mul_nonneg (hC γ hγ1 hγ2') ENNReal.toReal_nonneg)
        (Real.rpow_nonneg hT.le _)
    simpa only [ENNReal.toReal_ofReal hpos] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hbd

end HypoellipticAleksandrov.KineticAleksandrov.Interval
