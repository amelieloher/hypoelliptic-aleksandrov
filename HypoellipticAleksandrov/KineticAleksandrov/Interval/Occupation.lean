module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.OccupationTransfer
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.Occupation

/-! # The bounded-interval occupation theorem

The scalar maximum principle dominates killed interval transitions by the
whole-space scalar evolution. Its proved occupation density supplies all exponents;
Radon–Nikodym domination retains a common density and the same structural constants.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open Set MeasureTheory HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Decay
open HypoellipticAleksandrov.KineticAleksandrov.Occupation
open scoped ENNReal

/-- Interval occupation has a common density with constants independent of interval length. -/
theorem interval_occupation
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam) :
    ∃ C : ℝ → ℝ, (∀ γ : ℝ, 1 ≤ γ → γ ≤ 2 → 0 ≤ C γ) ∧
    ∀ (m Lb : ℝ), 0 < m → m ≤ Lb →
    ∀ (a c : ℝ) (_hac : a < c) (B : CoefficientField 1) (b : PDE.Vec 1 → PDE.Vec 1),
    SourceSetting lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b →
    ∀ (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
      (S : TerminalOperatorFamily (PDE.oneDimensionalAxisBox a c) stationary)
      (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary),
    RealizesTerminalEvolution (PDE.oneDimensionalAxisBox a c) stationary hJ
      (zIndependentCoefficient B) b S K →
    ∀ (σ T : ℝ), 0 < T →
    ∀ (ρ : Measure (PDE.oneDimensionalAxisBox a c)) [IsFiniteMeasure ρ],
    ∃ g : TimeVelocity 1 → ℝ, Measurable g ∧ (∀ p, 0 ≤ g p) ∧
      (∀ φ : BoundedBorel (TimeVelocity 1),
        (∫ p, φ p * g p ∂volume.restrict (Ioo 0 T ×ˢ PDE.oneDimensionalAxisBox a c)) =
        ∫ v, ∫ t : ElapsedTime (ENNReal.ofReal T), ∫ w, φ (t.1, w)
          ∂P K hJ (scalarQuery σ (σ + t.1) (le_add_of_nonneg_right t.2.1.le) v.1
            (by simpa only [movingDomain_stationary] using v.2))
          ∂elapsedVolume (ENNReal.ofReal T) ∂ρ) ∧
      ∀ γ : ℝ, 1 ≤ γ → γ ≤ 2 →
        MemLp g (ENNReal.ofReal γ)
          (volume.restrict (Ioo 0 T ×ˢ PDE.oneDimensionalAxisBox a c)) ∧
        eLpNorm g (ENNReal.ofReal γ)
          (volume.restrict (Ioo 0 T ×ˢ PDE.oneDimensionalAxisBox a c)) ≤
          ENNReal.ofReal (C γ) * ρ univ * ENNReal.ofReal (T ^ (3 / (2 * γ) - 1 / 2)) := by
  obtain ⟨C, hC, hocc⟩ := occupation hH (d := 1) (by norm_num)
    lam Lam hlam hlamLam
  refine ⟨C, fun γ hγ1 hγ2 => hC γ hγ1 (by norm_num; exact hγ2), ?_⟩
  intro m Lb _hm _hmLb a c hac B b hs hJ S K hr σ T hT ρ _
  have hp := (interval_evolution_clauses hH hLE hac B b hs hJ S K hr).2.1
  have hsetting : SourceSetting lam Lam 1 1 (univ : Set (PDE.Vec 1)) B (identityDrift 1) :=
    ⟨hs.1, identityDrift_smooth 1, zero_lt_one, le_rfl, identityDrift_bounds 1,
      Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩
  obtain ⟨Sw, Kw, hrw, _, hpw, _⟩ :=
    exists_unitBlock_evolution (exists_terminalEvolution_of_classical hLE hH)
      (by norm_num) lam Lam 1 1 univ B (identityDrift 1) hsetting
      (wholeSpace 1) (fun _ => 0) (wholeSpace_admissible 1) (zeroCurve_piecewiseC1 1)
  obtain ⟨gw, hgw, hgwLp⟩ := hocc B hs.1 Sw Kw hrw hpw (ρ.map Subtype.val) σ T hT
  have hgwi : Integrable gw (volume.restrict (Ioo (0 : ℝ) T ×ˢ univ)) :=
    memLp_one_iff_integrable.1 (by simpa using (hgwLp 1 le_rfl (by norm_num)).1)
  have hgwSlab : Green.SlabOccupationDensity Kw σ T (ρ.map Subtype.val) gw :=
    (isOccupationDensity_iff_slabOccupationDensity Kw σ T (ρ.map Subtype.val) gw).mp hgw
  have hdom := intervalOccupationMeasure_le_density hac B hs.1 hJ K hp Kw hpw
    σ T hT ρ gw hgwSlab hgwi
  let U : Set (TimeVelocity 1) := Ioo 0 T ×ˢ PDE.oneDimensionalAxisBox a c
  have hU : MeasurableSet U := measurableSet_Ioo.prod hJ
  have hνU : (intervalOccupationMeasure σ T K ρ).restrict U =
      intervalOccupationMeasure σ T K ρ :=
    Measure.restrict_eq_self_of_ae_mem (by
      rw [ae_iff]; exact intervalOccupationMeasure_compl_region σ T hT hJ K ρ)
  have hdomU : intervalOccupationMeasure σ T K ρ ≤
      (volume.restrict U).withDensity (fun p => ENNReal.ofReal (gw p)) := by
    have h := Measure.restrict_mono_measure hdom U
    rw [hνU, restrict_withDensity hU, Measure.restrict_restrict_of_subset
      (show U ⊆ Ioo (0 : ℝ) T ×ˢ univ from prod_mono Subset.rfl (subset_univ _))] at h
    exact h
  have := intervalOccupationMeasure_finite σ T hT K ρ
  obtain ⟨g, hgm, hg0, _hgi, hgle, hpair⟩ := exists_real_density_of_le_withDensity
    (volume.restrict U) (intervalOccupationMeasure σ T K ρ) gw hgw.1 hgw.2.1 hdomU
  refine ⟨g, hgm, hg0, ?_, ?_⟩
  · intro φ
    rw [hpair φ]
    obtain ⟨M, _, hM⟩ := φ.exists_bound
    rw [integral_intervalOccupationMeasure σ T hT K ρ φ φ.measurable ⟨M, hM⟩]
    apply integral_congr_ae
    refine Filter.Eventually.of_forall fun v => ?_
    apply integral_congr_ae
    refine Filter.Eventually.of_forall fun t => ?_
    dsimp only
    rw [interval_firstMarginal_eq_parabolic hJ K B hp σ (σ + t.1)
      (le_add_of_nonneg_right t.2.1.le) v.1 0]
  · intro γ hγ1 hγ2
    have hw := hgwLp γ hγ1 (by norm_num; exact hγ2)
    have hmeasure : volume.restrict U ≤ volume.restrict (Ioo (0 : ℝ) T ×ˢ univ) :=
      Measure.restrict_mono_set _ (prod_mono Subset.rfl (subset_univ _))
    have hgwU := hw.1.mono_measure hmeasure
    have hnorm : ∀ᵐ p ∂volume.restrict U, ‖g p‖ ≤ ‖gw p‖ := by
      filter_upwards [hgle] with p hp
      simpa only [Real.norm_of_nonneg (hg0 p), Real.norm_of_nonneg (hgw.2.1 p)] using hp
    have hgLp := hgwU.mono hgm.aestronglyMeasurable hnorm
    refine ⟨hgLp, ?_⟩
    have hle : eLpNorm g (ENNReal.ofReal γ) (volume.restrict U) ≤
        eLpNorm gw (ENNReal.ofReal γ) (volume.restrict (Ioo (0 : ℝ) T ×ˢ univ)) :=
      (eLpNorm_mono_ae hgm.aestronglyMeasurable hnorm).trans
        (eLpNorm_mono_measure gw hmeasure)
    have hbound : eLpNorm gw (ENNReal.ofReal γ)
        (volume.restrict (Ioo (0 : ℝ) T ×ˢ univ)) ≤
        ENNReal.ofReal (C γ * (ρ univ).toReal * T ^ (3 / (2 * γ) - 1 / 2)) := by
      apply (ENNReal.toReal_le_toReal hw.1.eLpNorm_ne_top ENNReal.ofReal_ne_top).mp
      have hpos : 0 ≤ C γ * (ρ univ).toReal * T ^ (3 / (2 * γ) - 1 / 2) := by
        exact mul_nonneg (mul_nonneg (hC γ hγ1 (by norm_num; exact hγ2))
          ENNReal.toReal_nonneg) (Real.rpow_nonneg hT.le _)
      rw [ENNReal.toReal_ofReal hpos]
      have hm : (ρ.map Subtype.val) univ = ρ univ :=
        Measure.map_apply measurable_subtype_coe MeasurableSet.univ |>.trans (by
          rw [preimage_univ])
      simpa only [occupationLpNorm, occupationBeta, Nat.cast_one, hm,
        show (1 : ℝ) + 2 = 3 from by norm_num] using hw.2
    apply hle.trans
    convert hbound using 1
    rw [ENNReal.ofReal_mul (mul_nonneg (hC γ hγ1 (by norm_num; exact hγ2))
      ENNReal.toReal_nonneg), ENNReal.ofReal_mul (hC γ hγ1 (by norm_num; exact hγ2)),
      ENNReal.ofReal_toReal (measure_ne_top ρ univ)]

end HypoellipticAleksandrov.KineticAleksandrov.Interval
