module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientH10Commutator
public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientH10NonprincipalRemainder

/-!
# Exact H10 commutator split
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal RealInnerProductSpace Matrix.Norms.Elementwise

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

private theorem continuous_mul_of_tsupport_subset
    {X : Type*} [TopologicalSpace X] {U : Set X} {b q : X → ℝ}
    (hU : IsOpen U) (hb : ContinuousOn b U) (hbsupp : tsupport b ⊆ U)
    (hq : ContinuousOn q U) : Continuous fun x => b x * q x := by
  refine (hb.mul hq).continuous_of_tsupport_subset hU ?_
  exact (tsupport_mul_subset_left (f := b) (g := q)).trans hbsupp

private theorem reverseTimeMap_image_closedCylinder_subset
    {d : ℕ} {Ω : Set (PDE.Vec d)} (r₀ r₁ : ℝ) :
    reverseTimeMap r₁ '' (Set.Icc 0 (r₁ - r₀) ×ˢ closure Ω) ⊆
      scalarParabolicClosedCylinder r₀ r₁ Ω := by
  rintro w ⟨z, hz, rfl⟩
  rcases hz with ⟨hτ, hy⟩
  rw [mem_scalarParabolicClosedCylinder_iff]
  refine ⟨?_, ?_, hy⟩
  · simp only [reverseTimeMap_apply]
    linarith [hτ.2]
  · simp only [reverseTimeMap_apply]
    linarith [hτ.1]

private theorem reverseTime_coefficient_smoothOn_closedCylinder
    {d : ℕ} {Ω : Set (PDE.Vec d)} (r₀ r₁ : ℝ) (a : CoefficientField d)
    (ha : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) (i j : Fin d) :
    IsSmoothOnNeighborhood (fun z : TimeVelocity d => reverseTimeCoefficient r₁ a z.1 z.2 i j)
      (Set.Icc 0 (r₁ - r₀) ×ˢ closure Ω) := by
  change IsSmoothOnNeighborhood ((fun z : TimeVelocity d => a z.1 z.2 i j) ∘ reverseTimeMap r₁) _
  exact IsSmoothOnNeighborhood.reverseTime r₁
    (reverseTimeMap_image_closedCylinder_subset r₀ r₁)
    (IsSmoothOnNeighborhood.coefficientEntry a ha i j)

private theorem reverseTime_drift_smoothOn_closedCylinder
    {d : ℕ} {Ω : Set (PDE.Vec d)} (r₀ r₁ : ℝ) (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d)
    (ha : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hb : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) (j : Fin d) :
    IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => reverseTimeDivergenceDrift r₁ a b z.1 z.2 j)
      (Set.Icc 0 (r₁ - r₀) ×ˢ closure Ω) := by
  change IsSmoothOnNeighborhood ((fun z : TimeVelocity d =>
    scalarSpatialCoefficientDivergence a z j - b z.1 z.2 j) ∘ reverseTimeMap r₁) _
  exact IsSmoothOnNeighborhood.reverseTime r₁
    (reverseTimeMap_image_closedCylinder_subset r₀ r₁)
    (IsSmoothOnNeighborhood.divergenceDriftEntry a b ha hb j)

private theorem reverseTime_scalar_smoothOn_closedCylinder
    {d : ℕ} {Ω : Set (PDE.Vec d)} (r₀ r₁ : ℝ) (c : ℝ → PDE.Vec d → ℝ)
    (hc : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) :
    IsSmoothOnNeighborhood (fun z : TimeVelocity d => reverseTimeScalarCoefficient r₁ c z.1 z.2)
      (Set.Icc 0 (r₁ - r₀) ×ˢ closure Ω) := by
  change IsSmoothOnNeighborhood ((fun z : TimeVelocity d => c z.1 z.2) ∘ reverseTimeMap r₁) _
  exact IsSmoothOnNeighborhood.reverseTime r₁
    (reverseTimeMap_image_closedCylinder_subset r₀ r₁) hc

private theorem continuous_cutoff_spatialDifferenceQuotient_slice
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {K : ℝ}
    (r₀ r₁ τ : ℝ) (β : PDE.QuantitativeSmoothCutoff inner Ω K) (k : Fin d) (h : ℝ)
    (f : TimeVelocity d → ℝ)
    (hf : IsSmoothOnNeighborhood f (Set.Icc 0 (r₁ - r₀) ×ˢ closure Ω))
    (hτ : τ ∈ Set.Icc 0 (r₁ - r₀))
    (hβshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport β.toFun) Ω) :
    Continuous (fun y => β y * spatialDifferenceQuotient k h f (τ, y)) := by
  rcases hf with ⟨V, hVopen, hSV, hV⟩
  let g₀ : PDE.Vec d → TimeVelocity d := fun y => (τ, y)
  let g₁ : PDE.Vec d → TimeVelocity d := fun y => (τ, y + h • PDE.basisVec k)
  let U : Set (PDE.Vec d) := g₀ ⁻¹' V ∩ g₁ ⁻¹' V
  have hg₀ : Continuous g₀ := continuous_const.prodMk continuous_id
  have hg₁ : Continuous g₁ := continuous_const.prodMk (continuous_id.add continuous_const)
  have hU : IsOpen U := (hg₀.isOpen_preimage V hVopen).inter (hg₁.isOpen_preimage V hVopen)
  have hβU : tsupport β.toFun ⊆ U := by
    intro y hy
    exact ⟨hSV ⟨hτ, subset_closure (β.tsupport_subset hy)⟩,
      hSV ⟨hτ, subset_closure (hβshift hy)⟩⟩
  have hf₀ : ContinuousOn (fun y => f (τ, y)) U :=
    hV.continuousOn.comp hg₀.continuousOn fun y hy => hy.1
  have hf₁ : ContinuousOn (fun y => f (τ, y + h • PDE.basisVec k)) U :=
    hV.continuousOn.comp hg₁.continuousOn fun y hy => hy.2
  have hdq : ContinuousOn (fun y => spatialDifferenceQuotient k h f (τ, y)) U := by
    simpa only [spatialDifferenceQuotient_apply, spatialTranslate_apply, spatialShift_apply,
      Pi.sub_def]
      using (hf₁.sub hf₀).div_const h
  exact continuous_mul_of_tsupport_subset hU β.smooth.continuous.continuousOn hβU hdq

private theorem continuous_cutoff_spatialTranslate_slice
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {K : ℝ}
    (r₀ r₁ τ : ℝ) (β : PDE.QuantitativeSmoothCutoff inner Ω K) (k : Fin d) (h : ℝ)
    (f : TimeVelocity d → ℝ)
    (hf : IsSmoothOnNeighborhood f (Set.Icc 0 (r₁ - r₀) ×ˢ closure Ω))
    (hτ : τ ∈ Set.Icc 0 (r₁ - r₀))
    (hβshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport β.toFun) Ω) :
    Continuous (fun y => β y * spatialTranslate k h f (τ, y)) := by
  rcases hf with ⟨V, hVopen, hSV, hV⟩
  let g : PDE.Vec d → TimeVelocity d := fun y => (τ, y + h • PDE.basisVec k)
  let U : Set (PDE.Vec d) := g ⁻¹' V
  have hg : Continuous g := continuous_const.prodMk (continuous_id.add continuous_const)
  have hU : IsOpen U := hg.isOpen_preimage V hVopen
  have hβU : tsupport β.toFun ⊆ U := by
    intro y hy
    exact hSV ⟨hτ, subset_closure (hβshift hy)⟩
  have htranslate : ContinuousOn (fun y => spatialTranslate k h f (τ, y)) U := by
    simpa only [spatialTranslate_apply, spatialShift_apply, Function.comp_def, g, U,
      Set.preimage] using!
      hV.continuousOn.comp hg.continuousOn (fun y hy => hy)
  exact continuous_mul_of_tsupport_subset hU β.smooth.continuous.continuousOn hβU htranslate

private theorem integrable_weighted_scalarLp_pair
    {d : ℕ} {Ω : Set (PDE.Vec d)} (q : PDE.Vec d → ℝ) (hq : Continuous q)
    (hcompact : HasCompactSupport q) (f g : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    Integrable (fun y => q y * f y * g y) (PDE.volumeOn Ω) := by
  have hqVolume : MemLp q ∞ (volume : Measure (PDE.Vec d)) := hq.memLp_of_hasCompactSupport hcompact
  have hqTop : MemLp q ∞ (PDE.volumeOn Ω) := by simpa only [PDE.volumeOn] using hqVolume.restrict Ω
  have hfg := (Lp.memLp f).integrable_mul (Lp.memLp g)
  have hweighted := hfg.mul_of_top_right hqTop
  convert hweighted using 1
  ext y
  simp only [Pi.mul_apply]
  ring

private theorem integrable_weighted_scalarLp_pair_raw
    {d : ℕ} {Ω : Set (PDE.Vec d)} (q : PDE.Vec d → ℝ) (hq : Continuous q)
    (hcompact : HasCompactSupport q) (f g : PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (p r : PDE.Vec d → ℝ) (hf : ⇑f =ᵐ[PDE.volumeOn Ω] p)
    (hg : ⇑g =ᵐ[PDE.volumeOn Ω] r) :
    Integrable (fun y => (q y * p y) * r y) (PDE.volumeOn Ω) := by
  apply (integrable_weighted_scalarLp_pair q hq hcompact f g).congr
  filter_upwards [hf, hg] with y hyf hyg
  rw [hyf, hyg]

private theorem h10_E_coord_ae
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη : ℝ} (hΩ : IsOpen Ω)
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη) (k : Fin d) (h : ℝ)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) (u : H10HilbertGraph hΩ) (i : Fin d) :
    ⇑(PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
        (gradientCLM hΩ (localizedSpatialDifferenceQuotientH10CLM
          hΩ η k h η.tsupport_subset hηshift u)) -
      cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h
        (valueCLM hΩ u)) =ᵐ[PDE.volumeOn Ω]
      fun y => PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
          (gradientCLM hΩ (localizedSpatialDifferenceQuotientH10CLM
            hΩ η k h η.tsupport_subset hηshift u)) y -
        cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h
          (valueCLM hΩ u) y := by
  filter_upwards [MeasureTheory.Lp.coeFn_sub
    (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
      (gradientCLM hΩ (localizedSpatialDifferenceQuotientH10CLM
        hΩ η k h η.tsupport_subset hηshift u)))
    (cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h
      (valueCLM hΩ u))] with y hy
  rw [hy]
  rfl

private theorem h10_H_coord_ae
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη : ℝ} (hΩ : IsOpen Ω)
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη) (k : Fin d) (h : ℝ)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) (u : H10HilbertGraph hΩ) (i : Fin d) :
    ⇑(PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
        (gradientCLM hΩ (localizedSpatialDifferenceQuotientH10CLM
          hΩ η k h η.tsupport_subset hηshift u)) +
      cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h
        (valueCLM hΩ u)) =ᵐ[PDE.volumeOn Ω]
      fun y => PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
          (gradientCLM hΩ (localizedSpatialDifferenceQuotientH10CLM
            hΩ η k h η.tsupport_subset hηshift u)) y +
        cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h
          (valueCLM hΩ u) y := by
  filter_upwards [MeasureTheory.Lp.coeFn_add
    (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
      (gradientCLM hΩ (localizedSpatialDifferenceQuotientH10CLM
        hΩ η k h η.tsupport_subset hηshift u)))
    (cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h
      (valueCLM hΩ u))] with y hy
  rw [hy]
  rfl

private theorem h10_U_coord_ae
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη : ℝ} (hΩ : IsOpen Ω)
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη) (u : H10HilbertGraph hΩ) (j : Fin d) :
    ⇑(scalarL2Multiplier η.toFun (η.smooth.continuous.aestronglyMeasurable)
      1 zero_le_one (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (η.nonneg y)]
        exact η.le_one y)
      (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u))) =ᵐ[PDE.volumeOn Ω]
      fun y => η y * PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u) y := by
  exact scalarL2Multiplier_apply_ae η.toFun (η.smooth.continuous.aestronglyMeasurable)
    1 zero_le_one (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (η.nonneg y)]
      exact η.le_one y) _

private theorem h10_U0_ae
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη : ℝ} (hΩ : IsOpen Ω)
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη) (u : H10HilbertGraph hΩ) :
    ⇑(scalarL2Multiplier η.toFun (η.smooth.continuous.aestronglyMeasurable)
      1 zero_le_one (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (η.nonneg y)]
        exact η.le_one y) (valueCLM hΩ u)) =ᵐ[PDE.volumeOn Ω]
      fun y => η y * valueCLM hΩ u y := by
  exact scalarL2Multiplier_apply_ae η.toFun (η.smooth.continuous.aestronglyMeasurable)
    1 zero_le_one (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (η.nonneg y)]
      exact η.le_one y) _

private theorem integral_pair_add_const_mul
    {d : ℕ} {Ω : Set (PDE.Vec d)} (z : ℝ) (f g : PDE.Vec d → ℝ)
    (hf : Integrable f (PDE.volumeOn Ω)) (hg : Integrable g (PDE.volumeOn Ω)) :
    (∫ y in Ω, (z * f y) + (z * g y) ∂volume) =
      z * ((∫ y in Ω, f y ∂volume) + (∫ y in Ω, g y ∂volume)) := by
  rw [integral_add (hf.const_mul z) (hg.const_mul z), integral_const_mul,
    integral_const_mul]
  ring

private theorem finset_sum_const_mul
    {ι : Type*} [Fintype ι] (z : ℝ) (f : ι → ℝ) :
    (∑ i, z * f i) = z * ∑ i, f i := by rw [Finset.mul_sum]

private theorem finset_sum_sum_const_mul
    {ι κ : Type*} [Fintype ι] [Fintype κ] (z : ℝ) (f : ι → κ → ℝ) :
    (∑ i, ∑ j, z * f i j) = z * ∑ i, ∑ j, f i j := by
  calc
    _ = ∑ i, z * ∑ j, f i j := by
      apply Finset.sum_congr rfl
      intro i _
      exact finset_sum_const_mul z (f i)
    _ = _ := finset_sum_const_mul z fun i => ∑ j, f i j

private theorem raw_split_eight_real_ring
    (z s p ad dt dd gt gd : ℝ) :
    -z * s - (z * p + z * ad) - (z * dt + z * dd) + (z * gt + z * gd) =
      -(z * p) + z * (-s - ad - dt - dd + gt + gd) := by ring

section

variable {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη Kχ : ℝ}
variable (r₀ r₁ : ℝ) (hΩ : IsOpen Ω) (a : CoefficientField d)
variable (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
variable (ha : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
  (scalarParabolicClosedCylinder r₀ r₁ Ω))
variable (hb : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
  (scalarParabolicClosedCylinder r₀ r₁ Ω))
variable (hc : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
  (scalarParabolicClosedCylinder r₀ r₁ Ω))
variable (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
variable (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
variable (k : Fin d) (h τ : ℝ)
variable (hχshift : Set.MapsTo
  (fun y : PDE.Vec d => y + h • PDE.basisVec k) (tsupport χ.toFun) Ω)
variable (hηshift : Set.MapsTo
  (fun y : PDE.Vec d => y + h • PDE.basisVec k) (tsupport η.toFun) Ω)
variable (hτ : τ ∈ Set.Icc 0 (r₁ - r₀)) (u : H10HilbertGraph hΩ)

include r₀ ha hτ hχshift

private theorem integrable_aT_E_H (i j : Fin d) :
    Integrable (fun y =>
      (χ y * spatialTranslate k h
          (fun z => reverseTimeCoefficient r₁ a z.1 z.2 i j) (τ, y)) *
        (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
            (gradientCLM hΩ (localizedSpatialDifferenceQuotientH10CLM
              hΩ η k h η.tsupport_subset hηshift u)) y -
          cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η j k h
            (valueCLM hΩ u) y) *
        (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
            (gradientCLM hΩ (localizedSpatialDifferenceQuotientH10CLM
              hΩ η k h η.tsupport_subset hηshift u)) y +
          cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h
            (valueCLM hΩ u) y))
      (PDE.volumeOn Ω) := by
  let A := localizedSpatialDifferenceQuotientH10CLM
    hΩ η k h η.tsupport_subset hηshift
  let E : PDE.ScalarLp Ω (2 : ℝ≥0∞) :=
    PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ (A u)) -
      cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η j k h
        (valueCLM hΩ u)
  let H : PDE.ScalarLp Ω (2 : ℝ≥0∞) :=
    PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i (gradientCLM hΩ (A u)) +
      cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h
        (valueCLM hΩ u)
  let q : PDE.Vec d → ℝ := fun y => χ y * spatialTranslate k h
    (fun z => reverseTimeCoefficient r₁ a z.1 z.2 i j) (τ, y)
  have hq : Continuous q := by
    dsimp only [q]
    exact continuous_cutoff_spatialTranslate_slice r₀ r₁ τ χ k h _
      (reverseTime_coefficient_smoothOn_closedCylinder r₀ r₁ a ha i j) hτ hχshift
  have hcompact : HasCompactSupport q := by
    dsimp only [q]
    exact χ.hasCompactSupport.mul_right
  have hE : ⇑E =ᵐ[PDE.volumeOn Ω] fun y =>
      PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ (A u)) y -
        cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η j k h
          (valueCLM hΩ u) y := by
    dsimp only [E, A]
    exact h10_E_coord_ae hΩ η k h hηshift u j
  have hH : ⇑H =ᵐ[PDE.volumeOn Ω] fun y =>
      PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i (gradientCLM hΩ (A u)) y +
        cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h
          (valueCLM hΩ u) y := by
    dsimp only [H, A]
    exact h10_H_coord_ae hΩ η k h hηshift u i
  simpa only [q, A] using
    (integrable_weighted_scalarLp_pair_raw q hq hcompact E H _ _ hE hH)

private theorem integrable_aD_U_H (i j : Fin d) :
    Integrable (fun y =>
      (χ y * spatialDifferenceQuotient k h
          (fun z => reverseTimeCoefficient r₁ a z.1 z.2 i j) (τ, y)) *
        (η y * PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
          (gradientCLM hΩ u) y) *
        (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
            (gradientCLM hΩ (localizedSpatialDifferenceQuotientH10CLM
              hΩ η k h η.tsupport_subset hηshift u)) y +
          cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h
            (valueCLM hΩ u) y))
      (PDE.volumeOn Ω) := by
  let A := localizedSpatialDifferenceQuotientH10CLM
    hΩ η k h η.tsupport_subset hηshift
  let H : PDE.ScalarLp Ω (2 : ℝ≥0∞) :=
    PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i (gradientCLM hΩ (A u)) +
      cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h
        (valueCLM hΩ u)
  let ηMeas := η.smooth.continuous.aestronglyMeasurable (μ := PDE.volumeOn Ω)
  let ηBound : ∀ᵐ y ∂PDE.volumeOn Ω, ‖η y‖ ≤ (1 : ℝ) :=
    Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (η.nonneg y)]
      exact η.le_one y
  let U : PDE.ScalarLp Ω (2 : ℝ≥0∞) :=
    scalarL2Multiplier η.toFun ηMeas 1 zero_le_one ηBound
      (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u))
  let q : PDE.Vec d → ℝ := fun y => χ y * spatialDifferenceQuotient k h
    (fun z => reverseTimeCoefficient r₁ a z.1 z.2 i j) (τ, y)
  have hq : Continuous q := by
    dsimp only [q]
    exact continuous_cutoff_spatialDifferenceQuotient_slice r₀ r₁ τ χ k h _
      (reverseTime_coefficient_smoothOn_closedCylinder r₀ r₁ a ha i j) hτ hχshift
  have hcompact : HasCompactSupport q := by
    dsimp only [q]
    exact χ.hasCompactSupport.mul_right
  have hU : ⇑U =ᵐ[PDE.volumeOn Ω] fun y =>
      η y * PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u) y := by
    dsimp only [U]
    exact h10_U_coord_ae hΩ η u j
  have hH : ⇑H =ᵐ[PDE.volumeOn Ω] fun y =>
      PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i (gradientCLM hΩ (A u)) y +
        cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h
          (valueCLM hΩ u) y := by
    dsimp only [H, A]
    exact h10_H_coord_ae hΩ η k h hηshift u i
  simpa only [q, A] using
    (integrable_weighted_scalarLp_pair_raw q hq hcompact U H _ _ hU hH)

omit r₀ ha hτ hχshift

include r₀ ha hb hτ hχshift

private theorem integrable_driftT_E_V (j : Fin d) :
    Integrable (fun y =>
      (χ y * spatialTranslate k h
          (fun z => reverseTimeDivergenceDrift r₁ a b z.1 z.2 j) (τ, y)) *
        (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
            (gradientCLM hΩ (localizedSpatialDifferenceQuotientH10CLM
              hΩ η k h η.tsupport_subset hηshift u)) y -
          cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η j k h
            (valueCLM hΩ u) y) *
        valueCLM hΩ
          (localizedSpatialDifferenceQuotientH10CLM
            hΩ η k h η.tsupport_subset hηshift u) y)
      (PDE.volumeOn Ω) := by
  let A := localizedSpatialDifferenceQuotientH10CLM
    hΩ η k h η.tsupport_subset hηshift
  let E : PDE.ScalarLp Ω (2 : ℝ≥0∞) :=
    PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ (A u)) -
      cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η j k h
        (valueCLM hΩ u)
  let V : PDE.ScalarLp Ω (2 : ℝ≥0∞) := valueCLM hΩ (A u)
  let q : PDE.Vec d → ℝ := fun y => χ y * spatialTranslate k h
    (fun z => reverseTimeDivergenceDrift r₁ a b z.1 z.2 j) (τ, y)
  have hq : Continuous q := by
    dsimp only [q]
    exact continuous_cutoff_spatialTranslate_slice r₀ r₁ τ χ k h _
      (reverseTime_drift_smoothOn_closedCylinder r₀ r₁ a b ha hb j) hτ hχshift
  have hcompact : HasCompactSupport q := by
    dsimp only [q]
    exact χ.hasCompactSupport.mul_right
  have hE : ⇑E =ᵐ[PDE.volumeOn Ω] fun y =>
      PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ (A u)) y -
        cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η j k h
          (valueCLM hΩ u) y := by
    dsimp only [E, A]
    exact h10_E_coord_ae hΩ η k h hηshift u j
  have hV : ⇑V =ᵐ[PDE.volumeOn Ω] fun y => V y :=
    Filter.Eventually.of_forall fun _ => rfl
  simpa only [q, A, V] using
    (integrable_weighted_scalarLp_pair_raw q hq hcompact E V _ _ hE hV)

private theorem integrable_driftD_U_V (j : Fin d) :
    Integrable (fun y =>
      (χ y * spatialDifferenceQuotient k h
          (fun z => reverseTimeDivergenceDrift r₁ a b z.1 z.2 j) (τ, y)) *
        (η y * PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
          (gradientCLM hΩ u) y) *
        valueCLM hΩ
          (localizedSpatialDifferenceQuotientH10CLM
            hΩ η k h η.tsupport_subset hηshift u) y)
      (PDE.volumeOn Ω) := by
  let A := localizedSpatialDifferenceQuotientH10CLM
    hΩ η k h η.tsupport_subset hηshift
  let V : PDE.ScalarLp Ω (2 : ℝ≥0∞) := valueCLM hΩ (A u)
  let ηMeas := η.smooth.continuous.aestronglyMeasurable (μ := PDE.volumeOn Ω)
  let ηBound : ∀ᵐ y ∂PDE.volumeOn Ω, ‖η y‖ ≤ (1 : ℝ) :=
    Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (η.nonneg y)]
      exact η.le_one y
  let U : PDE.ScalarLp Ω (2 : ℝ≥0∞) :=
    scalarL2Multiplier η.toFun ηMeas 1 zero_le_one ηBound
      (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u))
  let q : PDE.Vec d → ℝ := fun y => χ y * spatialDifferenceQuotient k h
    (fun z => reverseTimeDivergenceDrift r₁ a b z.1 z.2 j) (τ, y)
  have hq : Continuous q := by
    dsimp only [q]
    exact continuous_cutoff_spatialDifferenceQuotient_slice r₀ r₁ τ χ k h _
      (reverseTime_drift_smoothOn_closedCylinder r₀ r₁ a b ha hb j) hτ hχshift
  have hcompact : HasCompactSupport q := by
    dsimp only [q]
    exact χ.hasCompactSupport.mul_right
  have hU : ⇑U =ᵐ[PDE.volumeOn Ω] fun y =>
      η y * PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u) y := by
    dsimp only [U]
    exact h10_U_coord_ae hΩ η u j
  have hV : ⇑V =ᵐ[PDE.volumeOn Ω] fun y => V y :=
    Filter.Eventually.of_forall fun _ => rfl
  simpa only [q, A, V] using
    (integrable_weighted_scalarLp_pair_raw q hq hcompact U V _ _ hU hV)

omit r₀ ha hb hτ hχshift

include r₀ hc hτ hχshift

private theorem integrable_gammaT_V_V :
    Integrable (fun y =>
      (χ y * spatialTranslate k h
          (fun z => reverseTimeScalarCoefficient r₁ c z.1 z.2) (τ, y)) *
        valueCLM hΩ
          (localizedSpatialDifferenceQuotientH10CLM
            hΩ η k h η.tsupport_subset hηshift u) y *
        valueCLM hΩ
          (localizedSpatialDifferenceQuotientH10CLM
            hΩ η k h η.tsupport_subset hηshift u) y)
      (PDE.volumeOn Ω) := by
  let A := localizedSpatialDifferenceQuotientH10CLM
    hΩ η k h η.tsupport_subset hηshift
  let V : PDE.ScalarLp Ω (2 : ℝ≥0∞) := valueCLM hΩ (A u)
  let q : PDE.Vec d → ℝ := fun y => χ y * spatialTranslate k h
    (fun z => reverseTimeScalarCoefficient r₁ c z.1 z.2) (τ, y)
  have hq : Continuous q := by
    dsimp only [q]
    exact continuous_cutoff_spatialTranslate_slice r₀ r₁ τ χ k h _
      (reverseTime_scalar_smoothOn_closedCylinder r₀ r₁ c hc) hτ hχshift
  have hcompact : HasCompactSupport q := by
    dsimp only [q]
    exact χ.hasCompactSupport.mul_right
  have hV : ⇑V =ᵐ[PDE.volumeOn Ω] fun y => V y :=
    Filter.Eventually.of_forall fun _ => rfl
  simpa only [q, A, V] using
    (integrable_weighted_scalarLp_pair_raw q hq hcompact V V _ _ hV hV)

private theorem integrable_gammaD_U0_V :
    Integrable (fun y =>
      (χ y * spatialDifferenceQuotient k h
          (fun z => reverseTimeScalarCoefficient r₁ c z.1 z.2) (τ, y)) *
        (η y * valueCLM hΩ u y) *
        valueCLM hΩ
          (localizedSpatialDifferenceQuotientH10CLM
            hΩ η k h η.tsupport_subset hηshift u) y)
      (PDE.volumeOn Ω) := by
  let A := localizedSpatialDifferenceQuotientH10CLM
    hΩ η k h η.tsupport_subset hηshift
  let V : PDE.ScalarLp Ω (2 : ℝ≥0∞) := valueCLM hΩ (A u)
  let ηMeas := η.smooth.continuous.aestronglyMeasurable (μ := PDE.volumeOn Ω)
  let ηBound : ∀ᵐ y ∂PDE.volumeOn Ω, ‖η y‖ ≤ (1 : ℝ) :=
    Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (η.nonneg y)]
      exact η.le_one y
  let U₀ : PDE.ScalarLp Ω (2 : ℝ≥0∞) :=
    scalarL2Multiplier η.toFun ηMeas 1 zero_le_one ηBound (valueCLM hΩ u)
  let q : PDE.Vec d → ℝ := fun y => χ y * spatialDifferenceQuotient k h
    (fun z => reverseTimeScalarCoefficient r₁ c z.1 z.2) (τ, y)
  have hq : Continuous q := by
    dsimp only [q]
    exact continuous_cutoff_spatialDifferenceQuotient_slice r₀ r₁ τ χ k h _
      (reverseTime_scalar_smoothOn_closedCylinder r₀ r₁ c hc) hτ hχshift
  have hcompact : HasCompactSupport q := by
    dsimp only [q]
    exact χ.hasCompactSupport.mul_right
  have hU₀ : ⇑U₀ =ᵐ[PDE.volumeOn Ω] fun y => η y * valueCLM hΩ u y := by
    dsimp only [U₀]
    exact h10_U0_ae hΩ η u
  have hV : ⇑V =ᵐ[PDE.volumeOn Ω] fun y => V y :=
    Filter.Eventually.of_forall fun _ => rfl
  simpa only [q, A, V] using
    (integrable_weighted_scalarLp_pair_raw q hq hcompact U₀ V _ _ hU₀ hV)

omit r₀ hc hτ hχshift

end

private theorem integral_pair_mul_const
    {d : ℕ} {Ω : Set (PDE.Vec d)} (z : ℝ)
    (q₁ p₁ q₂ p₂ g : PDE.Vec d → ℝ)
    (h₁ : Integrable (fun y => (q₁ y * p₁ y) * g y) (PDE.volumeOn Ω))
    (h₂ : Integrable (fun y => (q₂ y * p₂ y) * g y) (PDE.volumeOn Ω)) :
    (∫ y in Ω, ((z * q₁ y) * p₁ y + (z * q₂ y) * p₂ y) * g y ∂volume) =
      z * ((∫ y in Ω, (q₁ y * p₁ y) * g y ∂volume) +
        ∫ y in Ω, (q₂ y * p₂ y) * g y ∂volume) := by
  rw [show (fun y => ((z * q₁ y) * p₁ y + (z * q₂ y) * p₂ y) * g y) =
      fun y => z * ((q₁ y * p₁ y) * g y) + z * ((q₂ y * p₂ y) * g y) by
        funext y
        ring]
  exact integral_pair_add_const_mul z _ _ h₁ h₂

private theorem raw_six_term_split
    {d : ℕ} {Ω : Set (PDE.Vec d)} (z : ℝ)
    (source V U₀ : PDE.Vec d → ℝ)
    (aT aD : Fin d → Fin d → PDE.Vec d → ℝ)
    (E H U driftT driftD : Fin d → PDE.Vec d → ℝ)
    (gammaT gammaD : PDE.Vec d → ℝ)
    (haT : ∀ i j : Fin d, Integrable (fun y =>
      (aT i j y * E j y) * H i y) (PDE.volumeOn Ω))
    (haD : ∀ i j : Fin d, Integrable (fun y =>
      (aD i j y * U j y) * H i y) (PDE.volumeOn Ω))
    (hdt : ∀ j : Fin d, Integrable (fun y =>
      (driftT j y * E j y) * V y) (PDE.volumeOn Ω))
    (hdd : ∀ j : Fin d, Integrable (fun y =>
      (driftD j y * U j y) * V y) (PDE.volumeOn Ω))
    (hgt : Integrable (fun y => (gammaT y * V y) * V y) (PDE.volumeOn Ω))
    (hgd : Integrable (fun y => (gammaD y * U₀ y) * V y) (PDE.volumeOn Ω)) :
    -(∫ y in Ω, (z * source y) * V y ∂volume) -
        (∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
          ((z * aT i j y) * E j y + (z * aD i j y) * U j y) * H i y ∂volume) -
        (∑ j : Fin d, ∫ y in Ω,
          ((z * driftT j y) * E j y + (z * driftD j y) * U j y) * V y ∂volume) +
        ∫ y in Ω, ((z * gammaT y) * V y + (z * gammaD y) * U₀ y) * V y ∂volume =
      -(∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
        (z * aT i j y) * E j y * H i y ∂volume) +
        z *
          (-(∫ y in Ω, source y * V y ∂volume) -
              (∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
                (aD i j y * U j y) * H i y ∂volume) -
              (∑ j : Fin d, ∫ y in Ω,
                (driftT j y * E j y) * V y ∂volume) -
              (∑ j : Fin d, ∫ y in Ω,
                (driftD j y * U j y) * V y ∂volume) +
              (∫ y in Ω, (gammaT y * V y) * V y ∂volume) +
              ∫ y in Ω, (gammaD y * U₀ y) * V y ∂volume) := by
  let S : ℝ := ∫ y in Ω, source y * V y ∂volume
  let P : ℝ := ∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
    (aT i j y * E j y) * H i y ∂volume
  let AD : ℝ := ∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
    (aD i j y * U j y) * H i y ∂volume
  let DT : ℝ := ∑ j : Fin d, ∫ y in Ω,
    (driftT j y * E j y) * V y ∂volume
  let DD : ℝ := ∑ j : Fin d, ∫ y in Ω,
    (driftD j y * U j y) * V y ∂volume
  let GT : ℝ := ∫ y in Ω, (gammaT y * V y) * V y ∂volume
  let GD : ℝ := ∫ y in Ω, (gammaD y * U₀ y) * V y ∂volume
  have hsource : (∫ y in Ω, (z * source y) * V y ∂volume) = z * S := by
    dsimp only [S]
    rw [show (fun y => (z * source y) * V y) =
        fun y => z * (source y * V y) by funext y; ring, integral_const_mul]
  have hprincipal (i j : Fin d) :
      (∫ y in Ω,
        ((z * aT i j y) * E j y + (z * aD i j y) * U j y) * H i y ∂volume) =
        z * ((∫ y in Ω, (aT i j y * E j y) * H i y ∂volume) +
          ∫ y in Ω, (aD i j y * U j y) * H i y ∂volume) :=
    integral_pair_mul_const z (aT i j) (E j) (aD i j) (U j) (H i) (haT i j) (haD i j)
  have hprincipalSum :
      (∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
        ((z * aT i j y) * E j y + (z * aD i j y) * U j y) * H i y ∂volume) =
        z * (P + AD) := by
    rw [show (∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
        ((z * aT i j y) * E j y + (z * aD i j y) * U j y) * H i y ∂volume) =
        ∑ i : Fin d, ∑ j : Fin d, z *
          ((∫ y in Ω, (aT i j y * E j y) * H i y ∂volume) +
            ∫ y in Ω, (aD i j y * U j y) * H i y ∂volume) by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          exact hprincipal i j]
    rw [finset_sum_sum_const_mul]
    dsimp only [P, AD]
    simp_rw [Finset.sum_add_distrib]
  have hprincipalWeighted :
      (∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
        (z * aT i j y) * E j y * H i y ∂volume) = z * P := by
    rw [show (∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
        (z * aT i j y) * E j y * H i y ∂volume) =
        ∑ i : Fin d, ∑ j : Fin d, z *
          ∫ y in Ω, (aT i j y * E j y) * H i y ∂volume by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          rw [show (fun y => (z * aT i j y) * E j y * H i y) =
              fun y => z * ((aT i j y * E j y) * H i y) by funext y; ring,
            integral_const_mul]]
    rw [finset_sum_sum_const_mul]
  have hdrift (j : Fin d) :
      (∫ y in Ω,
        ((z * driftT j y) * E j y + (z * driftD j y) * U j y) * V y ∂volume) =
        z * ((∫ y in Ω, (driftT j y * E j y) * V y ∂volume) +
          ∫ y in Ω, (driftD j y * U j y) * V y ∂volume) :=
    integral_pair_mul_const z (driftT j) (E j) (driftD j) (U j) V (hdt j) (hdd j)
  have hdriftSum :
      (∑ j : Fin d, ∫ y in Ω,
        ((z * driftT j y) * E j y + (z * driftD j y) * U j y) * V y ∂volume) =
        z * (DT + DD) := by
    rw [show (∑ j : Fin d, ∫ y in Ω,
        ((z * driftT j y) * E j y + (z * driftD j y) * U j y) * V y ∂volume) =
        ∑ j : Fin d, z *
          ((∫ y in Ω, (driftT j y * E j y) * V y ∂volume) +
            ∫ y in Ω, (driftD j y * U j y) * V y ∂volume) by
          apply Finset.sum_congr rfl
          intro j _
          exact hdrift j]
    rw [finset_sum_const_mul]
    dsimp only [DT, DD]
    simp_rw [Finset.sum_add_distrib]
  have hscalar :
      (∫ y in Ω, ((z * gammaT y) * V y + (z * gammaD y) * U₀ y) * V y ∂volume) =
        z * (GT + GD) := by
    dsimp only [GT, GD]
    exact integral_pair_mul_const z gammaT V gammaD U₀ V hgt hgd
  rw [hsource, hprincipalSum, hdriftSum, hscalar, hprincipalWeighted]
  convert raw_split_eight_real_ring z S P AD DT DD GT GD using 1; ring

private def commutatorRaw
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη Kχ : ℝ}
    (r₀ r₁ : ℝ) (hΩ : IsOpen Ω) (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c F : ℝ → PDE.Vec d → ℝ)
    (ζ : ReverseTimeScalarTest (r₁ - r₀))
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (k : Fin d) (h τ : ℝ)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) (u : H10HilbertGraph hΩ) : ℝ :=
  let A := localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hηshift
  let V : PDE.Vec d → ℝ := fun y => valueCLM hΩ (A u) y
  let G : Fin d → PDE.Vec d → ℝ := fun i y =>
    PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i (gradientCLM hΩ (A u)) y
  let W : Fin d → PDE.Vec d → ℝ := fun i y =>
    cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h (valueCLM hΩ u) y
  let E : Fin d → PDE.Vec d → ℝ := fun i y => G i y - W i y
  let H : Fin d → PDE.Vec d → ℝ := fun i y => G i y + W i y
  let U : Fin d → PDE.Vec d → ℝ := fun j y =>
    η y * PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u) y
  let U₀ : PDE.Vec d → ℝ := fun y => η y * valueCLM hΩ u y
  let source : TimeVelocity d → ℝ := fun z => F (r₁ - z.1) z.2
  let α : Fin d → Fin d → TimeVelocity d → ℝ :=
    fun i j z => reverseTimeCoefficient r₁ a z.1 z.2 i j
  let drift : Fin d → TimeVelocity d → ℝ :=
    fun j z => reverseTimeDivergenceDrift r₁ a b z.1 z.2 j
  let γ : TimeVelocity d → ℝ := fun z => reverseTimeScalarCoefficient r₁ c z.1 z.2
  let sourceD : PDE.Vec d → ℝ := fun y =>
    ζ τ * η y * spatialDifferenceQuotient k h source (τ, y)
  let aT : Fin d → Fin d → PDE.Vec d → ℝ := fun i j y =>
    ζ τ * χ y * spatialTranslate k h (α i j) (τ, y)
  let aD : Fin d → Fin d → PDE.Vec d → ℝ := fun i j y =>
    ζ τ * χ y * spatialDifferenceQuotient k h (α i j) (τ, y)
  let driftT : Fin d → PDE.Vec d → ℝ := fun j y =>
    ζ τ * χ y * spatialTranslate k h (drift j) (τ, y)
  let driftD : Fin d → PDE.Vec d → ℝ := fun j y =>
    ζ τ * χ y * spatialDifferenceQuotient k h (drift j) (τ, y)
  let γT : PDE.Vec d → ℝ := fun y => ζ τ * χ y * spatialTranslate k h γ (τ, y)
  let γD : PDE.Vec d → ℝ := fun y =>
    ζ τ * χ y * spatialDifferenceQuotient k h γ (τ, y)
  ((-(∫ y in Ω, sourceD y * V y ∂volume)) -
    (∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
      (aT i j y * E j y + aD i j y * U j y) * H i y ∂volume) -
    (∑ j : Fin d, ∫ y in Ω,
      (driftT j y * E j y + driftD j y * U j y) * V y ∂volume) +
    (∫ y in Ω, (γT y * V y + γD y * U₀ y) * V y ∂volume))

private def translatedPrincipal
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη Kχ : ℝ}
    (r₀ r₁ : ℝ) (hΩ : IsOpen Ω) (a : CoefficientField d)
    (ζ : ReverseTimeScalarTest (r₁ - r₀))
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ) (k : Fin d) (h τ : ℝ)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) (u : H10HilbertGraph hΩ) : ℝ :=
  let A := localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hηshift
  let G : Fin d → PDE.Vec d → ℝ := fun i y =>
    PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i (gradientCLM hΩ (A u)) y
  let W : Fin d → PDE.Vec d → ℝ := fun i y =>
    cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h (valueCLM hΩ u) y
  let E : Fin d → PDE.Vec d → ℝ := fun i y => G i y - W i y
  let H : Fin d → PDE.Vec d → ℝ := fun i y => G i y + W i y
  let α : Fin d → Fin d → TimeVelocity d → ℝ :=
    fun i j z => reverseTimeCoefficient r₁ a z.1 z.2 i j
  ∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
    (ζ τ * χ y * spatialTranslate k h (α i j) (τ, y)) * E j y * H i y ∂volume

private theorem commutatorRaw_eq_split
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη Kχ : ℝ}
    (r₀ r₁ : ℝ) (hΩ : IsOpen Ω) (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c F : ℝ → PDE.Vec d → ℝ)
    (ha : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hb : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hc : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (ζ : ReverseTimeScalarTest (r₁ - r₀))
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (k : Fin d) (h τ : ℝ)
    (hχshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport χ.toFun) Ω)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω)
    (hτ : τ ∈ Set.Icc 0 (r₁ - r₀)) (u : H10HilbertGraph hΩ) :
    commutatorRaw r₀ r₁ hΩ a b c F ζ η χ k h τ hηshift u =
      -translatedPrincipal r₀ r₁ hΩ a ζ η χ k h τ hηshift u + ζ τ *
        localizedSpatialDifferenceQuotientH10NonprincipalRemainder
          r₁ hΩ a b c F η χ k h τ hηshift u := by
  let A := localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hηshift
  let V : PDE.Vec d → ℝ := fun y => valueCLM hΩ (A u) y
  let G : Fin d → PDE.Vec d → ℝ := fun i y =>
    PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i (gradientCLM hΩ (A u)) y
  let W : Fin d → PDE.Vec d → ℝ := fun i y =>
    cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h (valueCLM hΩ u) y
  let E : Fin d → PDE.Vec d → ℝ := fun i y => G i y - W i y
  let H : Fin d → PDE.Vec d → ℝ := fun i y => G i y + W i y
  let U : Fin d → PDE.Vec d → ℝ := fun j y =>
    η y * PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u) y
  let U₀ : PDE.Vec d → ℝ := fun y => η y * valueCLM hΩ u y
  let source : TimeVelocity d → ℝ := fun z => F (r₁ - z.1) z.2
  let sourceD : PDE.Vec d → ℝ := fun y =>
    η y * spatialDifferenceQuotient k h source (τ, y)
  let α : Fin d → Fin d → TimeVelocity d → ℝ :=
    fun i j z => reverseTimeCoefficient r₁ a z.1 z.2 i j
  let drift : Fin d → TimeVelocity d → ℝ :=
    fun j z => reverseTimeDivergenceDrift r₁ a b z.1 z.2 j
  let γ : TimeVelocity d → ℝ := fun z => reverseTimeScalarCoefficient r₁ c z.1 z.2
  let aT : Fin d → Fin d → PDE.Vec d → ℝ := fun i j y =>
    χ y * spatialTranslate k h (α i j) (τ, y)
  let aD : Fin d → Fin d → PDE.Vec d → ℝ := fun i j y =>
    χ y * spatialDifferenceQuotient k h (α i j) (τ, y)
  let driftT : Fin d → PDE.Vec d → ℝ := fun j y =>
    χ y * spatialTranslate k h (drift j) (τ, y)
  let driftD : Fin d → PDE.Vec d → ℝ := fun j y =>
    χ y * spatialDifferenceQuotient k h (drift j) (τ, y)
  let γT : PDE.Vec d → ℝ := fun y => χ y * spatialTranslate k h γ (τ, y)
  let γD : PDE.Vec d → ℝ := fun y =>
    χ y * spatialDifferenceQuotient k h γ (τ, y)
  have hsplit := raw_six_term_split (z := ζ τ) sourceD V U₀ aT aD E H U driftT driftD
    γT γD
    (fun i j => by
      dsimp only [aT, E, H, G, W, A]
      exact integrable_aT_E_H (r₀ := r₀) (r₁ := r₁) (hΩ := hΩ) (a := a) (ha := ha)
        (η := η) (χ := χ) (k := k) (h := h) (τ := τ) (hχshift := hχshift)
        (hηshift := hηshift) (hτ := hτ) (u := u) i j)
    (fun i j => by
      dsimp only [aD, U, H, G, W, A]
      exact integrable_aD_U_H (r₀ := r₀) (r₁ := r₁) (hΩ := hΩ) (a := a) (ha := ha)
        (η := η) (χ := χ) (k := k) (h := h) (τ := τ) (hχshift := hχshift)
        (hηshift := hηshift) (hτ := hτ) (u := u) i j)
    (fun j => by
      dsimp only [driftT, E, V, G, W, A]
      exact integrable_driftT_E_V (r₀ := r₀) (r₁ := r₁) (hΩ := hΩ) (a := a) (b := b)
        (ha := ha) (hb := hb) (η := η) (χ := χ) (k := k) (h := h) (τ := τ)
        (hχshift := hχshift) (hηshift := hηshift) (hτ := hτ) (u := u) j)
    (fun j => by
      dsimp only [driftD, U, V, G, W, A]
      exact integrable_driftD_U_V (r₀ := r₀) (r₁ := r₁) (hΩ := hΩ) (a := a) (b := b)
        (ha := ha) (hb := hb) (η := η) (χ := χ) (k := k) (h := h) (τ := τ)
        (hχshift := hχshift) (hηshift := hηshift) (hτ := hτ) (u := u) j)
    (by
      dsimp only [γT, V, γ, A]
      exact integrable_gammaT_V_V (r₀ := r₀) (r₁ := r₁) (hΩ := hΩ) (c := c)
        (hc := hc) (η := η) (χ := χ) (k := k) (h := h) (τ := τ)
        (hχshift := hχshift) (hηshift := hηshift) (hτ := hτ) (u := u))
    (by
      dsimp only [γD, U₀, V, γ, A]
      exact integrable_gammaD_U0_V (r₀ := r₀) (r₁ := r₁) (hΩ := hΩ) (c := c)
        (hc := hc) (η := η) (χ := χ) (k := k) (h := h) (τ := τ)
        (hχshift := hχshift) (hηshift := hηshift) (hτ := hτ) (u := u))
  simpa only [commutatorRaw, translatedPrincipal,
    localizedSpatialDifferenceQuotientH10NonprincipalRemainder, A, V, G, W, E, H, U, U₀,
    source, sourceD, α, drift, γ, aT, aD, driftT, driftD, γT, γD, mul_assoc] using hsplit

private def commutatorLhs
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη : ℝ}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c F : ℝ → PDE.Vec d → ℝ)
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (ζ : ReverseTimeScalarTest (r₁ - r₀))
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη) (k : Fin d) (h τ : ℝ)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) (u : H10HilbertGraph hΩ) : ℝ :=
  let B := localizedSpatialDifferenceQuotientEnergyTestH10CLM
    hΩ η k h η.tsupport_subset hηshift
  ζ τ * (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ (B u) -
    reverseTimeSpatialForm hΩ r₁ τ a b c u (B u))

private def compactCommutatorOutput
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη Kχ : ℝ}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (F : ℝ → PDE.Vec d → ℝ)
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (ζ : ReverseTimeScalarTest (r₁ - r₀)) (hζunit : ∀ τ : ℝ, ‖ζ τ‖ ≤ 1)
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ (k : Fin d) (h : ℝ), |h| ≤ δ →
    ∃ hχshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport χ.toFun) Ω, ∀ (τ : ℝ) (hτ : τ ∈ Set.Icc 0 (r₁ - r₀))
      (u : H10HilbertGraph hΩ),
      let hηχ : tsupport η.toFun ⊆ tsupport χ.toFun := by
        intro y hy; apply subset_tsupport; change χ y ≠ 0
        rw [χ.eq_one_on_inner y hy]; exact one_ne_zero
      let hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
          (tsupport η.toFun) Ω := hχshift.mono_left hηχ
      commutatorLhs r₀ r₁ h₀₁ hΩ hΩbounded a b c F hFSmooth ζ η k h τ hηshift u =
        commutatorRaw r₀ r₁ hΩ a b c F ζ η χ k h τ hηshift u

private theorem compactCommutatorOutput_of_accepted
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη Kχ : ℝ}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (F : ℝ → PDE.Vec d → ℝ)
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (ζ : ReverseTimeScalarTest (r₁ - r₀)) (hζunit : ∀ τ : ℝ, ‖ζ τ‖ ≤ 1)
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ) :
    compactCommutatorOutput r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth
      F hFSmooth ζ hζunit η χ := by
  obtain ⟨δ, hδ, hrest⟩ :=
    exists_smallStep_reverseTimeSource_sub_reverseTimeSpatialForm_energyTest_eq_commutator
      r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth F hFSmooth ζ hζunit η χ
  refine ⟨δ, hδ, ?_⟩
  intro k h hh
  obtain ⟨hχshift, hfixed⟩ := hrest k h hh
  refine ⟨hχshift, ?_⟩
  intro τ hτ u
  change commutatorLhs r₀ r₁ h₀₁ hΩ hΩbounded a b c F hFSmooth ζ η k h τ _ u =
    commutatorRaw r₀ r₁ hΩ a b c F ζ η χ k h τ _ u
  simpa only [commutatorLhs, commutatorRaw] using hfixed τ hτ u

private def compactSplitOutput
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη Kχ : ℝ}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (F : ℝ → PDE.Vec d → ℝ)
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (ζ : ReverseTimeScalarTest (r₁ - r₀)) (hζunit : ∀ τ : ℝ, ‖ζ τ‖ ≤ 1)
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ (k : Fin d) (h : ℝ), |h| ≤ δ →
    ∃ hχshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport χ.toFun) Ω, ∀ (τ : ℝ) (hτ : τ ∈ Set.Icc 0 (r₁ - r₀))
      (u : H10HilbertGraph hΩ),
      let hηχ : tsupport η.toFun ⊆ tsupport χ.toFun := by
        intro y hy; apply subset_tsupport; change χ y ≠ 0
        rw [χ.eq_one_on_inner y hy]; exact one_ne_zero
      let hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
          (tsupport η.toFun) Ω := hχshift.mono_left hηχ
      commutatorLhs r₀ r₁ h₀₁ hΩ hΩbounded a b c F hFSmooth ζ η k h τ hηshift u =
        -translatedPrincipal r₀ r₁ hΩ a ζ η χ k h τ hηshift u + ζ τ *
          localizedSpatialDifferenceQuotientH10NonprincipalRemainder
            r₁ hΩ a b c F η χ k h τ hηshift u

private theorem compactSplitOutput_of_compact
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη Kχ : ℝ}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (F : ℝ → PDE.Vec d → ℝ)
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (ζ : ReverseTimeScalarTest (r₁ - r₀)) (hζunit : ∀ τ : ℝ, ‖ζ τ‖ ≤ 1)
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ) :
    compactSplitOutput r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth
      F hFSmooth ζ hζunit η χ := by
  obtain ⟨δ, hδ, hrest⟩ := compactCommutatorOutput_of_accepted
    r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth F hFSmooth ζ hζunit η χ
  refine ⟨δ, hδ, ?_⟩
  intro k h hh
  obtain ⟨hχshift, hfixed⟩ := hrest k h hh
  refine ⟨hχshift, ?_⟩
  intro τ hτ u
  exact (hfixed τ hτ u).trans
    (commutatorRaw_eq_split r₀ r₁ hΩ a b c F haSmooth hbSmooth hcSmooth ζ η χ k h τ
      hχshift _ hτ u)

/-- For all sufficiently small signed spatial steps, the exact arbitrary-`H¹₀`
fixed-slice commutator is minus its translated-principal term plus the scalar
time weight times the raw six-term nonprincipal remainder. -/
theorem
    exists_smallStep_h10Commutator_eq_neg_translatedPrincipal_add_nonprincipalRemainder
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη Kχ : ℝ}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (F : ℝ → PDE.Vec d → ℝ)
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (ζ : ReverseTimeScalarTest (r₁ - r₀)) (hζunit : ∀ τ : ℝ, ‖ζ τ‖ ≤ 1)
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (k : Fin d) (h : ℝ), |h| ≤ δ →
        ∃ hχshift : Set.MapsTo
          (fun y : PDE.Vec d => y + h • PDE.basisVec k)
          (tsupport χ.toFun) Ω,
        ∀ (τ : ℝ) (hτ : τ ∈ Set.Icc 0 (r₁ - r₀))
          (u : H10HilbertGraph hΩ),
        let hηχ : tsupport η.toFun ⊆ tsupport χ.toFun := by
          intro y hy
          apply subset_tsupport
          change χ y ≠ 0
          rw [χ.eq_one_on_inner y hy]
          exact one_ne_zero
        let hηshift : Set.MapsTo
            (fun y : PDE.Vec d => y + h • PDE.basisVec k)
            (tsupport η.toFun) Ω :=
          hχshift.mono_left hηχ
        let A : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
          localizedSpatialDifferenceQuotientH10CLM
            hΩ η k h η.tsupport_subset hηshift
        let B : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
          localizedSpatialDifferenceQuotientEnergyTestH10CLM
            hΩ η k h η.tsupport_subset hηshift
        let G : Fin d → PDE.Vec d → ℝ := fun i y =>
          PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
            (gradientCLM hΩ (A u)) y
        let W : Fin d → PDE.Vec d → ℝ := fun i y =>
          cutoffGradientSpatialDifferenceQuotientL2
            hΩ.measurableSet η i k h (valueCLM hΩ u) y
        let E : Fin d → PDE.Vec d → ℝ := fun i y => G i y - W i y
        let H : Fin d → PDE.Vec d → ℝ := fun i y => G i y + W i y
        let α : Fin d → Fin d → TimeVelocity d → ℝ :=
          fun i j z => reverseTimeCoefficient r₁ a z.1 z.2 i j
        let Q : ℝ := ζ τ *
            (reverseTimeNegativeSourceRaw
                r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ (B u) -
              reverseTimeSpatialForm hΩ r₁ τ a b c u (B u))
        let P : ℝ := ∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
            (ζ τ * χ y * spatialTranslate k h (α i j) (τ, y)) *
              E j y * H i y ∂volume
        let R : ℝ :=
          localizedSpatialDifferenceQuotientH10NonprincipalRemainder
            r₁ hΩ a b c F η χ k h τ hηshift u
        Q = -P + ζ τ * R := by
  change compactSplitOutput r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth
    F hFSmooth ζ hζunit η χ
  exact compactSplitOutput_of_compact
    r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth F hFSmooth ζ hζunit η χ

/-- The fixed supplied-collar commutator is minus its translated-principal part
plus the nonprincipal remainder under the uniform majorants. -/
theorem h10Commutator_eq_neg_translatedPrincipal_add_nonprincipalRemainder_of_majorants
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη Kχ : ℝ}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω)
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (ζ : ReverseTimeScalarTest (r₁ - r₀)) (hζunit : ∀ τ : ℝ, ‖ζ τ‖ ≤ 1)
    (δ : ℝ)
    (hcarrier : spatialCoordinateShiftCarrier (tsupport χ.toFun) δ ⊆ Ω)
    (M : ℝ) (hM : 0 ≤ M)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c F : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hA : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
      spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
      spatialMatrixFDerivFrobeniusNorm
        (fun w : TimeVelocity d => reverseTimeCoefficient r₁ a w.1 w.2) z ≤ M)
    (hB : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
      spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
      PDE.vecEuclideanNorm (reverseTimeDivergenceDrift r₁ a b z.1 z.2) ≤ M)
    (hBD : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
      spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
      spatialVectorFDerivFrobeniusNorm
        (fun w : TimeVelocity d => reverseTimeDivergenceDrift r₁ a b w.1 w.2) z ≤ M)
    (hq : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
      spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
      |-(reverseTimeScalarCoefficient r₁ c z.1 z.2)| ≤ M)
    (hqD : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
      spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
      spatialScalarFDerivEuclideanNorm
        (fun w : TimeVelocity d => -(reverseTimeScalarCoefficient r₁ c w.1 w.2)) z ≤ M)
    (hfD : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
      spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
      spatialScalarFDerivEuclideanNorm
        (fun w : TimeVelocity d => -(reverseTimeScalarCoefficient r₁ F w.1 w.2)) z ≤ M)
    (k : Fin d) (h : ℝ) (hh : |h| ≤ δ) (τ : ℝ)
    (hτ : τ ∈ Set.Icc 0 (r₁ - r₀)) (u : H10HilbertGraph hΩ) :
    let hχshift : Set.MapsTo
        (fun y : PDE.Vec d => y + h • PDE.basisVec k) (tsupport χ.toFun) Ω :=
      mapsTo_add_smul_basisVec_of_spatialCoordinateShiftCarrier_subset hcarrier k hh
    let hηχ : tsupport η.toFun ⊆ tsupport χ.toFun := by
      intro y hy
      apply subset_tsupport
      change χ y ≠ 0
      rw [χ.eq_one_on_inner y hy]
      exact one_ne_zero
    let hηshift : Set.MapsTo
        (fun y : PDE.Vec d => y + h • PDE.basisVec k) (tsupport η.toFun) Ω :=
      hχshift.mono_left hηχ
    let A : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
      localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hηshift
    let B : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
      localizedSpatialDifferenceQuotientEnergyTestH10CLM
        hΩ η k h η.tsupport_subset hηshift
    let G : Fin d → PDE.Vec d → ℝ := fun i y =>
      PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i (gradientCLM hΩ (A u)) y
    let W : Fin d → PDE.Vec d → ℝ := fun i y =>
      cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h (valueCLM hΩ u) y
    let E : Fin d → PDE.Vec d → ℝ := fun i y => G i y - W i y
    let H : Fin d → PDE.Vec d → ℝ := fun i y => G i y + W i y
    let α : Fin d → Fin d → TimeVelocity d → ℝ :=
      fun i j z => reverseTimeCoefficient r₁ a z.1 z.2 i j
    let Q : ℝ := ζ τ *
      (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ (B u) -
        reverseTimeSpatialForm hΩ r₁ τ a b c u (B u))
    let P : ℝ := ∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
      (ζ τ * χ y * spatialTranslate k h (α i j) (τ, y)) * E j y * H i y ∂volume
    let R : ℝ := localizedSpatialDifferenceQuotientH10NonprincipalRemainder
      r₁ hΩ a b c F η χ k h τ hηshift u
    Q = -P + ζ τ * R := by
  let hχshift : Set.MapsTo
      (fun y : PDE.Vec d => y + h • PDE.basisVec k) (tsupport χ.toFun) Ω :=
    mapsTo_add_smul_basisVec_of_spatialCoordinateShiftCarrier_subset hcarrier k hh
  let hηχ : tsupport η.toFun ⊆ tsupport χ.toFun := by
    intro y hy
    apply subset_tsupport
    change χ y ≠ 0
    rw [χ.eq_one_on_inner y hy]
    exact one_ne_zero
  let hηshift : Set.MapsTo
      (fun y : PDE.Vec d => y + h • PDE.basisVec k) (tsupport η.toFun) Ω :=
    hχshift.mono_left hηχ
  have hcomm :=
    reverseTimeSource_sub_reverseTimeSpatialForm_energyTest_eq_commutator_of_majorants
      r₀ r₁ h₀₁ hΩ hΩbounded η χ ζ hζunit δ M hM hcarrier a b c F haSmooth
      hbSmooth hcSmooth hFSmooth hA hB hBD hq hqD hfD k h hh τ hτ u
  have hsplit := commutatorRaw_eq_split r₀ r₁ hΩ a b c F haSmooth hbSmooth hcSmooth ζ η χ
    k h τ hχshift hηshift hτ u
  simpa only [hχshift, hηχ, hηshift, commutatorRaw, translatedPrincipal,
    localizedSpatialDifferenceQuotientH10NonprincipalRemainder] using hcomm.trans hsplit

end HypoellipticAleksandrov.Parabolic.Dirichlet
