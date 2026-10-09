module

public import HypoellipticAleksandrov.Parabolic.SpatialFDerivNormContinuity
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSmoothness
public import HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialCoordinateShiftCarrier
public import PDEFoundation.Sobolev.Cutoff.Basic

/-!
# Interior coefficient majorants after time reflection

Smooth reflected coefficients have bounded majorants on compact interior carriers.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open Set
open scoped BigOperators Matrix.Norms.Elementwise

private theorem IsSmoothOnNeighborhood.reverseTimeNormed
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S K : Set (TimeVelocity d)} (r₁ : ℝ) {f : TimeVelocity d → E}
    (hSK : reverseTimeMap r₁ '' S ⊆ K) (hf : IsSmoothOnNeighborhood f K) :
    IsSmoothOnNeighborhood (f ∘ reverseTimeMap r₁) S := by
  rcases hf with ⟨V, hVopen, hKV, hV⟩
  refine ⟨reverseTimeMap r₁ ⁻¹' V,
    (contDiff_reverseTimeMap r₁).continuous.isOpen_preimage V hVopen, ?_, ?_⟩
  · intro z hz
    exact hKV (hSK ⟨z, hz, rfl⟩)
  · exact hV.comp
      ((contDiff_reverseTimeMap r₁).of_le (by exact_mod_cast le_top)).contDiffOn
      fun _ hz => hz

private theorem IsSmoothOnNeighborhood.negScalar
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} {f : E → ℝ} (hf : IsSmoothOnNeighborhood f K) :
    IsSmoothOnNeighborhood (-f) K := by
  rcases hf with ⟨V, hVopen, hKV, hV⟩
  exact ⟨V, hVopen, hKV, hV.neg⟩

private theorem IsSmoothOnNeighborhood.continuousOn
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set E} {f : E → F} (hf : IsSmoothOnNeighborhood f K) :
    ContinuousOn f K := by
  rcases hf with ⟨V, _hVopen, hKV, hV⟩
  exact hV.continuousOn.mono hKV

private theorem IsSmoothOnNeighborhood.divergenceDrift
    {d : ℕ} {K : Set (TimeVelocity d)}
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (ha : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2) K)
    (hb : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2) K) :
    IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => scalarSpatialCoefficientDivergence a z - b z.1 z.2) K := by
  rcases ha with ⟨Va, hVaopen, hKVa, hVa⟩
  rcases hb with ⟨Vb, hVbopen, hKVb, hVb⟩
  refine ⟨Va ∩ Vb, hVaopen.inter hVbopen, fun z hz => ⟨hKVa hz, hKVb hz⟩, ?_⟩
  apply ContDiffOn.sub
  · apply contDiffOn_pi'
    intro j
    have hentry (i : Fin d) : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun z : TimeVelocity d => a z.1 z.2 i j) Va := by
      exact (contDiffOn_apply ℝ ℝ j Set.univ).comp
        ((contDiffOn_apply ℝ (Fin d → ℝ) i Set.univ).comp hVa fun _ _ => Set.mem_univ _)
        fun _ _ => Set.mem_univ _
    have hsum : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d =>
        ∑ i : Fin d, (fderiv ℝ (fun w : TimeVelocity d => a w.1 w.2 i j) z)
          (0, PDE.basisVec i)) Va := by
      apply ContDiffOn.sum
      intro i _
      exact ((hentry i).fderiv_of_isOpen hVaopen (m := (⊤ : ℕ∞)) (by simp)).clm_apply
        contDiffOn_const
    refine (hsum.congr ?_).mono Set.inter_subset_left
    intro z hz
    rcases z with ⟨r, y⟩
    simp only [scalarSpatialCoefficientDivergence]
    apply Finset.sum_congr rfl
    intro i _
    exact fderiv_spatialSlice_apply a r y (PDE.basisVec i) i j
      (((hentry i).contDiffAt (hVaopen.mem_nhds hz)).differentiableAt (by simp))
  · exact hVb.mono Set.inter_subset_right

private theorem reverseTimeImage_subset_closedCylinder
    {d : ℕ} {r₀ r₁ : ℝ} {Ω K : Set (PDE.Vec d)}
    (hKΩ : K ⊆ Ω) :
    reverseTimeMap r₁ '' (Set.Icc 0 (r₁ - r₀) ×ˢ K) ⊆
      scalarParabolicClosedCylinder r₀ r₁ Ω := by
  rintro w ⟨z, hz, rfl⟩
  rw [mem_scalarParabolicClosedCylinder_iff]
  refine ⟨?_, ?_, subset_closure (hKΩ hz.2)⟩
  · simp only [reverseTimeMap_apply]
    linarith [hz.1.2]
  · simp only [reverseTimeMap_apply]
    linarith [hz.1.1]

/-- Smooth data have one common finite majorant for all coefficient and source
quantities used by the interior difference-quotient estimate. -/
theorem exists_reverseTimeInteriorCoefficientMajorant
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kχ : ℝ}
    (r₀ r₁ : ℝ)
    (χ : PDE.QuantitativeSmoothCutoff inner Ω Kχ)
    (δ : ℝ)
    (hcarrier :
      spatialCoordinateShiftCarrier (tsupport χ.toFun) δ ⊆ Ω)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c F : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hFSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) :
    ∃ M : ℝ, 0 ≤ M ∧
      (∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
          spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
        spatialMatrixFDerivFrobeniusNorm
          (fun w : TimeVelocity d =>
            reverseTimeCoefficient r₁ a w.1 w.2) z ≤ M) ∧
      (∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
          spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
        PDE.vecEuclideanNorm
          (reverseTimeDivergenceDrift r₁ a b z.1 z.2) ≤ M) ∧
      (∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
          spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
        spatialVectorFDerivFrobeniusNorm
          (fun w : TimeVelocity d =>
            reverseTimeDivergenceDrift r₁ a b w.1 w.2) z ≤ M) ∧
      (∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
          spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
        |-(reverseTimeScalarCoefficient r₁ c z.1 z.2)| ≤ M) ∧
      (∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
          spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
        spatialScalarFDerivEuclideanNorm
          (fun w : TimeVelocity d =>
            -(reverseTimeScalarCoefficient r₁ c w.1 w.2)) z ≤ M) ∧
      ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
          spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
        spatialScalarFDerivEuclideanNorm
          (fun w : TimeVelocity d =>
            -(reverseTimeScalarCoefficient r₁ F w.1 w.2)) z ≤ M := by
  classical
  let Q : Set (TimeVelocity d) := Set.Icc 0 (r₁ - r₀) ×ˢ
    spatialCoordinateShiftCarrier (tsupport χ.toFun) δ
  have hχcompact : IsCompact (tsupport χ.toFun) := χ.hasCompactSupport
  have hQcompact : IsCompact Q := isCompact_Icc.prod
    (HypoellipticAleksandrov.Parabolic.Dirichlet.IsCompact.spatialCoordinateShiftCarrier
      hχcompact δ)
  have himage : reverseTimeMap r₁ '' Q ⊆ scalarParabolicClosedCylinder r₀ r₁ Ω :=
    reverseTimeImage_subset_closedCylinder hcarrier
  have haR : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => reverseTimeCoefficient r₁ a z.1 z.2) Q := by
    change IsSmoothOnNeighborhood
      ((fun z : TimeVelocity d => a z.1 z.2) ∘ reverseTimeMap r₁) Q
    exact IsSmoothOnNeighborhood.reverseTimeNormed r₁ himage haSmooth
  have hbR : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => reverseTimeDivergenceDrift r₁ a b z.1 z.2) Q := by
    change IsSmoothOnNeighborhood
      ((fun z : TimeVelocity d => scalarSpatialCoefficientDivergence a z - b z.1 z.2) ∘
        reverseTimeMap r₁) Q
    exact IsSmoothOnNeighborhood.reverseTimeNormed r₁ himage
      (IsSmoothOnNeighborhood.divergenceDrift a b haSmooth hbSmooth)
  have hcR : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => -(reverseTimeScalarCoefficient r₁ c z.1 z.2)) Q := by
    change IsSmoothOnNeighborhood
      (-((fun z : TimeVelocity d => c z.1 z.2) ∘ reverseTimeMap r₁)) Q
    exact IsSmoothOnNeighborhood.negScalar
      (IsSmoothOnNeighborhood.reverseTime r₁ himage hcSmooth)
  have hFR : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => -(reverseTimeScalarCoefficient r₁ F z.1 z.2)) Q := by
    change IsSmoothOnNeighborhood
      (-((fun z : TimeVelocity d => F z.1 z.2) ∘ reverseTimeMap r₁)) Q
    exact IsSmoothOnNeighborhood.negScalar
      (IsSmoothOnNeighborhood.reverseTime r₁ himage hFSmooth)
  have hBvalue : ContinuousOn (fun z : TimeVelocity d =>
      PDE.vecEuclideanNorm (reverseTimeDivergenceDrift r₁ a b z.1 z.2)) Q := by
    unfold PDE.vecEuclideanNorm PDE.vecNormSq
    apply Real.continuous_sqrt.comp_continuousOn
    apply continuousOn_finset_sum
    intro j _
    simpa only [Function.comp_def, Pi.pow_apply, pow_two, Pi.mul_def] using
      (((continuous_apply j).comp_continuousOn
        (IsSmoothOnNeighborhood.continuousOn hbR)).pow 2)
  obtain ⟨C₁, hC₁⟩ := hQcompact.exists_bound_of_continuousOn
    haR.continuousOn_spatialMatrixFDerivFrobeniusNorm
  obtain ⟨C₂, hC₂⟩ := hQcompact.exists_bound_of_continuousOn hBvalue
  obtain ⟨C₃, hC₃⟩ := hQcompact.exists_bound_of_continuousOn
    hbR.continuousOn_spatialVectorFDerivFrobeniusNorm
  obtain ⟨C₄, hC₄⟩ := hQcompact.exists_bound_of_continuousOn
    (continuous_abs.comp_continuousOn (IsSmoothOnNeighborhood.continuousOn hcR))
  obtain ⟨C₅, hC₅⟩ := hQcompact.exists_bound_of_continuousOn
    hcR.continuousOn_spatialScalarFDerivEuclideanNorm
  obtain ⟨C₆, hC₆⟩ := hQcompact.exists_bound_of_continuousOn
    hFR.continuousOn_spatialScalarFDerivEuclideanNorm
  let M := max 0 (max C₁ (max C₂ (max C₃ (max C₄ (max C₅ C₆)))))
  refine ⟨M, le_max_left _ _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact (le_abs_self _).trans <| (hC₁ z hz).trans <|
      (le_max_left C₁ _).trans (le_max_right 0 _)
  · intro z hz
    exact (le_abs_self _).trans <| (hC₂ z hz).trans <| (le_max_left C₂ _).trans
      ((le_max_right C₁ _).trans (le_max_right 0 _))
  · intro z hz
    exact (le_abs_self _).trans <| (hC₃ z hz).trans <| (le_max_left C₃ _).trans
      ((le_max_right C₂ _).trans ((le_max_right C₁ _).trans (le_max_right 0 _)))
  · intro z hz
    simpa only [Real.norm_eq_abs, abs_abs, Function.comp_apply] using
      (hC₄ z hz).trans ((le_max_left C₄ _).trans
      ((le_max_right C₃ _).trans ((le_max_right C₂ _).trans
        ((le_max_right C₁ _).trans (le_max_right 0 _)))))
  · intro z hz
    exact (le_abs_self _).trans <| (hC₅ z hz).trans <| (le_max_left C₅ _).trans
      ((le_max_right C₄ _).trans ((le_max_right C₃ _).trans
        ((le_max_right C₂ _).trans ((le_max_right C₁ _).trans (le_max_right 0 _)))))
  · intro z hz
    exact (le_abs_self _).trans <| (hC₆ z hz).trans <| (le_max_right C₅ C₆).trans
      ((le_max_right C₄ _).trans ((le_max_right C₃ _).trans
        ((le_max_right C₂ _).trans ((le_max_right C₁ _).trans (le_max_right 0 _)))))

end HypoellipticAleksandrov.Parabolic.Dirichlet
