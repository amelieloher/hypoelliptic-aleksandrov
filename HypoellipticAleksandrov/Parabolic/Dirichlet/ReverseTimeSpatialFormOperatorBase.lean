module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormBounds
public import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Fixed-time reverse-time spatial form operator

This module continuizes the literal reverse-time spatial form at each local
time. Its public API provides the time-uniform slice multiplier bounds, the
local operator, its literal evaluation, and its uniform application bound.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal RealInnerProductSpace Matrix.Norms.Elementwise MatrixOrder

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

private theorem continuousOn_reverseTimeCoefficientEntry_slice
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ τ : ℝ) (a : CoefficientField d) (i j : Fin d)
    (ha : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hτ : τ ∈ Set.Icc 0 (r₁ - r₀)) :
    ContinuousOn (fun y : PDE.Vec d => a (r₁ - τ) y i j) Ω := by
  rcases ha with ⟨V, hVopen, hKV, hV⟩
  have hrow : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => a z.1 z.2 i) V := by
    exact (contDiffOn_apply ℝ (Fin d → ℝ) i Set.univ).comp hV (by
      intro z hz
      exact Set.mem_univ _)
  have hentry : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => a z.1 z.2 i j) V := by
    exact (contDiffOn_apply ℝ ℝ j Set.univ).comp hrow (by
      intro z hz
      exact Set.mem_univ _)
  have htime : r₀ ≤ r₁ - τ ∧ r₁ - τ ≤ r₁ := by
    constructor <;> linarith [hτ.1, hτ.2]
  have hmap : MapsTo (fun y : PDE.Vec d => (r₁ - τ, y)) Ω
      (scalarParabolicClosedCylinder r₀ r₁ Ω) := by
    intro y hy
    exact ⟨htime, subset_closure hy⟩
  simpa [Function.comp_def] using! (hentry.continuousOn.mono hKV).comp
    (Continuous.prodMk_right _).continuousOn hmap

private theorem continuousOn_reverseTimeDivergenceDriftEntry_slice
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ τ : ℝ) (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (j : Fin d)
    (ha : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hb : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hτ : τ ∈ Set.Icc 0 (r₁ - r₀)) :
    ContinuousOn (fun y : PDE.Vec d => reverseTimeDivergenceDrift r₁ a b τ y j) Ω := by
  have htime : r₀ ≤ r₁ - τ ∧ r₁ - τ ≤ r₁ := by
    constructor <;> linarith [hτ.1, hτ.2]
  have hmap : MapsTo (fun y : PDE.Vec d => (r₁ - τ, y)) Ω
      (scalarParabolicClosedCylinder r₀ r₁ Ω) := by
    intro y hy
    exact ⟨htime, subset_closure hy⟩
  have hdiv : ContinuousOn (fun y : PDE.Vec d =>
      scalarSpatialCoefficientDivergence (reverseTimeCoefficient r₁ a) (τ, y) j) Ω := by
    have hcont := continuousOn_scalarSpatialCoefficientDivergence_of_smoothOnNeighborhood
      r₀ r₁ a ha
    have hvec : ContinuousOn (fun y : PDE.Vec d =>
        scalarSpatialCoefficientDivergence a (r₁ - τ, y)) Ω := by
      simpa [Function.comp_def] using hcont.comp (Continuous.prodMk_right _).continuousOn hmap
    have heval : ContinuousOn (fun x : PDE.Vec d => x j) Set.univ :=
      (continuous_apply j).continuousOn
    simpa only [Function.comp_def, scalarSpatialCoefficientDivergence_reverseTimeCoefficient,
      reverseTimeMap_apply] using heval.comp hvec (by intro y hy; simp)
  rcases hb with ⟨V, hVopen, hKV, hV⟩
  have hentry : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => b z.1 z.2 j) V := by
    exact (contDiffOn_apply ℝ ℝ j Set.univ).comp hV (by
      intro z hz
      exact Set.mem_univ _)
  have hbcont : ContinuousOn (fun y : PDE.Vec d => b (r₁ - τ) y j) Ω := by
    simpa [Function.comp_def] using! (hentry.continuousOn.mono hKV).comp
      (Continuous.prodMk_right _).continuousOn hmap
  simpa only [reverseTimeDivergenceDrift, reverseTimeVectorCoefficient_apply,
    Pi.sub_apply, Pi.sub_def] using hdiv.sub hbcont

/-- Smooth coefficients have nonnegative, time-uniform bounds for the slice multipliers. -/
theorem exists_sliceMultiplierBounds_of_smoothOnNeighborhood
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) :
    ∃ (Ca : Fin d → Fin d → ℝ) (Cd : Fin d → ℝ) (Cc : ℝ),
      (∀ i j, 0 ≤ Ca i j) ∧ (∀ j, 0 ≤ Cd j) ∧ 0 ≤ Cc ∧
      (∀ τ : Set.Icc 0 (r₁ - r₀), ∀ i j,
        AEStronglyMeasurable (fun y => a (r₁ - τ.1) y i j) (PDE.volumeOn Ω)) ∧
      (∀ τ : Set.Icc 0 (r₁ - r₀), ∀ i j,
        ∀ᵐ y ∂PDE.volumeOn Ω, ‖a (r₁ - τ.1) y i j‖ ≤ Ca i j) ∧
      (∀ τ : Set.Icc 0 (r₁ - r₀), ∀ j,
        AEStronglyMeasurable
          (fun y => reverseTimeDivergenceDrift r₁ a b τ.1 y j) (PDE.volumeOn Ω)) ∧
      (∀ τ : Set.Icc 0 (r₁ - r₀), ∀ j,
        ∀ᵐ y ∂PDE.volumeOn Ω,
          ‖reverseTimeDivergenceDrift r₁ a b τ.1 y j‖ ≤ Cd j) ∧
      (∀ τ : Set.Icc 0 (r₁ - r₀),
        AEStronglyMeasurable
          (fun y => reverseTimeScalarCoefficient r₁ c τ.1 y) (PDE.volumeOn Ω)) ∧
      (∀ τ : Set.Icc 0 (r₁ - r₀),
        ∀ᵐ y ∂PDE.volumeOn Ω,
          ‖reverseTimeScalarCoefficient r₁ c τ.1 y‖ ≤ Cc) := by
  have haCont (i j : Fin d) : ContinuousOn (fun z : TimeVelocity d => a z.1 z.2 i j)
      (scalarParabolicClosedCylinder r₀ r₁ Ω) := by
    rcases haSmooth with ⟨V, hVopen, hKV, hV⟩
    have hrow : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => a z.1 z.2 i) V := by
      exact (contDiffOn_apply ℝ (Fin d → ℝ) i Set.univ).comp hV
        (by intro z hz; exact Set.mem_univ _)
    exact ((contDiffOn_apply ℝ ℝ j Set.univ).comp hrow
      (by intro z hz; exact Set.mem_univ _)).continuousOn.mono hKV
  choose ca hca using fun i j =>
    (isCompact_scalarParabolicClosedCylinder r₀ r₁ hΩbounded).exists_bound_of_continuousOn
      (haCont i j)
  let Ca : Fin d → Fin d → ℝ := fun i j => max (ca i j) 0
  have hCa (i j : Fin d) : 0 ≤ Ca i j := le_max_right _ _
  have hCaBound (τ : Set.Icc 0 (r₁ - r₀)) (i j : Fin d) :
      ∀ᵐ y ∂PDE.volumeOn Ω, ‖a (r₁ - τ.1) y i j‖ ≤ Ca i j := by
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with y hy
    have htime : r₀ ≤ r₁ - τ.1 ∧ r₁ - τ.1 ≤ r₁ := by
      constructor <;> linarith [τ.2.1, τ.2.2]
    exact (hca i j (r₁ - τ.1, y) ⟨htime, subset_closure hy⟩).trans (le_max_left _ _)
  have hCdCont (j : Fin d) : ContinuousOn
      (fun z : TimeVelocity d => scalarSpatialCoefficientDivergence a z j - b z.1 z.2 j)
      (scalarParabolicClosedCylinder r₀ r₁ Ω) := by
    have hdiv := continuousOn_scalarSpatialCoefficientDivergence_of_smoothOnNeighborhood
      r₀ r₁ a haSmooth
    have heval : ContinuousOn (fun x : PDE.Vec d => x j) Set.univ :=
      (continuous_apply j).continuousOn
    rcases hbSmooth with ⟨V, hVopen, hKV, hV⟩
    have hbj : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => b z.1 z.2 j) V := by
      exact (contDiffOn_apply ℝ ℝ j Set.univ).comp hV (by intro z hz; exact Set.mem_univ _)
    exact heval.comp hdiv (by intro z hz; exact Set.mem_univ _) |>.sub (hbj.continuousOn.mono hKV)
  choose cd hcd using fun j =>
    (isCompact_scalarParabolicClosedCylinder r₀ r₁ hΩbounded).exists_bound_of_continuousOn
      (hCdCont j)
  let Cd : Fin d → ℝ := fun j => max (cd j) 0
  have hCd (j : Fin d) : 0 ≤ Cd j := le_max_right _ _
  have hCdBound (τ : Set.Icc 0 (r₁ - r₀)) (j : Fin d) :
      ∀ᵐ y ∂PDE.volumeOn Ω,
        ‖reverseTimeDivergenceDrift r₁ a b τ.1 y j‖ ≤ Cd j := by
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with y hy
    have htime : r₀ ≤ r₁ - τ.1 ∧ r₁ - τ.1 ≤ r₁ := by
      constructor <;> linarith [τ.2.1, τ.2.2]
    simpa only [reverseTimeDivergenceDrift,
      scalarSpatialCoefficientDivergence_reverseTimeCoefficient,
      reverseTimeMap_apply, reverseTimeVectorCoefficient_apply, Pi.sub_apply] using
      (hcd j (r₁ - τ.1, y) ⟨htime, subset_closure hy⟩).trans (le_max_left _ _)
  obtain ⟨Cc, hCc, hCcBound⟩ :=
    exists_reverseTimeScalarCoefficient_bound_of_smoothOnNeighborhood r₀ r₁ hΩbounded c hcSmooth
  refine ⟨Ca, Cd, Cc, hCa, hCd, hCc, ?_, hCaBound, ?_, hCdBound, ?_, ?_⟩
  · intro τ i j
    exact ContinuousOn.aestronglyMeasurable
      (continuousOn_reverseTimeCoefficientEntry_slice r₀ r₁ τ.1 a i j haSmooth τ.2)
      hΩ.measurableSet
  · intro τ j
    exact (continuousOn_reverseTimeDivergenceDriftEntry_slice r₀ r₁ τ.1 a b j haSmooth hbSmooth
      τ.2).aestronglyMeasurable hΩ.measurableSet
  · intro τ
    exact (continuousOn_reverseTimeScalarCoefficient_slice_of_smoothOnNeighborhood r₀ r₁ τ.1 c
      hcSmooth τ.2).aestronglyMeasurable hΩ.measurableSet
  · intro τ
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with y hy
    simpa only [Real.norm_eq_abs] using hCcBound τ.1 τ.2 y hy

/-- Multiplier inner-product expression for the reverse-time spatial form. -/
noncomputable def reverseTimeSpatialFormMultiplierExpression
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (r₀ r₁ : ℝ) (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (Ca : Fin d → Fin d → ℝ) (hCa : ∀ i j, 0 ≤ Ca i j)
    (hAMeas : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ i j,
      AEStronglyMeasurable (fun y => a (r₁ - τ.1) y i j) (PDE.volumeOn Ω))
    (hABound : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ i j,
      ∀ᵐ y ∂PDE.volumeOn Ω, ‖a (r₁ - τ.1) y i j‖ ≤ Ca i j)
    (Cd : Fin d → ℝ) (hCd : ∀ j, 0 ≤ Cd j)
    (hDriftMeas : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ j,
      AEStronglyMeasurable
        (fun y => reverseTimeDivergenceDrift r₁ a b τ.1 y j) (PDE.volumeOn Ω))
    (hDriftBound : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ j,
      ∀ᵐ y ∂PDE.volumeOn Ω, ‖reverseTimeDivergenceDrift r₁ a b τ.1 y j‖ ≤ Cd j)
    (Cc : ℝ) (hCc : 0 ≤ Cc)
    (hScalarMeas : ∀ τ : Set.Icc 0 (r₁ - r₀),
      AEStronglyMeasurable
        (fun y => reverseTimeScalarCoefficient r₁ c τ.1 y) (PDE.volumeOn Ω))
    (hScalarBound : ∀ τ : Set.Icc 0 (r₁ - r₀),
      ∀ᵐ y ∂PDE.volumeOn Ω, ‖reverseTimeScalarCoefficient r₁ c τ.1 y‖ ≤ Cc)
    (τ : Set.Icc 0 (r₁ - r₀)) (u v : H10HilbertGraph hΩ) : ℝ :=
  (∑ i : Fin d, ∑ j : Fin d,
    inner ℝ
      (scalarL2Multiplier (fun y => a (r₁ - τ.1) y i j)
        (hAMeas τ i j) (Ca i j) (hCa i j) (hABound τ i j)
        (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u)))
      (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i (gradientCLM hΩ v))) +
    (∑ j : Fin d,
      inner ℝ
        (scalarL2Multiplier (fun y => reverseTimeDivergenceDrift r₁ a b τ.1 y j)
          (hDriftMeas τ j) (Cd j) (hCd j) (hDriftBound τ j)
          (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u)))
        (valueCLM hΩ v)) -
    inner ℝ
      (scalarL2Multiplier (fun y => reverseTimeScalarCoefficient r₁ c τ.1 y)
        (hScalarMeas τ) Cc hCc (hScalarBound τ) (valueCLM hΩ u))
      (valueCLM hΩ v)

private theorem reverseTimeSpatialForm_eq_multiplierExpression
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (r₀ r₁ : ℝ) (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (Ca : Fin d → Fin d → ℝ) (hCa : ∀ i j, 0 ≤ Ca i j)
    (hAMeas : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ i j,
      AEStronglyMeasurable (fun y => a (r₁ - τ.1) y i j) (PDE.volumeOn Ω))
    (hABound : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ i j,
      ∀ᵐ y ∂PDE.volumeOn Ω, ‖a (r₁ - τ.1) y i j‖ ≤ Ca i j)
    (Cd : Fin d → ℝ) (hCd : ∀ j, 0 ≤ Cd j)
    (hDriftMeas : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ j,
      AEStronglyMeasurable
        (fun y => reverseTimeDivergenceDrift r₁ a b τ.1 y j) (PDE.volumeOn Ω))
    (hDriftBound : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ j,
      ∀ᵐ y ∂PDE.volumeOn Ω, ‖reverseTimeDivergenceDrift r₁ a b τ.1 y j‖ ≤ Cd j)
    (Cc : ℝ) (hCc : 0 ≤ Cc)
    (hScalarMeas : ∀ τ : Set.Icc 0 (r₁ - r₀),
      AEStronglyMeasurable
        (fun y => reverseTimeScalarCoefficient r₁ c τ.1 y) (PDE.volumeOn Ω))
    (hScalarBound : ∀ τ : Set.Icc 0 (r₁ - r₀),
      ∀ᵐ y ∂PDE.volumeOn Ω, ‖reverseTimeScalarCoefficient r₁ c τ.1 y‖ ≤ Cc)
    (τ : Set.Icc 0 (r₁ - r₀)) (u v : H10HilbertGraph hΩ) :
    reverseTimeSpatialForm hΩ r₁ τ.1 a b c u v =
      reverseTimeSpatialFormMultiplierExpression hΩ r₀ r₁ a b c Ca hCa hAMeas hABound Cd hCd
        hDriftMeas hDriftBound Cc hCc hScalarMeas hScalarBound τ u v := by
  exact reverseTimeSpatialForm_eq_multiplierInner_of_sliceEvidence hΩ r₁ τ.1 a b c u v
    Ca hCa (hAMeas τ) (hABound τ) Cd hCd (hDriftMeas τ) (hDriftBound τ) Cc hCc
    (hScalarMeas τ) (hScalarBound τ)

/-- The reverse-time spatial form as a bounded bilinear map. -/
noncomputable def reverseTimeSpatialFormBilinear
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (r₀ r₁ : ℝ) (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (Ca : Fin d → Fin d → ℝ) (hCa : ∀ i j, 0 ≤ Ca i j)
    (hAMeas : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ i j,
      AEStronglyMeasurable (fun y => a (r₁ - τ.1) y i j) (PDE.volumeOn Ω))
    (hABound : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ i j,
      ∀ᵐ y ∂PDE.volumeOn Ω, ‖a (r₁ - τ.1) y i j‖ ≤ Ca i j)
    (Cd : Fin d → ℝ) (hCd : ∀ j, 0 ≤ Cd j)
    (hDriftMeas : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ j,
      AEStronglyMeasurable
        (fun y => reverseTimeDivergenceDrift r₁ a b τ.1 y j) (PDE.volumeOn Ω))
    (hDriftBound : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ j,
      ∀ᵐ y ∂PDE.volumeOn Ω, ‖reverseTimeDivergenceDrift r₁ a b τ.1 y j‖ ≤ Cd j)
    (Cc : ℝ) (hCc : 0 ≤ Cc)
    (hScalarMeas : ∀ τ : Set.Icc 0 (r₁ - r₀),
      AEStronglyMeasurable
        (fun y => reverseTimeScalarCoefficient r₁ c τ.1 y) (PDE.volumeOn Ω))
    (hScalarBound : ∀ τ : Set.Icc 0 (r₁ - r₀),
      ∀ᵐ y ∂PDE.volumeOn Ω, ‖reverseTimeScalarCoefficient r₁ c τ.1 y‖ ≤ Cc)
    (τ : Set.Icc 0 (r₁ - r₀)) :
    H10HilbertGraph hΩ →ₗ[ℝ] H10HilbertGraph hΩ →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (reverseTimeSpatialFormMultiplierExpression hΩ r₀ r₁ a b c Ca hCa hAMeas hABound Cd hCd
      hDriftMeas hDriftBound Cc hCc hScalarMeas hScalarBound τ)
    (by
      intro u w v
      simp only [reverseTimeSpatialFormMultiplierExpression, map_add, inner_add_left,
        Finset.sum_add_distrib]
      ring)
    (by
      intro q u v
      simp only [reverseTimeSpatialFormMultiplierExpression, map_smul, inner_smul_left,
        starRingEnd_apply, star_trivial, smul_eq_mul]
      simp_rw [← Finset.mul_sum]
      ring)
    (by
      intro u v w
      simp only [reverseTimeSpatialFormMultiplierExpression, map_add, inner_add_right,
        Finset.sum_add_distrib]
      ring)
    (by
      intro q u v
      simp only [reverseTimeSpatialFormMultiplierExpression, map_smul, inner_smul_right,
        smul_eq_mul]
      simp_rw [← Finset.mul_sum]
      ring)

/-- The reverse-time spatial form as a continuous operator at a local time. -/
noncomputable def reverseTimeSpatialFormOperator
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (τ : Set.Icc 0 (r₁ - r₀)) :
    H10HilbertGraph hΩ →L[ℝ] H10HilbertGraphDual hΩ := by
  let hEvidence := exists_sliceMultiplierBounds_of_smoothOnNeighborhood r₀ r₁ hΩ hΩbounded
    a b c haSmooth hbSmooth hcSmooth
  let Ca := Classical.choose hEvidence
  let hCaRest := Classical.choose_spec hEvidence
  let Cd := Classical.choose hCaRest
  let hCdRest := Classical.choose_spec hCaRest
  let Cc := Classical.choose hCdRest
  let hEvidenceData := Classical.choose_spec hCdRest
  let hCa := hEvidenceData.1
  let hCd := hEvidenceData.2.1
  let hCc := hEvidenceData.2.2.1
  let hAMeas := hEvidenceData.2.2.2.1
  let hABound := hEvidenceData.2.2.2.2.1
  let hDriftMeas := hEvidenceData.2.2.2.2.2.1
  let hDriftBound := hEvidenceData.2.2.2.2.2.2.1
  let hScalarMeas := hEvidenceData.2.2.2.2.2.2.2.1
  let hScalarBound := hEvidenceData.2.2.2.2.2.2.2.2
  let hBound := reverseTimeSpatialForm_bounded_of_smoothOnNeighborhood r₀ r₁ h₀₁ hΩ hΩbounded
    a b c haSmooth hbSmooth hcSmooth
  let C := Classical.choose hBound
  let hCData := Classical.choose_spec hBound
  exact LinearMap.mkContinuous₂
    (reverseTimeSpatialFormBilinear hΩ r₀ r₁ a b c Ca hCa hAMeas hABound Cd hCd hDriftMeas
      hDriftBound Cc hCc hScalarMeas hScalarBound τ)
    C
    (fun u v => by
      change ‖reverseTimeSpatialFormMultiplierExpression hΩ r₀ r₁ a b c Ca hCa hAMeas hABound
        Cd hCd hDriftMeas hDriftBound Cc hCc hScalarMeas hScalarBound τ u v‖ ≤
          C * ‖u‖ * ‖v‖
      rw [← reverseTimeSpatialForm_eq_multiplierExpression hΩ r₀ r₁ a b c Ca hCa hAMeas hABound
        Cd hCd hDriftMeas hDriftBound Cc hCc hScalarMeas hScalarBound τ u v,
        Real.norm_eq_abs]
      exact hCData.2 τ.1 τ.2 u v)

/-- The local operator evaluates to the literal reverse-time spatial form. -/
theorem reverseTimeSpatialFormOperator_apply
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (τ : Set.Icc 0 (r₁ - r₀)) (u v : H10HilbertGraph hΩ) :
    reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth τ u v =
      reverseTimeSpatialForm hΩ r₁ τ.1 a b c u v := by
  unfold reverseTimeSpatialFormOperator
  obtain ⟨Ca, Cd, Cc, hCa, hCd, hCc, hAMeas, hABound, hDriftMeas, hDriftBound,
    hScalarMeas, hScalarBound⟩ :=
    exists_sliceMultiplierBounds_of_smoothOnNeighborhood r₀ r₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth
  obtain ⟨C, hC, hForm⟩ :=
    reverseTimeSpatialForm_bounded_of_smoothOnNeighborhood r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth
  rw [LinearMap.mkContinuous₂_apply]
  exact (reverseTimeSpatialForm_eq_multiplierExpression hΩ r₀ r₁ a b c Ca hCa hAMeas hABound Cd hCd
    hDriftMeas hDriftBound Cc hCc hScalarMeas hScalarBound τ u v).symm

/-- The local operator curve has one time-uniform application bound. -/
theorem exists_reverseTimeSpatialFormOperator_bound
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ u : H10HilbertGraph hΩ,
        ‖reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth τ u‖ ≤ C * ‖u‖ := by
  obtain ⟨C, hC, hForm⟩ :=
    reverseTimeSpatialForm_bounded_of_smoothOnNeighborhood r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth
  refine ⟨C, hC, ?_⟩
  intro τ u
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC (norm_nonneg _))
  intro v
  rw [Real.norm_eq_abs, reverseTimeSpatialFormOperator_apply]
  exact hForm τ.1 τ.2 u v


end HypoellipticAleksandrov.Parabolic.Dirichlet
