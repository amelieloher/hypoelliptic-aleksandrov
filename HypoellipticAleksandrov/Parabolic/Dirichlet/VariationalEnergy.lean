module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormBounds
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeHilbertIntegrationByParts
public import HypoellipticAleksandrov.Parabolic.Dirichlet.WeakTimeDerivativeUnique
public import HypoellipticAleksandrov.Parabolic.Dirichlet.IntegralGronwall

/-!
# Reverse-time variational energy uniqueness

This file proves the literal difference-energy estimate and uniqueness for
reverse-time variational solutions of the homogeneous-lateral Dirichlet problem.
It does not construct solutions.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped ENNReal RealInnerProductSpace Matrix.Norms.Elementwise MatrixOrder

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

local instance instReverseTimeL2VStarModuleEnergy
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) :
    Module ℝ (ReverseTimeL2VStar hΩ T) :=
  MeasureTheory.Lp.instModule

/-- A literal common-event weak variational solution of the reversed,
homogeneous-lateral Dirichlet energy problem. -/
def IsReverseTimeVariationalEnergySolution
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c F : ℝ → PDE.Vec d → ℝ)
    (hFSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (u : ReverseTimeL2V hΩ (r₁ - r₀))
    (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀)
      (sub_pos.mpr h₀₁) u g) : Prop :=
  reverseTimeInitialTrace hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) u g hdu = initial ∧
  ∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀),
    ∀ hτ : τ ∈ Set.Ioo 0 (r₁ - r₀),
    ∀ v : H10HilbertGraph hΩ,
      (g τ) v + reverseTimeSpatialForm hΩ r₁ τ a b c (u τ) v =
        reverseTimeSourceFunctional hΩ
          (reverseTimeSourceSlice r₁ τ F
            (reverseTimeSourceSlice_memLp_of_smoothOnNeighborhood
              r₀ r₁ hΩ hΩbounded F hFSmooth τ
              ⟨le_of_lt hτ.1, le_of_lt hτ.2⟩)) v

/-- The literal closed-time Gårding difference-energy inequality. -/
def HasReverseTimeDifferenceEnergyBound
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ lam K : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω)
    (u : ReverseTimeL2V hΩ (r₁ - r₀))
    (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀)
      (sub_pos.mpr h₀₁) u g)
    (v : ReverseTimeL2V hΩ (r₁ - r₀))
    (k : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdv : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀)
      (sub_pos.mpr h₀₁) v k) : Prop :=
  ∀ s t : ℝ, ∀ hs : s ∈ Set.Icc 0 (r₁ - r₀),
    ∀ ht : t ∈ Set.Icc 0 (r₁ - r₀), s ≤ t →
      ‖reverseTimeHilbertRepresentative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁)
          u g hdu ⟨t, ht⟩ -
          reverseTimeHilbertRepresentative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁)
          v k hdv ⟨t, ht⟩‖ ^ 2 -
        ‖reverseTimeHilbertRepresentative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁)
          u g hdu ⟨s, hs⟩ -
          reverseTimeHilbertRepresentative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁)
          v k hdv ⟨s, hs⟩‖ ^ 2 +
        lam * (∫ τ in Set.Ioc s t,
          ‖gradientCLM hΩ (u τ - v τ)‖ ^ 2
            ∂reverseTimeVolume (r₁ - r₀)) ≤
      2 * K * (∫ τ in Set.Ioc s t,
        ‖valueCLM hΩ (u τ - v τ)‖ ^ 2
          ∂reverseTimeVolume (r₁ - r₀))

private theorem exists_reverseTimeSpatialForm_sliceEvidence_of_smoothOnNeighborhood
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (τ : ℝ) (hτ : τ ∈ Set.Icc 0 (r₁ - r₀)) :
    ∃ (Ca : Fin d → Fin d → ℝ) (Cd : Fin d → ℝ) (Cc : ℝ),
      (∀ i j, 0 ≤ Ca i j) ∧
      (∀ i j, AEStronglyMeasurable
        (fun y : PDE.Vec d => a (r₁ - τ) y i j) (PDE.volumeOn Ω)) ∧
      (∀ i j, ∀ᵐ y ∂PDE.volumeOn Ω,
        ‖a (r₁ - τ) y i j‖ ≤ Ca i j) ∧
      (∀ j, 0 ≤ Cd j) ∧
      (∀ j, AEStronglyMeasurable
        (fun y : PDE.Vec d => reverseTimeDivergenceDrift r₁ a b τ y j)
          (PDE.volumeOn Ω)) ∧
      (∀ j, ∀ᵐ y ∂PDE.volumeOn Ω,
        ‖reverseTimeDivergenceDrift r₁ a b τ y j‖ ≤ Cd j) ∧
      0 ≤ Cc ∧
      AEStronglyMeasurable
        (fun y : PDE.Vec d => reverseTimeScalarCoefficient r₁ c τ y)
        (PDE.volumeOn Ω) ∧
      (∀ᵐ y ∂PDE.volumeOn Ω,
        ‖reverseTimeScalarCoefficient r₁ c τ y‖ ≤ Cc) := by
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
  have hCaBound (i j : Fin d) : ∀ᵐ y ∂PDE.volumeOn Ω,
      ‖a (r₁ - τ) y i j‖ ≤ Ca i j := by
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with y hy
    have htime : r₀ ≤ r₁ - τ ∧ r₁ - τ ≤ r₁ := by
      constructor <;> linarith [hτ.1, hτ.2]
    exact (hca i j (r₁ - τ, y) ⟨htime, subset_closure hy⟩).trans (le_max_left _ _)
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
  have hCdBound (j : Fin d) : ∀ᵐ y ∂PDE.volumeOn Ω,
      ‖reverseTimeDivergenceDrift r₁ a b τ y j‖ ≤ Cd j := by
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with y hy
    have htime : r₀ ≤ r₁ - τ ∧ r₁ - τ ≤ r₁ := by
      constructor <;> linarith [hτ.1, hτ.2]
    simpa only [reverseTimeDivergenceDrift,
      scalarSpatialCoefficientDivergence_reverseTimeCoefficient,
      reverseTimeMap_apply, reverseTimeVectorCoefficient_apply, Pi.sub_apply] using
      (hcd j (r₁ - τ, y) ⟨htime, subset_closure hy⟩).trans (le_max_left _ _)
  obtain ⟨Cc, hCc, hCcBound⟩ :=
    exists_reverseTimeScalarCoefficient_bound_of_smoothOnNeighborhood r₀ r₁ hΩbounded c hcSmooth
  refine ⟨Ca, Cd, Cc, hCa, ?_, hCaBound, hCd, ?_, hCdBound, hCc, ?_, ?_⟩
  · intro i j
    rcases haSmooth with ⟨V, hVopen, hKV, hV⟩
    have hrow : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => a z.1 z.2 i) V := by
      exact (contDiffOn_apply ℝ (Fin d → ℝ) i Set.univ).comp hV
        (by intro z hz; exact Set.mem_univ _)
    have hentry : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => a z.1 z.2 i j) V := by
      exact (contDiffOn_apply ℝ ℝ j Set.univ).comp hrow (by intro z hz; exact Set.mem_univ _)
    have htime : r₀ ≤ r₁ - τ ∧ r₁ - τ ≤ r₁ := by
      constructor <;> linarith [hτ.1, hτ.2]
    have hmap : MapsTo (fun y : PDE.Vec d => (r₁ - τ, y)) Ω
        (scalarParabolicClosedCylinder r₀ r₁ Ω) := by
      intro y hy
      exact ⟨htime, subset_closure hy⟩
    have hslice : ContinuousOn (fun y : PDE.Vec d => a (r₁ - τ) y i j) Ω := by
      simpa only [Function.comp_def] using (hentry.continuousOn.mono hKV).comp
        (Continuous.prodMk_right _).continuousOn hmap
    exact hslice.aestronglyMeasurable hΩ.measurableSet
  · intro j
    have htime : r₀ ≤ r₁ - τ ∧ r₁ - τ ≤ r₁ := by
      constructor <;> linarith [hτ.1, hτ.2]
    have hmap : MapsTo (fun y : PDE.Vec d => (r₁ - τ, y)) Ω
        (scalarParabolicClosedCylinder r₀ r₁ Ω) := by
      intro y hy
      exact ⟨htime, subset_closure hy⟩
    have hdiv : ContinuousOn (fun y : PDE.Vec d =>
        scalarSpatialCoefficientDivergence (reverseTimeCoefficient r₁ a) (τ, y) j) Ω := by
      have hcont := continuousOn_scalarSpatialCoefficientDivergence_of_smoothOnNeighborhood
        r₀ r₁ a haSmooth
      have hvec : ContinuousOn (fun y : PDE.Vec d =>
          scalarSpatialCoefficientDivergence a (r₁ - τ, y)) Ω := by
        simpa only [Function.comp_def] using
          hcont.comp (Continuous.prodMk_right _).continuousOn hmap
      have heval : ContinuousOn (fun x : PDE.Vec d => x j) Set.univ :=
        (continuous_apply j).continuousOn
      simpa only [scalarSpatialCoefficientDivergence_reverseTimeCoefficient,
        reverseTimeMap_apply, Function.comp_def] using heval.comp hvec (by intro y hy; simp)
    rcases hbSmooth with ⟨V, hVopen, hKV, hV⟩
    have hentry : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => b z.1 z.2 j) V := by
      exact (contDiffOn_apply ℝ ℝ j Set.univ).comp hV (by intro z hz; exact Set.mem_univ _)
    have hbcont : ContinuousOn (fun y : PDE.Vec d => b (r₁ - τ) y j) Ω := by
      simpa only [Function.comp_def] using (hentry.continuousOn.mono hKV).comp
        (Continuous.prodMk_right _).continuousOn hmap
    have hslice : ContinuousOn
        (fun y : PDE.Vec d => reverseTimeDivergenceDrift r₁ a b τ y j) Ω := by
      simpa only [reverseTimeDivergenceDrift, reverseTimeVectorCoefficient_apply,
        Pi.sub_def] using hdiv.sub hbcont
    exact hslice.aestronglyMeasurable hΩ.measurableSet
  · exact (continuousOn_reverseTimeScalarCoefficient_slice_of_smoothOnNeighborhood
      r₀ r₁ τ c hcSmooth hτ).aestronglyMeasurable hΩ.measurableSet
  · filter_upwards [ae_restrict_mem hΩ.measurableSet] with y hy
    simpa only [Real.norm_eq_abs] using hCcBound τ hτ y hy

private noncomputable def reverseTimeSpatialFormMultiplierExpression
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (r₁ τ : ℝ) (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (Ca : Fin d → Fin d → ℝ) (Cd : Fin d → ℝ) (Cc : ℝ)
    (hCa : ∀ i j, 0 ≤ Ca i j)
    (hAMeas : ∀ i j, AEStronglyMeasurable
      (fun y : PDE.Vec d => a (r₁ - τ) y i j) (PDE.volumeOn Ω))
    (hABound : ∀ i j, ∀ᵐ y ∂PDE.volumeOn Ω, ‖a (r₁ - τ) y i j‖ ≤ Ca i j)
    (hCd : ∀ j, 0 ≤ Cd j)
    (hDriftMeas : ∀ j, AEStronglyMeasurable
      (fun y : PDE.Vec d => reverseTimeDivergenceDrift r₁ a b τ y j) (PDE.volumeOn Ω))
    (hDriftBound : ∀ j, ∀ᵐ y ∂PDE.volumeOn Ω,
      ‖reverseTimeDivergenceDrift r₁ a b τ y j‖ ≤ Cd j)
    (hCc : 0 ≤ Cc)
    (hScalarMeas : AEStronglyMeasurable
      (fun y : PDE.Vec d => reverseTimeScalarCoefficient r₁ c τ y) (PDE.volumeOn Ω))
    (hScalarBound : ∀ᵐ y ∂PDE.volumeOn Ω,
      ‖reverseTimeScalarCoefficient r₁ c τ y‖ ≤ Cc)
    (u v : H10HilbertGraph hΩ) : ℝ :=
  (∑ i : Fin d, ∑ j : Fin d,
    inner ℝ
      (scalarL2Multiplier (fun y : PDE.Vec d => a (r₁ - τ) y i j)
        (hAMeas i j) (Ca i j) (hCa i j) (hABound i j)
        (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u)))
      (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i (gradientCLM hΩ v))) +
    (∑ j : Fin d,
      inner ℝ
        (scalarL2Multiplier (fun y : PDE.Vec d => reverseTimeDivergenceDrift r₁ a b τ y j)
          (hDriftMeas j) (Cd j) (hCd j) (hDriftBound j)
          (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u)))
        (valueCLM hΩ v)) -
    inner ℝ
      (scalarL2Multiplier (fun y : PDE.Vec d => reverseTimeScalarCoefficient r₁ c τ y)
        hScalarMeas Cc hCc hScalarBound (valueCLM hΩ u))
      (valueCLM hΩ v)

private theorem reverseTimeSpatialForm_eq_multiplierExpression
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (r₁ τ : ℝ) (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (Ca : Fin d → Fin d → ℝ) (Cd : Fin d → ℝ) (Cc : ℝ)
    (hCa : ∀ i j, 0 ≤ Ca i j)
    (hAMeas : ∀ i j, AEStronglyMeasurable
      (fun y : PDE.Vec d => a (r₁ - τ) y i j) (PDE.volumeOn Ω))
    (hABound : ∀ i j, ∀ᵐ y ∂PDE.volumeOn Ω, ‖a (r₁ - τ) y i j‖ ≤ Ca i j)
    (hCd : ∀ j, 0 ≤ Cd j)
    (hDriftMeas : ∀ j, AEStronglyMeasurable
      (fun y : PDE.Vec d => reverseTimeDivergenceDrift r₁ a b τ y j) (PDE.volumeOn Ω))
    (hDriftBound : ∀ j, ∀ᵐ y ∂PDE.volumeOn Ω,
      ‖reverseTimeDivergenceDrift r₁ a b τ y j‖ ≤ Cd j)
    (hCc : 0 ≤ Cc)
    (hScalarMeas : AEStronglyMeasurable
      (fun y : PDE.Vec d => reverseTimeScalarCoefficient r₁ c τ y) (PDE.volumeOn Ω))
    (hScalarBound : ∀ᵐ y ∂PDE.volumeOn Ω,
      ‖reverseTimeScalarCoefficient r₁ c τ y‖ ≤ Cc)
    (u v : H10HilbertGraph hΩ) :
    reverseTimeSpatialForm hΩ r₁ τ a b c u v =
      reverseTimeSpatialFormMultiplierExpression hΩ r₁ τ a b c Ca Cd Cc hCa hAMeas hABound
        hCd hDriftMeas hDriftBound hCc hScalarMeas hScalarBound u v := by
  exact reverseTimeSpatialForm_eq_multiplierInner_of_sliceEvidence hΩ r₁ τ a b c u v
    Ca hCa hAMeas hABound Cd hCd hDriftMeas hDriftBound Cc hCc hScalarMeas hScalarBound

private theorem reverseTimeSpatialForm_sub_left_of_sliceEvidence
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (r₁ τ : ℝ) (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (Ca : Fin d → Fin d → ℝ) (Cd : Fin d → ℝ) (Cc : ℝ)
    (hCa : ∀ i j, 0 ≤ Ca i j)
    (hAMeas : ∀ i j, AEStronglyMeasurable
      (fun y : PDE.Vec d => a (r₁ - τ) y i j) (PDE.volumeOn Ω))
    (hABound : ∀ i j, ∀ᵐ y ∂PDE.volumeOn Ω, ‖a (r₁ - τ) y i j‖ ≤ Ca i j)
    (hCd : ∀ j, 0 ≤ Cd j)
    (hDriftMeas : ∀ j, AEStronglyMeasurable
      (fun y : PDE.Vec d => reverseTimeDivergenceDrift r₁ a b τ y j) (PDE.volumeOn Ω))
    (hDriftBound : ∀ j, ∀ᵐ y ∂PDE.volumeOn Ω,
      ‖reverseTimeDivergenceDrift r₁ a b τ y j‖ ≤ Cd j)
    (hCc : 0 ≤ Cc)
    (hScalarMeas : AEStronglyMeasurable
      (fun y : PDE.Vec d => reverseTimeScalarCoefficient r₁ c τ y) (PDE.volumeOn Ω))
    (hScalarBound : ∀ᵐ y ∂PDE.volumeOn Ω,
      ‖reverseTimeScalarCoefficient r₁ c τ y‖ ≤ Cc)
    (u₁ u₂ v : H10HilbertGraph hΩ) :
    reverseTimeSpatialForm hΩ r₁ τ a b c (u₁ - u₂) v =
      reverseTimeSpatialForm hΩ r₁ τ a b c u₁ v -
        reverseTimeSpatialForm hΩ r₁ τ a b c u₂ v := by
  rw [reverseTimeSpatialForm_eq_multiplierExpression hΩ r₁ τ a b c Ca Cd Cc hCa hAMeas hABound
        hCd hDriftMeas hDriftBound hCc hScalarMeas hScalarBound,
      reverseTimeSpatialForm_eq_multiplierExpression hΩ r₁ τ a b c Ca Cd Cc hCa hAMeas hABound
        hCd hDriftMeas hDriftBound hCc hScalarMeas hScalarBound,
      reverseTimeSpatialForm_eq_multiplierExpression hΩ r₁ τ a b c Ca Cd Cc hCa hAMeas hABound
        hCd hDriftMeas hDriftBound hCc hScalarMeas hScalarBound]
  simp only [reverseTimeSpatialFormMultiplierExpression, ContinuousLinearMap.map_sub,
    inner_sub_left, Finset.sum_sub_distrib]
  ring

private theorem reverseTimeSpatialForm_sub_left_of_smoothOnNeighborhood
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (τ : ℝ) (hτ : τ ∈ Set.Icc 0 (r₁ - r₀))
    (u₁ u₂ v : H10HilbertGraph hΩ) :
    reverseTimeSpatialForm hΩ r₁ τ a b c (u₁ - u₂) v =
      reverseTimeSpatialForm hΩ r₁ τ a b c u₁ v -
        reverseTimeSpatialForm hΩ r₁ τ a b c u₂ v := by
  obtain ⟨Ca, Cd, Cc, hCa, hAMeas, hABound, hCd, hDriftMeas, hDriftBound,
    hCc, hScalarMeas, hScalarBound⟩ :=
    exists_reverseTimeSpatialForm_sliceEvidence_of_smoothOnNeighborhood
      r₀ r₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth τ hτ
  exact reverseTimeSpatialForm_sub_left_of_sliceEvidence hΩ r₁ τ a b c Ca Cd Cc hCa hAMeas
    hABound hCd hDriftMeas hDriftBound hCc hScalarMeas hScalarBound u₁ u₂ v

private theorem reverseTimeSpatialForm_sub_left_diagonal_of_smoothOnNeighborhood
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (τ : ℝ) (hτ : τ ∈ Set.Icc 0 (r₁ - r₀))
    (u v : H10HilbertGraph hΩ) :
    reverseTimeSpatialForm hΩ r₁ τ a b c u (u - v) -
      reverseTimeSpatialForm hΩ r₁ τ a b c v (u - v) =
        reverseTimeSpatialForm hΩ r₁ τ a b c (u - v) (u - v) := by
  simpa using
    (reverseTimeSpatialForm_sub_left_of_smoothOnNeighborhood
      r₀ r₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth τ hτ u v (u - v)).symm

private theorem hasGelfandWeakTimeDerivative_sub
    {d : ℕ} {Ω : Set (PDE.Vec d)} {hΩ : IsOpen Ω} {T : ℝ} {hT : 0 < T}
    {u v : ReverseTimeL2V hΩ T} {g k : ReverseTimeL2VStar hΩ T}
    (hu : HasGelfandWeakTimeDerivative hΩ T hT u g)
    (hv : HasGelfandWeakTimeDerivative hΩ T hT v k) :
    HasGelfandWeakTimeDerivative hΩ T hT (u - v) (g - k) := by
  simpa [sub_eq_add_neg] using hu.add (hv.smul (-1 : ℝ))

private theorem ae_reverseTimeVariationalEnergy_difference_equation
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
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
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (u : ReverseTimeL2V hΩ (r₁ - r₀))
    (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) u g)
    (hu : IsReverseTimeVariationalEnergySolution r₀ r₁ h₀₁ hΩ hΩbounded
      a b c F hFSmooth initial u g hdu)
    (v : ReverseTimeL2V hΩ (r₁ - r₀))
    (k : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdv : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) v k)
    (hv : IsReverseTimeVariationalEnergySolution r₀ r₁ h₀₁ hΩ hΩbounded
      a b c F hFSmooth initial v k hdv) :
    ∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀),
      ∀ _hτ : τ ∈ Set.Ioo 0 (r₁ - r₀),
        ((g - k) τ) ((u - v) τ) + reverseTimeSpatialForm hΩ r₁ τ a b c
          ((u - v) τ) ((u - v) τ) = 0 := by
  rcases hu with ⟨_, huEq⟩
  rcases hv with ⟨_, hvEq⟩
  filter_upwards [huEq, hvEq, Lp.coeFn_sub u v, Lp.coeFn_sub g k] with τ huτ hvτ huv hgk
  intro hτ
  have hτcc : τ ∈ Set.Icc 0 (r₁ - r₀) := ⟨le_of_lt hτ.1, le_of_lt hτ.2⟩
  have huTest := huτ hτ (u τ - v τ)
  have hvTest := hvτ hτ (u τ - v τ)
  have hform := reverseTimeSpatialForm_sub_left_diagonal_of_smoothOnNeighborhood
    r₀ r₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth τ hτcc (u τ) (v τ)
  rw [huv, hgk]
  change ((g τ - k τ) (u τ - v τ)) +
    reverseTimeSpatialForm hΩ r₁ τ a b c (u τ - v τ) (u τ - v τ) = 0
  rw [ContinuousLinearMap.sub_apply]
  linarith

private theorem reverseTimeHilbertRepresentative_sub_eq
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hdu : HasGelfandWeakTimeDerivative hΩ T hT u g)
    (v : ReverseTimeL2V hΩ T) (k : ReverseTimeL2VStar hΩ T)
    (hdv : HasGelfandWeakTimeDerivative hΩ T hT v k)
    (hdiff : HasGelfandWeakTimeDerivative hΩ T hT (u - v) (g - k)) :
    reverseTimeHilbertRepresentative hΩ T hT (u - v) (g - k) hdiff =
      reverseTimeHilbertRepresentative hΩ T hT u g hdu -
        reverseTimeHilbertRepresentative hΩ T hT v k hdv := by
  obtain ⟨hU, _⟩ := reverseTimeHilbertRepresentative_spec hΩ T hT u g hdu
  obtain ⟨hV, _⟩ := reverseTimeHilbertRepresentative_spec hΩ T hT v k hdv
  obtain ⟨hW, _⟩ := reverseTimeHilbertRepresentative_spec hΩ T hT (u - v) (g - k) hdiff
  apply ReverseTimeHilbertRepresentativeAgrees.unique hW hT
  filter_upwards [hU, hV, Lp.coeFn_sub u v] with τ hUτ hVτ huv
  intro hτ
  let hτcc : τ ∈ Set.Icc 0 T := ⟨le_of_lt hτ.1, le_of_lt hτ.2⟩
  change
    (reverseTimeHilbertRepresentative hΩ T hT u g hdu -
      reverseTimeHilbertRepresentative hΩ T hT v k hdv) ⟨τ, hτcc⟩ =
      valueCLM hΩ ((u - v) τ)
  change reverseTimeHilbertRepresentative hΩ T hT u g hdu ⟨τ, hτcc⟩ -
      reverseTimeHilbertRepresentative hΩ T hT v k hdv ⟨τ, hτcc⟩ =
        valueCLM hΩ ((u - v) τ)
  rw [hUτ hτ, hVτ hτ, huv]
  exact (valueCLM hΩ).map_sub _ _

private theorem setIntegral_garding_of_ae
    {μ : Measure ℝ} (p G V : ℝ → ℝ) (lam K s t : ℝ)
    (hp : Integrable p μ) (hG : Integrable G μ) (hV : Integrable V μ)
    (hae : ∀ᵐ r ∂μ, 2 * p r + lam * G r ≤ 2 * K * V r) :
    2 * (∫ r in Set.Ioc s t, p r ∂μ) + lam * (∫ r in Set.Ioc s t, G r ∂μ) ≤
      2 * K * (∫ r in Set.Ioc s t, V r ∂μ) := by
  have hl : Integrable (fun r => 2 * p r + lam * G r) μ :=
    (hp.const_mul 2).add (hG.const_mul lam)
  have hr : Integrable (fun r => 2 * K * V r) μ := by
    simpa only [mul_assoc] using hV.const_mul (2 * K)
  have h := setIntegral_mono_ae_restrict hl.integrableOn hr.integrableOn
    (ae_restrict_of_ae hae : ∀ᵐ r ∂μ.restrict (Set.Ioc s t),
      2 * p r + lam * G r ≤ 2 * K * V r)
  rw [integral_add (hp.const_mul 2).restrict (hG.const_mul lam).restrict,
    integral_const_mul, integral_const_mul, integral_const_mul] at h
  exact h

private theorem hasReverseTimeDifferenceEnergyBound_of_pointwise
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ lam K : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω)
    (u : ReverseTimeL2V hΩ (r₁ - r₀)) (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) u g)
    (v : ReverseTimeL2V hΩ (r₁ - r₀)) (k : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdv : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) v k)
    (hdiff : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) (u - v) (g - k))
    (hpoint : ∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀),
      2 * ((g - k) τ) ((u - v) τ) + lam * ‖gradientCLM hΩ ((u - v) τ)‖ ^ 2 ≤
        2 * K * ‖valueCLM hΩ ((u - v) τ)‖ ^ 2) :
    HasReverseTimeDifferenceEnergyBound r₀ r₁ lam K h₀₁ hΩ u g hdu v k hdv := by
  intro s t hs ht hst
  have hrep := reverseTimeHilbertRepresentative_sub_eq hΩ (r₁ - r₀) (sub_pos.mpr h₀₁)
    u g hdu v k hdv hdiff
  have henergy := (reverseTimeHilbertRepresentative_spec hΩ (r₁ - r₀) (sub_pos.mpr h₀₁)
    (u - v) (g - k) hdiff).2 s t hs ht hst
  have hpair : Integrable (fun τ => ((g - k) τ) ((u - v) τ))
      (reverseTimeVolume (r₁ - r₀)) :=
    integrable_reverseTimeDualPairing hΩ (r₁ - r₀) (u - v) (g - k)
  have hgradMem : MemLp (fun τ => gradientCLM hΩ ((u - v) τ)) (2 : ℝ≥0∞)
      (reverseTimeVolume (r₁ - r₀)) :=
    (Lp.memLp (u - v)).continuousLinearMap_comp (gradientCLM hΩ)
  have hvalueMem : MemLp (fun τ => valueCLM hΩ ((u - v) τ)) (2 : ℝ≥0∞)
      (reverseTimeVolume (r₁ - r₀)) :=
    (Lp.memLp (u - v)).continuousLinearMap_comp (valueCLM hΩ)
  have hgrad : Integrable (fun τ => ‖gradientCLM hΩ ((u - v) τ)‖ ^ 2)
      (reverseTimeVolume (r₁ - r₀)) :=
    (memLp_two_iff_integrable_sq_norm hgradMem.aestronglyMeasurable).mp hgradMem
  have hvalue : Integrable (fun τ => ‖valueCLM hΩ ((u - v) τ)‖ ^ 2)
      (reverseTimeVolume (r₁ - r₀)) :=
    (memLp_two_iff_integrable_sq_norm hvalueMem.aestronglyMeasurable).mp hvalueMem
  have hint := setIntegral_garding_of_ae
    (fun τ => ((g - k) τ) ((u - v) τ))
    (fun τ => ‖gradientCLM hΩ ((u - v) τ)‖ ^ 2)
    (fun τ => ‖valueCLM hΩ ((u - v) τ)‖ ^ 2)
    lam K s t hpair hgrad hvalue hpoint
  have hgradIoc :
      (∫ τ in Set.Ioc s t, ‖gradientCLM hΩ ((u - v) τ)‖ ^ 2
        ∂reverseTimeVolume (r₁ - r₀)) =
      ∫ τ in Set.Ioc s t, ‖gradientCLM hΩ (u τ - v τ)‖ ^ 2
        ∂reverseTimeVolume (r₁ - r₀) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (Lp.coeFn_sub u v)] with τ hτ
    rw [hτ]
    simp only [Pi.sub_apply]
  have hvalueIoc :
      (∫ τ in Set.Ioc s t, ‖valueCLM hΩ ((u - v) τ)‖ ^ 2
        ∂reverseTimeVolume (r₁ - r₀)) =
      ∫ τ in Set.Ioc s t, ‖valueCLM hΩ (u τ - v τ)‖ ^ 2
        ∂reverseTimeVolume (r₁ - r₀) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (Lp.coeFn_sub u v)] with τ hτ
    rw [hτ]
    simp only [Pi.sub_apply]
  rw [hrep] at henergy
  change
    ‖reverseTimeHilbertRepresentative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) u g hdu ⟨t, ht⟩ -
        reverseTimeHilbertRepresentative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) v k hdv ⟨t, ht⟩‖ ^ 2 -
      ‖reverseTimeHilbertRepresentative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) u g hdu ⟨s, hs⟩ -
        reverseTimeHilbertRepresentative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) v k hdv ⟨s, hs⟩‖ ^ 2 =
      2 * (∫ r in Set.Ioc s t, ((g - k) r) ((u - v) r)
        ∂reverseTimeVolume (r₁ - r₀)) at henergy
  rw [hgradIoc, hvalueIoc] at hint
  rw [henergy]
  exact hint

/-- Smooth coefficient data supply a difference-energy constant before the
forcing, initial datum, solution curves, and time endpoints are chosen. -/
theorem exists_reverseTimeVariationalEnergy_difference_constant
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ lam : ℝ) (h₀₁ : r₀ < r₁) (hlam : 0 < lam)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hLower : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
        lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
    (hcNonpos : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → c z.1 z.2 ≤ 0) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ F : ℝ → PDE.Vec d → ℝ,
      ∀ hFSmooth : IsSmoothOnNeighborhood
        (fun z : TimeVelocity d => F z.1 z.2)
        (scalarParabolicClosedCylinder r₀ r₁ Ω),
      ∀ initial : PDE.ScalarLp Ω (2 : ℝ≥0∞),
      ∀ u : ReverseTimeL2V hΩ (r₁ - r₀),
      ∀ g : ReverseTimeL2VStar hΩ (r₁ - r₀),
      ∀ hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀)
        (sub_pos.mpr h₀₁) u g,
      ∀ _hu : IsReverseTimeVariationalEnergySolution r₀ r₁ h₀₁ hΩ hΩbounded
        a b c F hFSmooth initial u g hdu,
      ∀ v : ReverseTimeL2V hΩ (r₁ - r₀),
      ∀ k : ReverseTimeL2VStar hΩ (r₁ - r₀),
      ∀ hdv : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀)
        (sub_pos.mpr h₀₁) v k,
      ∀ _hv : IsReverseTimeVariationalEnergySolution r₀ r₁ h₀₁ hΩ hΩbounded
        a b c F hFSmooth initial v k hdv,
      HasReverseTimeDifferenceEnergyBound r₀ r₁ lam K h₀₁ hΩ
        u g hdu v k hdv := by
  obtain ⟨K, hK, hGarding⟩ :=
    reverseTimeSpatialForm_garding_of_smoothOnNeighborhood r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
      a b c haSmooth hbSmooth hcSmooth hLower hcNonpos
  refine ⟨K, hK, ?_⟩
  intro F hFSmooth initial u g hdu hu v k hdv hv
  let hdiff := hasGelfandWeakTimeDerivative_sub hdu hdv
  have hpde := ae_reverseTimeVariationalEnergy_difference_equation r₀ r₁ h₀₁ hΩ hΩbounded
    a b c F haSmooth hbSmooth hcSmooth hFSmooth initial u g hdu hu v k hdv hv
  have hpoint : ∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀),
      2 * ((g - k) τ) ((u - v) τ) + lam * ‖gradientCLM hΩ ((u - v) τ)‖ ^ 2 ≤
        2 * K * ‖valueCLM hΩ ((u - v) τ)‖ ^ 2 := by
    filter_upwards [hpde, ae_restrict_mem measurableSet_Ioo] with τ hpdeτ hτ
    have hτcc : τ ∈ Set.Icc 0 (r₁ - r₀) := ⟨le_of_lt hτ.1, le_of_lt hτ.2⟩
    have hgarding := hGarding τ hτcc ((u - v) τ)
    have heq := hpdeτ hτ
    linarith
  exact hasReverseTimeDifferenceEnergyBound_of_pointwise r₀ r₁ lam K h₀₁ hΩ
    u g hdu v k hdv hdiff hpoint

private theorem setIntegral_Ioc_reverseTimeVolume_eq_volume
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) {T t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    (∫ r in Set.Ioc 0 t, f r ∂reverseTimeVolume T) = ∫ r in Set.Ioc 0 t, f r := by
  rw [reverseTimeVolume, reverseTimeOpenInterval, restrict_Ioo_eq_restrict_Icc,
    Measure.restrict_restrict measurableSet_Ioc]
  congr 2
  exact inter_eq_left.mpr (Set.Ioc_subset_Icc_self.trans fun r hr =>
    ⟨hr.1, hr.2.trans ht.2⟩)

private def clampTime (T r : ℝ) : ℝ := min T (max 0 r)

private theorem clampTime_mem_Icc {T : ℝ} (hT : 0 < T) (r : ℝ) :
    clampTime T r ∈ Set.Icc 0 T := by
  dsimp only [clampTime]
  constructor
  · exact le_min hT.le (le_max_left _ _)
  · exact min_le_left _ _

private theorem clampTime_eq_of_mem {T r : ℝ} (hr : r ∈ Set.Icc 0 T) :
    clampTime T r = r := by
  dsimp only [clampTime]
  rw [max_eq_right hr.1, min_eq_right hr.2]

private theorem continuous_clampTime (T : ℝ) : Continuous (clampTime T) := by
  exact continuous_const.min (continuous_const.max continuous_id)

private theorem continuous_clamped_normSq
    {E : Type*} [NormedAddCommGroup E] {T : ℝ} (hT : 0 < T)
    (W : C(↥(Set.Icc 0 T), E)) :
    Continuous (fun r : ℝ => ‖W ⟨clampTime T r, clampTime_mem_Icc hT r⟩‖ ^ 2) := by
  exact (W.continuous.comp ((continuous_clampTime T).subtype_mk _)).norm.pow 2

private theorem eq_zero_of_norm_sq_eq_zero
    {E : Type*} [NormedAddCommGroup E] (x : E) (h : ‖x‖ ^ 2 = 0) :
    x = 0 := by
  have hnorm : ‖x‖ = 0 := by
    nlinarith [norm_nonneg x]
  exact norm_eq_zero.mp hnorm

private theorem reverseTime_value_sq_integral_eq_clamped_energy
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (w : ReverseTimeL2V hΩ T)
    (W : C(↥(Set.Icc 0 T), PDE.ScalarLp Ω (2 : ℝ≥0∞)))
    (hW : ReverseTimeHilbertRepresentativeAgrees hΩ T w W)
    (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
    (∫ r in Set.Ioc 0 t, ‖valueCLM hΩ (w r)‖ ^ 2 ∂reverseTimeVolume T) =
      ∫ r in Set.Ioc 0 t, ‖W ⟨clampTime T r, clampTime_mem_Icc hT r⟩‖ ^ 2 := by
  have hIoo : ∀ᵐ r ∂reverseTimeVolume T, r ∈ Set.Ioo 0 T :=
    ae_restrict_mem measurableSet_Ioo
  calc
    (∫ r in Set.Ioc 0 t, ‖valueCLM hΩ (w r)‖ ^ 2 ∂reverseTimeVolume T) =
        ∫ r in Set.Ioc 0 t, ‖W ⟨clampTime T r, clampTime_mem_Icc hT r⟩‖ ^ 2
          ∂reverseTimeVolume T := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hW, ae_restrict_of_ae hIoo]
        with r hWr hr
      have hrcc : r ∈ Set.Icc 0 T := ⟨le_of_lt hr.1, le_of_lt hr.2⟩
      have hclamp : clampTime T r = r := clampTime_eq_of_mem hrcc
      have hWr' : W ⟨clampTime T r, clampTime_mem_Icc hT r⟩ = valueCLM hΩ (w r) := by
        simpa only [hclamp] using hWr hr
      rw [← hWr']
    _ = ∫ r in Set.Ioc 0 t, ‖W ⟨clampTime T r, clampTime_mem_Icc hT r⟩‖ ^ 2 :=
      setIntegral_Ioc_reverseTimeVolume_eq_volume _ ht

private theorem reverseTimeHilbertRepresentative_eq_zero_of_clamped_energy_bound
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (_hΩ : IsOpen Ω) (T K : ℝ) (hT : 0 < T) (hK : 0 ≤ K)
    (W : C(↥(Set.Icc 0 T), PDE.ScalarLp Ω (2 : ℝ≥0∞)))
    (hWzero : W ⟨0, ⟨le_rfl, hT.le⟩⟩ = 0)
    (hbound : ∀ t : ℝ, ∀ ht : t ∈ Set.Icc 0 T,
      ‖W ⟨t, ht⟩‖ ^ 2 ≤ (2 * K) *
        (∫ r in Set.Ioc 0 t, ‖W ⟨clampTime T r, clampTime_mem_Icc hT r⟩‖ ^ 2)) :
    ∀ t : ℝ, ∀ ht : t ∈ Set.Icc 0 T, W ⟨t, ht⟩ = 0 := by
  let E : ℝ → ℝ := fun t => ‖W ⟨clampTime T t, clampTime_mem_Icc hT t⟩‖ ^ 2
  have hEcont : ContinuousOn E (Set.Icc 0 T) := by
    exact (continuous_clamped_normSq hT W).continuousOn
  have hEnonneg : ∀ t ∈ Set.Icc 0 T, 0 ≤ E t := by
    intro t ht
    exact sq_nonneg _
  have hEzero : E 0 = 0 := by
    dsimp only [E]
    have hsub : (⟨clampTime T 0, clampTime_mem_Icc hT 0⟩ : Set.Icc 0 T) =
        ⟨0, ⟨le_rfl, hT.le⟩⟩ := by
      apply Subtype.ext
      exact clampTime_eq_of_mem ⟨le_rfl, hT.le⟩
    rw [hsub, hWzero]
    norm_num
  have hEineq : ∀ t ∈ Set.Icc 0 T, E t ≤ (2 * K) * (∫ r in Set.Ioc 0 t, E r) := by
    intro t ht
    have hsub : (⟨clampTime T t, clampTime_mem_Icc hT t⟩ : Set.Icc 0 T) = ⟨t, ht⟩ := by
      apply Subtype.ext
      exact clampTime_eq_of_mem ht
    calc
      E t = ‖W ⟨t, ht⟩‖ ^ 2 := by
        dsimp only [E]
        exact congrArg (fun s : Set.Icc 0 T => ‖W s‖ ^ 2) hsub
      _ ≤ (2 * K) * (∫ r in Set.Ioc 0 t,
          ‖W ⟨clampTime T r, clampTime_mem_Icc hT r⟩‖ ^ 2) := hbound t ht
      _ = (2 * K) * (∫ r in Set.Ioc 0 t, E r) := rfl
  have hEzeroOn := eq_zero_on_Icc_of_nonneg_le_mul_integral hT
    (mul_nonneg (by norm_num) hK) E hEcont hEnonneg hEzero hEineq
  intro t ht
  have hsq' : ‖W ⟨clampTime T t, clampTime_mem_Icc hT t⟩‖ ^ 2 = 0 := hEzeroOn t ht
  have hsub : (⟨clampTime T t, clampTime_mem_Icc hT t⟩ : Set.Icc 0 T) = ⟨t, ht⟩ := by
    apply Subtype.ext
    exact clampTime_eq_of_mem ht
  have hsq : ‖W ⟨t, ht⟩‖ ^ 2 = 0 := by
    rw [← hsub]
    exact hsq'
  exact eq_zero_of_norm_sq_eq_zero _ hsq

private theorem reverseTimeL2V_eq_of_hilbertRepresentative_eq_zero
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ)
    (u v : ReverseTimeL2V hΩ T)
    (W : C(↥(Set.Icc 0 T), PDE.ScalarLp Ω (2 : ℝ≥0∞)))
    (hW : ReverseTimeHilbertRepresentativeAgrees hΩ T (u - v) W)
    (hWzero : ∀ t : ℝ, ∀ ht : t ∈ Set.Icc 0 T, W ⟨t, ht⟩ = 0) :
    u = v := by
  apply Lp.ext
  filter_upwards [hW, ae_restrict_mem measurableSet_Ioo, Lp.coeFn_sub u v]
    with τ hWτ hτ huv
  have hτcc : τ ∈ Set.Icc 0 T := ⟨le_of_lt hτ.1, le_of_lt hτ.2⟩
  have hvaluezero : valueCLM hΩ ((u - v) τ) = 0 := by
    rw [← hWτ hτ]
    exact hWzero τ hτcc
  have hdiffzero : (u - v) τ = 0 := by
    apply valueCLM_injective hΩ
    simpa only [ContinuousLinearMap.map_zero] using hvaluezero
  rw [huv] at hdiffzero
  simpa only [Pi.sub_apply] using sub_eq_zero.mp hdiffzero

private theorem reverseTimeL2V_eq_of_differenceEnergyBound
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ lam K : ℝ) (h₀₁ : r₀ < r₁) (hlam : 0 < lam) (hK : 0 ≤ K)
    (hΩ : IsOpen Ω)
    (u : ReverseTimeL2V hΩ (r₁ - r₀)) (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) u g)
    (v : ReverseTimeL2V hΩ (r₁ - r₀)) (k : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdv : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) v k)
    (htrace : reverseTimeInitialTrace hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) u g hdu =
      reverseTimeInitialTrace hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) v k hdv)
    (hbound : HasReverseTimeDifferenceEnergyBound r₀ r₁ lam K h₀₁ hΩ
      u g hdu v k hdv) :
    u = v := by
  let hT : 0 < r₁ - r₀ := sub_pos.mpr h₀₁
  let hdiff : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀) hT (u - v) (g - k) :=
    hasGelfandWeakTimeDerivative_sub hdu hdv
  let W := reverseTimeHilbertRepresentative hΩ (r₁ - r₀) hT (u - v) (g - k) hdiff
  have hW := (reverseTimeHilbertRepresentative_spec hΩ (r₁ - r₀) hT
    (u - v) (g - k) hdiff).1
  have hrep := reverseTimeHilbertRepresentative_sub_eq hΩ (r₁ - r₀) hT
    u g hdu v k hdv hdiff
  have hWzero : W ⟨0, ⟨le_rfl, hT.le⟩⟩ = 0 := by
    change reverseTimeHilbertRepresentative hΩ (r₁ - r₀) hT (u - v) (g - k) hdiff
      ⟨0, ⟨le_rfl, hT.le⟩⟩ = 0
    rw [hrep]
    change reverseTimeInitialTrace hΩ (r₁ - r₀) hT u g hdu -
      reverseTimeInitialTrace hΩ (r₁ - r₀) hT v k hdv = 0
    rw [htrace]
    exact sub_self _
  have hvalueIoc (t : ℝ) (ht : t ∈ Set.Icc 0 (r₁ - r₀)) :
      (∫ τ in Set.Ioc 0 t, ‖valueCLM hΩ (u τ - v τ)‖ ^ 2
        ∂reverseTimeVolume (r₁ - r₀)) =
        ∫ τ in Set.Ioc 0 t, ‖valueCLM hΩ ((u - v) τ)‖ ^ 2
          ∂reverseTimeVolume (r₁ - r₀) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (Lp.coeFn_sub u v)] with τ hτ
    rw [hτ]
    simp only [Pi.sub_apply]
  have hclampedEnergyBound : ∀ t : ℝ, ∀ ht : t ∈ Set.Icc 0 (r₁ - r₀),
      ‖W ⟨t, ht⟩‖ ^ 2 ≤ (2 * K) *
        (∫ r in Set.Ioc 0 t,
          ‖W ⟨clampTime (r₁ - r₀) r, clampTime_mem_Icc hT r⟩‖ ^ 2) := by
    intro t ht
    have henergy := hbound 0 t ⟨le_rfl, hT.le⟩ ht ht.1
    have hrep_t : W ⟨t, ht⟩ =
        reverseTimeHilbertRepresentative hΩ (r₁ - r₀) hT u g hdu ⟨t, ht⟩ -
          reverseTimeHilbertRepresentative hΩ (r₁ - r₀) hT v k hdv ⟨t, ht⟩ := by
      change reverseTimeHilbertRepresentative hΩ (r₁ - r₀) hT (u - v) (g - k) hdiff
        ⟨t, ht⟩ = _
      exact congrArg (fun z => z ⟨t, ht⟩) hrep
    have hrep_zero : W ⟨0, ⟨le_rfl, hT.le⟩⟩ =
        reverseTimeHilbertRepresentative hΩ (r₁ - r₀) hT u g hdu ⟨0, ⟨le_rfl, hT.le⟩⟩ -
          reverseTimeHilbertRepresentative hΩ (r₁ - r₀) hT v k hdv ⟨0, ⟨le_rfl, hT.le⟩⟩ := by
      change reverseTimeHilbertRepresentative hΩ (r₁ - r₀) hT (u - v) (g - k) hdiff
        ⟨0, ⟨le_rfl, hT.le⟩⟩ = _
      exact congrArg (fun z => z ⟨0, ⟨le_rfl, hT.le⟩⟩) hrep
    rw [← hrep_t, ← hrep_zero] at henergy
    rw [hWzero] at henergy
    have henergy' : ‖W ⟨t, ht⟩‖ ^ 2 + lam *
        (∫ τ in Set.Ioc 0 t, ‖gradientCLM hΩ (u τ - v τ)‖ ^ 2
          ∂reverseTimeVolume (r₁ - r₀)) ≤
        2 * K * (∫ τ in Set.Ioc 0 t, ‖valueCLM hΩ (u τ - v τ)‖ ^ 2
          ∂reverseTimeVolume (r₁ - r₀)) := by
      have hzero : ‖(0 : PDE.ScalarLp Ω (2 : ℝ≥0∞))‖ ^ 2 = 0 := by
        norm_num
      rw [hzero, sub_zero] at henergy
      exact henergy
    have hgrad : 0 ≤ ∫ τ in Set.Ioc 0 t, ‖gradientCLM hΩ (u τ - v τ)‖ ^ 2
        ∂reverseTimeVolume (r₁ - r₀) := by
      exact integral_nonneg fun τ => sq_nonneg _
    have hdrop : ‖W ⟨t, ht⟩‖ ^ 2 ≤
        2 * K * (∫ τ in Set.Ioc 0 t, ‖valueCLM hΩ (u τ - v τ)‖ ^ 2
          ∂reverseTimeVolume (r₁ - r₀)) := by
      have hterm : 0 ≤ lam *
          (∫ τ in Set.Ioc 0 t, ‖gradientCLM hΩ (u τ - v τ)‖ ^ 2
            ∂reverseTimeVolume (r₁ - r₀)) := mul_nonneg (le_of_lt hlam) hgrad
      exact (le_add_of_nonneg_right hterm).trans henergy'
    calc
      ‖W ⟨t, ht⟩‖ ^ 2 ≤ 2 * K * (∫ τ in Set.Ioc 0 t, ‖valueCLM hΩ (u τ - v τ)‖ ^ 2
          ∂reverseTimeVolume (r₁ - r₀)) := hdrop
      _ = 2 * K * (∫ τ in Set.Ioc 0 t, ‖valueCLM hΩ ((u - v) τ)‖ ^ 2
          ∂reverseTimeVolume (r₁ - r₀)) :=
        congrArg (fun x : ℝ => 2 * K * x) (hvalueIoc t ht)
      _ = (2 * K) * (∫ r in Set.Ioc 0 t,
          ‖W ⟨clampTime (r₁ - r₀) r, clampTime_mem_Icc hT r⟩‖ ^ 2) := by
        exact congrArg (fun x : ℝ => 2 * K * x)
          (reverseTime_value_sq_integral_eq_clamped_energy hΩ (r₁ - r₀) hT
            (u - v) W hW t ht)
  have hWzeroOn := reverseTimeHilbertRepresentative_eq_zero_of_clamped_energy_bound
    hΩ (r₁ - r₀) K hT hK W hWzero hclampedEnergyBound
  exact reverseTimeL2V_eq_of_hilbertRepresentative_eq_zero hΩ (r₁ - r₀)
    u v W hW hWzeroOn

/-- Two reverse-time variational energy solutions with common initial trace are equal. -/
theorem reverseTimeVariationalEnergySolution_unique
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ lam : ℝ) (h₀₁ : r₀ < r₁) (hlam : 0 < lam)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
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
    (hLower : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
        lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
    (hcNonpos : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → c z.1 z.2 ≤ 0)
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (u : ReverseTimeL2V hΩ (r₁ - r₀))
    (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀)
      (sub_pos.mpr h₀₁) u g)
    (hu : IsReverseTimeVariationalEnergySolution r₀ r₁ h₀₁ hΩ hΩbounded
      a b c F hFSmooth initial u g hdu)
    (v : ReverseTimeL2V hΩ (r₁ - r₀))
    (k : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdv : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀)
      (sub_pos.mpr h₀₁) v k)
    (hv : IsReverseTimeVariationalEnergySolution r₀ r₁ h₀₁ hΩ hΩbounded
      a b c F hFSmooth initial v k hdv) :
    u = v ∧ g = k := by
  obtain ⟨K, hK, hboundAll⟩ :=
    exists_reverseTimeVariationalEnergy_difference_constant r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
      a b c haSmooth hbSmooth hcSmooth hLower hcNonpos
  have hbound := hboundAll F hFSmooth initial u g hdu hu v k hdv hv
  have htrace : reverseTimeInitialTrace hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) u g hdu =
      reverseTimeInitialTrace hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) v k hdv := by
    calc
      reverseTimeInitialTrace hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) u g hdu = initial := hu.1
      _ = reverseTimeInitialTrace hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) v k hdv := hv.1.symm
  have huv : u = v := reverseTimeL2V_eq_of_differenceEnergyBound r₀ r₁ lam K h₀₁ hlam hK
    hΩ u g hdu v k hdv htrace hbound
  have hdv' : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) u k :=
    hdv.congr huv.symm rfl
  exact ⟨huv, hdu.unique hdv'⟩
