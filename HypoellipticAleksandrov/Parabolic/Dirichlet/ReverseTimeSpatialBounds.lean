module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTime
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import PDEFoundation.Measure.RestrictedVolume

/-!
# Local reverse-time spatial bounds

This module derives the compact-cylinder bounds on the reverse-time
coefficient, drift, scalar coefficient, and source slices required by the
Dirichlet data layer.  All regularity hypotheses are local to the indicated
closed cylinder.
-/

@[expose] public section

noncomputable section

open scoped ENNReal Matrix.Norms.Elementwise
open MeasureTheory Set

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- A scalar parabolic closed cylinder is compact when its spatial base is bounded. -/
theorem isCompact_scalarParabolicClosedCylinder
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (hΩbounded : Bornology.IsBounded Ω) :
    IsCompact (scalarParabolicClosedCylinder r₀ r₁ Ω) := by
  change IsCompact (Set.Icc r₀ r₁ ×ˢ closure Ω)
  exact isCompact_Icc.prod hΩbounded.isCompact_closure

/-- The derivative of a fixed-time spatial coefficient slice is the joint
derivative in a purely spatial direction. -/
theorem fderiv_scalarSpatialSlice_apply
    {d : ℕ} (a : CoefficientField d) (r : ℝ)
    (y v : PDE.Vec d) (i j : Fin d)
    (ha : DifferentiableAt ℝ
      (fun z : TimeVelocity d => a z.1 z.2 i j) (r, y)) :
    (fderiv ℝ (fun x : PDE.Vec d => a r x i j) y) v =
      (fderiv ℝ (fun z : TimeVelocity d => a z.1 z.2 i j) (r, y)) (0, v) := by
  have hslice : HasFDerivAt (fun x : PDE.Vec d => a r x i j)
      ((fderiv ℝ (fun z : TimeVelocity d => a z.1 z.2 i j) (r, y)).comp
        (ContinuousLinearMap.inr ℝ ℝ (PDE.Vec d))) y := by
    simpa only [Function.comp_def] using ha.hasFDerivAt.comp y
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) r y)
  rw [hslice.fderiv]
  rfl

/-- Joint smoothness near the closed cylinder makes the literal fixed-time
spatial coefficient divergence continuous there. -/
theorem continuousOn_scalarSpatialCoefficientDivergence_of_smoothOnNeighborhood
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (a : CoefficientField d)
    (ha : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) :
    ContinuousOn (scalarSpatialCoefficientDivergence a)
      (scalarParabolicClosedCylinder r₀ r₁ Ω) := by
  rcases ha with ⟨V, hVopen, hKV, hV⟩
  apply continuousOn_pi.2
  intro j
  change ContinuousOn (fun z : TimeVelocity d => ∑ i : Fin d,
    (fderiv ℝ (fun y : PDE.Vec d => a z.1 y i j) z.2) (PDE.basisVec i))
    (scalarParabolicClosedCylinder r₀ r₁ Ω)
  apply continuousOn_finset_sum
  intro i _hi
  have hrow : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => a z.1 z.2 i) V := by
    exact (contDiffOn_apply ℝ (Fin d → ℝ) i Set.univ).comp hV (by
      intro z hz
      exact Set.mem_univ _)
  have hentry : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => a z.1 z.2 i j) V := by
    exact (contDiffOn_apply ℝ ℝ j Set.univ).comp hrow (by
      intro z hz
      exact Set.mem_univ _)
  have hderiv : ContinuousOn (fun z : TimeVelocity d =>
      (fderiv ℝ (fun w : TimeVelocity d => a w.1 w.2 i j) z) (0, PDE.basisVec i)) V :=
    (hentry.continuousOn_fderiv_of_isOpen hVopen (by simp)).clm_apply
      continuousOn_const
  refine (hderiv.mono hKV).congr ?_
  intro z hz
  rcases z with ⟨r, y⟩
  simpa using fderiv_scalarSpatialSlice_apply a r y (PDE.basisVec i) i j
    ((hentry.contDiffAt (hVopen.mem_nhds (hKV hz))).differentiableAt (by simp))

/-- Smooth coefficients near a bounded closed cylinder have one uniform bound
for the reverse-time spatial coefficient divergence. -/
theorem exists_scalarSpatialCoefficientDivergence_bound_of_smoothOnNeighborhood
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (ha : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ τ : ℝ, τ ∈ Set.Icc 0 (r₁ - r₀) →
      ∀ y : PDE.Vec d, y ∈ Ω →
        ‖scalarSpatialCoefficientDivergence
          (reverseTimeCoefficient r₁ a) (τ, y)‖ ≤ M := by
  have hcont := continuousOn_scalarSpatialCoefficientDivergence_of_smoothOnNeighborhood
    r₀ r₁ a ha
  obtain ⟨C, hC⟩ :=
    (isCompact_scalarParabolicClosedCylinder r₀ r₁ hΩbounded).exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro τ hτ y hy
  have htime : r₀ ≤ r₁ - τ ∧ r₁ - τ ≤ r₁ := by
    constructor <;> linarith [hτ.1, hτ.2]
  have hpoint : (r₁ - τ, y) ∈ scalarParabolicClosedCylinder r₀ r₁ Ω :=
    ⟨htime, subset_closure hy⟩
  rw [scalarSpatialCoefficientDivergence_reverseTimeCoefficient]
  exact (hC (r₁ - τ, y) hpoint).trans (le_max_left _ _)

/-- Smooth coefficient and drift data near a bounded closed cylinder have one
uniform bound for the reverse-time divergence drift. -/
theorem exists_reverseTimeDivergenceDrift_bound_of_smoothOnNeighborhood
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (ha : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hb : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ τ : ℝ, τ ∈ Set.Icc 0 (r₁ - r₀) →
      ∀ y : PDE.Vec d, y ∈ Ω →
        ‖reverseTimeDivergenceDrift r₁ a b τ y‖ ≤ M := by
  obtain ⟨A, hA0, hA⟩ :=
    exists_scalarSpatialCoefficientDivergence_bound_of_smoothOnNeighborhood
      r₀ r₁ hΩbounded a ha
  rcases hb with ⟨V, hVopen, hKV, hV⟩
  obtain ⟨B, hB⟩ :=
    (isCompact_scalarParabolicClosedCylinder r₀ r₁ hΩbounded).exists_bound_of_continuousOn
      (hV.continuousOn.mono hKV)
  refine ⟨A + max B 0, add_nonneg hA0 (le_max_right _ _), ?_⟩
  intro τ hτ y hy
  have htime : r₀ ≤ r₁ - τ ∧ r₁ - τ ≤ r₁ := by
    constructor <;> linarith [hτ.1, hτ.2]
  have hpoint : (r₁ - τ, y) ∈ scalarParabolicClosedCylinder r₀ r₁ Ω :=
    ⟨htime, subset_closure hy⟩
  calc
    ‖reverseTimeDivergenceDrift r₁ a b τ y‖ ≤
        ‖scalarSpatialCoefficientDivergence (reverseTimeCoefficient r₁ a) (τ, y)‖ +
          ‖reverseTimeVectorCoefficient r₁ b τ y‖ := norm_sub_le _ _
    _ ≤ A + max B 0 := add_le_add (hA τ hτ y hy) (by
      simpa only [reverseTimeVectorCoefficient_apply] using
        (hB (r₁ - τ, y) hpoint).trans (le_max_left _ _))

/-- A smooth scalar coefficient near the closed cylinder restricts to a
continuous reverse-time spatial slice. -/
theorem continuousOn_reverseTimeScalarCoefficient_slice_of_smoothOnNeighborhood
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ τ : ℝ) (c : ℝ → PDE.Vec d → ℝ)
    (hc : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hτ : τ ∈ Set.Icc 0 (r₁ - r₀)) :
    ContinuousOn (fun y : PDE.Vec d =>
      reverseTimeScalarCoefficient r₁ c τ y) Ω := by
  rcases hc with ⟨V, hVopen, hKV, hV⟩
  have htime : r₀ ≤ r₁ - τ ∧ r₁ - τ ≤ r₁ := by
    constructor <;> linarith [hτ.1, hτ.2]
  have hmap : MapsTo (fun y : PDE.Vec d => (r₁ - τ, y)) Ω
      (scalarParabolicClosedCylinder r₀ r₁ Ω) := by
    intro y hy
    exact ⟨htime, subset_closure hy⟩
  have hcont : Continuous (fun y : PDE.Vec d => (r₁ - τ, y)) :=
    Continuous.prodMk_right _
  simpa only [reverseTimeScalarCoefficient_apply, Function.comp_def] using
    (hV.continuousOn.mono hKV).comp hcont.continuousOn hmap

/-- Smooth scalar coefficients near a bounded closed cylinder have one
uniform bound for all reverse-time spatial slices. -/
theorem exists_reverseTimeScalarCoefficient_bound_of_smoothOnNeighborhood
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (hΩbounded : Bornology.IsBounded Ω)
    (c : ℝ → PDE.Vec d → ℝ)
    (hc : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ τ : ℝ, τ ∈ Set.Icc 0 (r₁ - r₀) →
      ∀ y : PDE.Vec d, y ∈ Ω →
        |reverseTimeScalarCoefficient r₁ c τ y| ≤ M := by
  rcases hc with ⟨V, hVopen, hKV, hV⟩
  obtain ⟨C, hC⟩ :=
    (isCompact_scalarParabolicClosedCylinder r₀ r₁ hΩbounded).exists_bound_of_continuousOn
      (hV.continuousOn.mono hKV)
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro τ hτ y hy
  have htime : r₀ ≤ r₁ - τ ∧ r₁ - τ ≤ r₁ := by
    constructor <;> linarith [hτ.1, hτ.2]
  have hpoint : (r₁ - τ, y) ∈ scalarParabolicClosedCylinder r₀ r₁ Ω :=
    ⟨htime, subset_closure hy⟩
  simpa only [reverseTimeScalarCoefficient_apply, Real.norm_eq_abs] using
    (hC (r₁ - τ, y) hpoint).trans (le_max_left _ _)

/-- A smooth source near the closed cylinder is a.e.-strongly measurable on
each reverse-time slice with respect to the restricted spatial volume. -/
theorem aestronglyMeasurable_reverseTimeSourceSlice_of_smoothOnNeighborhood
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ τ : ℝ) (hΩ : IsOpen Ω)
    (F : ℝ → PDE.Vec d → ℝ)
    (hF : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hτ : τ ∈ Set.Icc 0 (r₁ - r₀)) :
    MeasureTheory.AEStronglyMeasurable
      (fun y : PDE.Vec d => F (r₁ - τ) y) (PDE.volumeOn Ω) := by
  have hcont := continuousOn_reverseTimeScalarCoefficient_slice_of_smoothOnNeighborhood
    r₀ r₁ τ F hF hτ
  simpa only [reverseTimeScalarCoefficient_apply, Function.comp_def] using
    hcont.aestronglyMeasurable hΩ.measurableSet

/-- A smooth source near a bounded closed cylinder belongs to `L²` on every
reverse-time slice. -/
theorem reverseTimeSourceSlice_memLp_of_smoothOnNeighborhood
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω)
    (F : ℝ → PDE.Vec d → ℝ)
    (hF : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (τ : ℝ) (hτ : τ ∈ Set.Icc 0 (r₁ - r₀)) :
    MemLp
      (fun y : PDE.Vec d => F (r₁ - τ) y)
      (2 : ℝ≥0∞) (PDE.volumeOn Ω) := by
  letI : MeasureTheory.IsFiniteMeasure (PDE.volumeOn Ω) :=
    MeasureTheory.isFiniteMeasure_restrict.mpr hΩbounded.measure_lt_top.ne
  obtain ⟨C, hC0, hC⟩ :=
    exists_reverseTimeScalarCoefficient_bound_of_smoothOnNeighborhood
      r₀ r₁ hΩbounded F hF
  have hmeas : AEStronglyMeasurable (fun y : PDE.Vec d => F (r₁ - τ) y)
      (PDE.volumeOn Ω) :=
    aestronglyMeasurable_reverseTimeSourceSlice_of_smoothOnNeighborhood
      r₀ r₁ τ hΩ F hF hτ
  refine MemLp.of_bound hmeas C ?_
  filter_upwards [ae_restrict_mem hΩ.measurableSet] with y hy
  simpa only [Real.norm_eq_abs, reverseTimeScalarCoefficient_apply] using hC τ hτ y hy

/-- Smooth source data near a bounded closed cylinder have one uniform `L²`
bound for all reverse-time slices. -/
theorem exists_reverseTimeSourceSlice_L2_bound_of_smoothOnNeighborhood
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω)
    (F : ℝ → PDE.Vec d → ℝ)
    (hF : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ τ : ℝ, τ ∈ Set.Icc 0 (r₁ - r₀) →
      ∀ hτLp : MemLp
        (fun y : PDE.Vec d => F (r₁ - τ) y)
        (2 : ℝ≥0∞) (PDE.volumeOn Ω),
        ‖hτLp.toLp (fun y : PDE.Vec d => F (r₁ - τ) y)‖ ≤ M := by
  letI : MeasureTheory.IsFiniteMeasure (PDE.volumeOn Ω) :=
    MeasureTheory.isFiniteMeasure_restrict.mpr hΩbounded.measure_lt_top.ne
  obtain ⟨C, hC0, hC⟩ :=
    exists_reverseTimeScalarCoefficient_bound_of_smoothOnNeighborhood
      r₀ r₁ hΩbounded F hF
  let B : ℝ := max C 0
  refine ⟨(MeasureTheory.measureUnivNNReal (PDE.volumeOn Ω)) ^
      ((2 : ℝ≥0∞).toReal)⁻¹ * B, mul_nonneg (by positivity) (le_max_right _ _), ?_⟩
  intro τ hτ hτLp
  apply MeasureTheory.Lp.norm_le_of_ae_bound (le_max_right _ _)
  filter_upwards [hτLp.coeFn_toLp, ae_restrict_mem hΩ.measurableSet] with y hy hyΩ
  rw [hy]
  simpa only [Real.norm_eq_abs, reverseTimeScalarCoefficient_apply] using
    (hC τ hτ y hyΩ).trans (le_max_left _ _)

end HypoellipticAleksandrov.Parabolic.Dirichlet
