module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.GelfandTriple
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTime
public import HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialL2Multiplier
public import PDEFoundation.Sobolev.W1p.Graph
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Tactic.Ring

/-!
# Reverse-time spatial form

This file records the literal fixed-time spatial scalar for the reversed
divergence-form equation, together with an explicitly evidenced quotient-safe
`L²` representation.  The raw scalar has no asserted variational properties.
-/

@[expose] public section

open Filter MeasureTheory
open scoped BigOperators ENNReal RealInnerProductSpace

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- The literal spatial scalar in the reversed divergence-form equation. -/
noncomputable def reverseTimeSpatialForm
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (r₁ τ : ℝ) (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (u v : H10HilbertGraph hΩ) : ℝ :=
  (∑ i : Fin d, ∑ j : Fin d,
    ∫ y in Ω,
      a (r₁ - τ) y i j *
        (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
          (gradientCLM hΩ u)) y *
        (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
          (gradientCLM hΩ v)) y) +
    (∑ j : Fin d,
      ∫ y in Ω,
        reverseTimeDivergenceDrift r₁ a b τ y j *
          (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
            (gradientCLM hΩ u)) y *
          (valueCLM hΩ v) y) -
    ∫ y in Ω,
      reverseTimeScalarCoefficient r₁ c τ y *
        (valueCLM hΩ u) y * (valueCLM hΩ v) y

/-- Definitional expansion of the literal reversed spatial scalar. -/
theorem reverseTimeSpatialForm_apply
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (r₁ τ : ℝ) (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (u v : H10HilbertGraph hΩ) :
    reverseTimeSpatialForm hΩ r₁ τ a b c u v =
      (∑ i : Fin d, ∑ j : Fin d,
        ∫ y in Ω,
          a (r₁ - τ) y i j *
            (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
              (gradientCLM hΩ u)) y *
            (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
              (gradientCLM hΩ v)) y) +
        (∑ j : Fin d,
          ∫ y in Ω,
            reverseTimeDivergenceDrift r₁ a b τ y j *
              (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
                (gradientCLM hΩ u)) y *
              (valueCLM hΩ v) y) -
        ∫ y in Ω,
          reverseTimeScalarCoefficient r₁ c τ y *
            (valueCLM hΩ u) y * (valueCLM hΩ v) y :=
  rfl

/-- The negative reverse-time source functional induced by bundled spatial `L²` data. -/
noncomputable def reverseTimeSourceFunctional
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (f : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    H10HilbertGraph hΩ →L[ℝ] ℝ :=
  -(scalarLpToH10HilbertGraphDual hΩ f)

/-- Evaluation of the negative reverse-time source functional. -/
theorem reverseTimeSourceFunctional_apply
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (f : PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (v : H10HilbertGraph hΩ) :
    reverseTimeSourceFunctional hΩ f v =
      -inner ℝ (valueCLM hΩ v) f := by
  rw [reverseTimeSourceFunctional]
  simp only [ContinuousLinearMap.neg_apply, scalarLpToH10HilbertGraphDual_apply]

/-- The reverse-time source functional is bounded by the spatial pivot norm. -/
theorem norm_reverseTimeSourceFunctional_le
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (f : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    ‖reverseTimeSourceFunctional hΩ f‖ ≤ ‖valueCLM hΩ‖ * ‖f‖ := by
  rw [reverseTimeSourceFunctional, norm_neg]
  exact norm_scalarLpToH10HilbertGraphDual_apply_le hΩ f

/-- Pointwise operator-norm bound for the negative reverse-time source functional. -/
theorem abs_reverseTimeSourceFunctional_apply_le
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (f : PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (v : H10HilbertGraph hΩ) :
    |reverseTimeSourceFunctional hΩ f v| ≤
      (‖valueCLM hΩ‖ * ‖f‖) * ‖v‖ := by
  rw [reverseTimeSourceFunctional_apply, abs_neg]
  calc
    |inner ℝ (valueCLM hΩ v) f| ≤ ‖valueCLM hΩ v‖ * ‖f‖ := by
      exact abs_real_inner_le_norm (valueCLM hΩ v) f
    _ ≤ (‖valueCLM hΩ‖ * ‖v‖) * ‖f‖ := by
      exact mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ = (‖valueCLM hΩ‖ * ‖f‖) * ‖v‖ := by ring

/-- The bundled spatial `L²` source slice obtained from explicit `MemLp` evidence. -/
noncomputable def reverseTimeSourceSlice
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₁ τ : ℝ) (F : ℝ → PDE.Vec d → ℝ)
    (hF : MeasureTheory.MemLp
      (fun y : PDE.Vec d => F (r₁ - τ) y)
      (2 : ℝ≥0∞) (PDE.volumeOn Ω)) :
    PDE.ScalarLp Ω (2 : ℝ≥0∞) :=
  hF.toLp (fun y : PDE.Vec d => F (r₁ - τ) y)

/-- The source slice is represented almost everywhere by its reverse-time pullback. -/
theorem coeFn_reverseTimeSourceSlice
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₁ τ : ℝ) (F : ℝ → PDE.Vec d → ℝ)
    (hF : MeasureTheory.MemLp
      (fun y : PDE.Vec d => F (r₁ - τ) y)
      (2 : ℝ≥0∞) (PDE.volumeOn Ω)) :
    ⇑(reverseTimeSourceSlice r₁ τ F hF) =ᵐ[PDE.volumeOn Ω]
      fun y : PDE.Vec d => F (r₁ - τ) y := by
  exact hF.coeFn_toLp

private theorem principal_integral_eq_multiplierInner
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (q : PDE.Vec d → ℝ)
    (hq : AEStronglyMeasurable q (PDE.volumeOn Ω))
    (C : ℝ) (hC : 0 ≤ C)
    (hqBound : ∀ᵐ y ∂PDE.volumeOn Ω, ‖q y‖ ≤ C)
    (f g : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    (∫ y in Ω, q y * f y * g y) =
      inner ℝ (scalarL2Multiplier q hq C hC hqBound f) g := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [scalarL2Multiplier_apply_ae q hq C hC hqBound f] with y hy
  rw [hy]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

private theorem drift_integral_eq_multiplierInner
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (q : PDE.Vec d → ℝ)
    (hq : AEStronglyMeasurable q (PDE.volumeOn Ω))
    (C : ℝ) (hC : 0 ≤ C)
    (hqBound : ∀ᵐ y ∂PDE.volumeOn Ω, ‖q y‖ ≤ C)
    (f g : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    (∫ y in Ω, q y * f y * g y) =
      inner ℝ (scalarL2Multiplier q hq C hC hqBound f) g := by
  exact principal_integral_eq_multiplierInner q hq C hC hqBound f g

private theorem scalar_integral_eq_multiplierInner
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (q : PDE.Vec d → ℝ)
    (hq : AEStronglyMeasurable q (PDE.volumeOn Ω))
    (C : ℝ) (hC : 0 ≤ C)
    (hqBound : ∀ᵐ y ∂PDE.volumeOn Ω, ‖q y‖ ≤ C)
    (f g : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    (∫ y in Ω, q y * f y * g y) =
      inner ℝ (scalarL2Multiplier q hq C hC hqBound f) g := by
  exact principal_integral_eq_multiplierInner q hq C hC hqBound f g

/-- With explicit slice multiplier evidence, the raw scalar has an `L²` representation. -/
theorem reverseTimeSpatialForm_eq_multiplierInner_of_sliceEvidence
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (r₁ τ : ℝ) (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (u v : H10HilbertGraph hΩ)
    (Ca : Fin d → Fin d → ℝ)
    (hCa : ∀ i j : Fin d, 0 ≤ Ca i j)
    (hAMeas : ∀ i j : Fin d,
      AEStronglyMeasurable (fun y : PDE.Vec d => a (r₁ - τ) y i j)
        (PDE.volumeOn Ω))
    (hABound : ∀ i j : Fin d,
      ∀ᵐ y ∂PDE.volumeOn Ω, ‖a (r₁ - τ) y i j‖ ≤ Ca i j)
    (Cd : Fin d → ℝ)
    (hCd : ∀ j : Fin d, 0 ≤ Cd j)
    (hDriftMeas : ∀ j : Fin d,
      AEStronglyMeasurable
        (fun y : PDE.Vec d => reverseTimeDivergenceDrift r₁ a b τ y j)
        (PDE.volumeOn Ω))
    (hDriftBound : ∀ j : Fin d,
      ∀ᵐ y ∂PDE.volumeOn Ω,
        ‖reverseTimeDivergenceDrift r₁ a b τ y j‖ ≤ Cd j)
    (Cc : ℝ) (hCc : 0 ≤ Cc)
    (hScalarMeas : AEStronglyMeasurable
      (fun y : PDE.Vec d => reverseTimeScalarCoefficient r₁ c τ y)
      (PDE.volumeOn Ω))
    (hScalarBound : ∀ᵐ y ∂PDE.volumeOn Ω,
      ‖reverseTimeScalarCoefficient r₁ c τ y‖ ≤ Cc) :
    reverseTimeSpatialForm hΩ r₁ τ a b c u v =
      (∑ i : Fin d, ∑ j : Fin d,
        inner ℝ
          (scalarL2Multiplier
            (fun y : PDE.Vec d => a (r₁ - τ) y i j)
            (hAMeas i j) (Ca i j) (hCa i j) (hABound i j)
            (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
              (gradientCLM hΩ u)))
          (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
            (gradientCLM hΩ v))) +
        (∑ j : Fin d,
          inner ℝ
            (scalarL2Multiplier
              (fun y : PDE.Vec d => reverseTimeDivergenceDrift r₁ a b τ y j)
              (hDriftMeas j) (Cd j) (hCd j) (hDriftBound j)
              (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
                (gradientCLM hΩ u)))
            (valueCLM hΩ v)) -
        inner ℝ
          (scalarL2Multiplier
            (fun y : PDE.Vec d => reverseTimeScalarCoefficient r₁ c τ y)
            hScalarMeas Cc hCc hScalarBound (valueCLM hΩ u))
          (valueCLM hΩ v) := by
  rw [reverseTimeSpatialForm_apply]
  have hPrincipal (i j : Fin d) :
      (∫ y in Ω,
        a (r₁ - τ) y i j *
          (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
            (gradientCLM hΩ u)) y *
          (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
            (gradientCLM hΩ v)) y) =
        inner ℝ
          (scalarL2Multiplier
            (fun y : PDE.Vec d => a (r₁ - τ) y i j)
            (hAMeas i j) (Ca i j) (hCa i j) (hABound i j)
            (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
              (gradientCLM hΩ u)))
          (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
            (gradientCLM hΩ v)) :=
    principal_integral_eq_multiplierInner
      (fun y : PDE.Vec d => a (r₁ - τ) y i j)
      (hAMeas i j) (Ca i j) (hCa i j) (hABound i j) _ _
  have hDrift (j : Fin d) :
      (∫ y in Ω,
        reverseTimeDivergenceDrift r₁ a b τ y j *
          (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
            (gradientCLM hΩ u)) y *
          (valueCLM hΩ v) y) =
        inner ℝ
          (scalarL2Multiplier
            (fun y : PDE.Vec d => reverseTimeDivergenceDrift r₁ a b τ y j)
            (hDriftMeas j) (Cd j) (hCd j) (hDriftBound j)
            (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
              (gradientCLM hΩ u)))
          (valueCLM hΩ v) :=
    drift_integral_eq_multiplierInner
      (fun y : PDE.Vec d => reverseTimeDivergenceDrift r₁ a b τ y j)
      (hDriftMeas j) (Cd j) (hCd j) (hDriftBound j) _ _
  have hScalar :
      (∫ y in Ω,
        reverseTimeScalarCoefficient r₁ c τ y *
          (valueCLM hΩ u) y * (valueCLM hΩ v) y) =
        inner ℝ
          (scalarL2Multiplier
            (fun y : PDE.Vec d => reverseTimeScalarCoefficient r₁ c τ y)
            hScalarMeas Cc hCc hScalarBound (valueCLM hΩ u))
          (valueCLM hΩ v) :=
    scalar_integral_eq_multiplierInner
      (fun y : PDE.Vec d => reverseTimeScalarCoefficient r₁ c τ y)
      hScalarMeas Cc hCc hScalarBound _ _
  simp_rw [hPrincipal, hDrift, hScalar]

end HypoellipticAleksandrov.Parabolic.Dirichlet
