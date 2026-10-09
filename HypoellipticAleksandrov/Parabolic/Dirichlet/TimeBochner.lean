module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.GelfandTriple
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Reverse-time Bochner spaces

This module defines the quotient-valued Bochner `L²` carriers over the literal
reverse-time interval and lifts the spatial Gelfand-triple maps to them.
It makes only almost-everywhere representative statements, never fixed-time
evaluation or temporal regularity claims.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- The open reverse-time interval, including the empty case `T ≤ 0`. -/
def reverseTimeOpenInterval (T : ℝ) : Set ℝ :=
  Set.Ioo 0 T

/-- Lebesgue measure restricted to the literal open reverse-time interval. -/
noncomputable def reverseTimeVolume (T : ℝ) : Measure ℝ :=
  volume.restrict (reverseTimeOpenInterval T)

/-- Bochner `L²` curves with values in the zero-boundary spatial Hilbert graph. -/
abbrev ReverseTimeL2V
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) : Type _ :=
  MeasureTheory.Lp (H10HilbertGraph hΩ) (2 : ℝ≥0∞) (reverseTimeVolume T)

/-- Bochner `L²` curves with values in spatial restricted-volume `L²`. -/
abbrev ReverseTimeL2H
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) : Type _ :=
  MeasureTheory.Lp (PDE.ScalarLp Ω (2 : ℝ≥0∞)) (2 : ℝ≥0∞)
    (reverseTimeVolume T)

/-- Bochner `L²` curves with values in the spatial Gelfand dual. -/
abbrev ReverseTimeL2VStar
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) : Type _ :=
  MeasureTheory.Lp (H10HilbertGraphDual hΩ) (2 : ℝ≥0∞)
    (reverseTimeVolume T)

/-- Pointwise application of the spatial value map, lifted to Bochner `L²`. -/
noncomputable def reverseTimeValueCLM
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) :
    ReverseTimeL2V hΩ T →L[ℝ] ReverseTimeL2H hΩ T :=
  (valueCLM hΩ).compLpL (2 : ℝ≥0∞) (reverseTimeVolume T)

/-- Pointwise application of the spatial pivot map, lifted to Bochner `L²`. -/
noncomputable def reverseTimePivotCLM
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) :
    ReverseTimeL2H hΩ T →L[ℝ] ReverseTimeL2VStar hΩ T :=
  (scalarLpToH10HilbertGraphDual hΩ).compLpL (2 : ℝ≥0∞)
    (reverseTimeVolume T)

/-- The timewise Gelfand embedding `V → H → V*`. -/
noncomputable def reverseTimeGelfandCLM
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) :
    ReverseTimeL2V hΩ T →L[ℝ] ReverseTimeL2VStar hΩ T :=
  (reverseTimePivotCLM hΩ T).comp (reverseTimeValueCLM hΩ T)

/-- Almost-everywhere formula for the Bochner lift of the spatial value map. -/
theorem coeFn_reverseTimeValueCLM
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ)
    (u : ReverseTimeL2V hΩ T) :
    reverseTimeValueCLM hΩ T u =ᵐ[reverseTimeVolume T]
      fun τ => valueCLM hΩ (u τ) :=
  ContinuousLinearMap.coeFn_compLpL (valueCLM hΩ) u

/-- Operator-norm bound for the Bochner lift of the spatial value map. -/
theorem norm_reverseTimeValueCLM_le
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) :
    ‖reverseTimeValueCLM hΩ T‖ ≤ ‖valueCLM hΩ‖ :=
  ContinuousLinearMap.norm_compLpL_le (valueCLM hΩ)

/-- Application norm bound for the Bochner lift of the spatial value map. -/
theorem norm_reverseTimeValueCLM_apply_le
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ)
    (u : ReverseTimeL2V hΩ T) :
    ‖reverseTimeValueCLM hΩ T u‖ ≤ ‖valueCLM hΩ‖ * ‖u‖ := by
  exact le_trans ((reverseTimeValueCLM hΩ T).le_opNorm u)
    (mul_le_mul_of_nonneg_right (norm_reverseTimeValueCLM_le hΩ T) (norm_nonneg u))

/-- Almost-everywhere formula for the Bochner lift of the spatial pivot map. -/
theorem coeFn_reverseTimePivotCLM
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ)
    (h : ReverseTimeL2H hΩ T) :
    reverseTimePivotCLM hΩ T h =ᵐ[reverseTimeVolume T]
      fun τ => scalarLpToH10HilbertGraphDual hΩ (h τ) :=
  ContinuousLinearMap.coeFn_compLpL (scalarLpToH10HilbertGraphDual hΩ) h

/-- Operator-norm bound for the Bochner lift of the spatial pivot map. -/
theorem norm_reverseTimePivotCLM_le
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) :
    ‖reverseTimePivotCLM hΩ T‖ ≤ ‖scalarLpToH10HilbertGraphDual hΩ‖ :=
  ContinuousLinearMap.norm_compLpL_le (scalarLpToH10HilbertGraphDual hΩ)

/-- Application norm bound for the Bochner lift of the spatial pivot map. -/
theorem norm_reverseTimePivotCLM_apply_le
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ)
    (h : ReverseTimeL2H hΩ T) :
    ‖reverseTimePivotCLM hΩ T h‖ ≤
      ‖scalarLpToH10HilbertGraphDual hΩ‖ * ‖h‖ := by
  exact le_trans ((reverseTimePivotCLM hΩ T).le_opNorm h)
    (mul_le_mul_of_nonneg_right (norm_reverseTimePivotCLM_le hΩ T) (norm_nonneg h))

/-- Almost-everywhere formula for the composed timewise Gelfand map. -/
theorem coeFn_reverseTimeGelfandCLM
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ)
    (u : ReverseTimeL2V hΩ T) :
    reverseTimeGelfandCLM hΩ T u =ᵐ[reverseTimeVolume T]
      fun τ => scalarLpToH10HilbertGraphDual hΩ (valueCLM hΩ (u τ)) := by
  filter_upwards [coeFn_reverseTimePivotCLM hΩ T
      (reverseTimeValueCLM hΩ T u), coeFn_reverseTimeValueCLM hΩ T u]
    with τ hPivot hValue
  change ((reverseTimePivotCLM hΩ T) (reverseTimeValueCLM hΩ T u)) τ = _
  rw [hPivot, hValue]

/-- Operator-norm bound for the composed timewise Gelfand map. -/
theorem norm_reverseTimeGelfandCLM_le
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) :
    ‖reverseTimeGelfandCLM hΩ T‖ ≤
      ‖reverseTimePivotCLM hΩ T‖ * ‖reverseTimeValueCLM hΩ T‖ :=
  ContinuousLinearMap.opNorm_comp_le _ _

end HypoellipticAleksandrov.Parabolic.Dirichlet
