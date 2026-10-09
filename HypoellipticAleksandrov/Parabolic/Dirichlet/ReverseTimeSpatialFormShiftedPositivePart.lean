module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.H10ShiftedPositivePart
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialForm

/-!
# Shifted positive-part inequality for the reverse-time spatial form

This file proves the fixed-slice spatial-form inequality for testing against
`(u - k)₊`.  The scalar integrability assumptions are exactly those needed by
the literal total integrals in the form.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

private theorem h10ShiftedPositivePart_gradientCoord
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (u : H10HilbertGraph hΩ) (k : ℝ≥0) (i : Fin d) : ∀ᵐ y ∂PDE.volumeOn Ω,
    (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
      (gradientCLM hΩ (h10ShiftedPositivePart hΩ u k))) y =
      {z | (k : ℝ) < valueCLM hΩ u z}.indicator
        (fun z => (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
          (gradientCLM hΩ u)) z) y := by
  filter_upwards [gradientCLM_h10ShiftedPositivePart hΩ u k,
    PDE.coeFn_hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i (gradientCLM hΩ u),
    PDE.coeFn_hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
      (gradientCLM hΩ (h10ShiftedPositivePart hΩ u k))] with y hg hu hw
  by_cases hy : (k : ℝ) < valueCLM hΩ u y
  · calc
      _ = (gradientCLM hΩ (h10ShiftedPositivePart hΩ u k) y).ofLp i := hw
      _ = (gradientCLM hΩ u y).ofLp i := congrArg (fun q => q.ofLp i)
        (hg.trans (Set.indicator_of_mem
          (s := {z : PDE.Vec d | (k : ℝ) < valueCLM hΩ u z}) hy
          (gradientCLM hΩ u)))
      _ = _ := hu.symm
      _ = _ := (Set.indicator_of_mem
        (s := {z : PDE.Vec d | (k : ℝ) < valueCLM hΩ u z}) hy _).symm
  · calc
      _ = (gradientCLM hΩ (h10ShiftedPositivePart hΩ u k) y).ofLp i := hw
      _ = (0 : PDE.HilbertVec d).ofLp i := congrArg (fun q => q.ofLp i)
        (hg.trans (Set.indicator_of_notMem
          (s := {z : PDE.Vec d | (k : ℝ) < valueCLM hΩ u z}) hy
          (gradientCLM hΩ u)))
      _ = 0 := rfl
      _ = _ := (Set.indicator_of_notMem
        (s := {z : PDE.Vec d | (k : ℝ) < valueCLM hΩ u z}) hy _).symm

private theorem reverseTimePrincipal_shiftedPositivePart_eq
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (r₁ τ : ℝ) (a : CoefficientField d) (u : H10HilbertGraph hΩ) (k : ℝ≥0) :
      (∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
        a (r₁ - τ) y i j *
          (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u)) y *
          (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
            (gradientCLM hΩ (h10ShiftedPositivePart hΩ u k))) y) =
        ∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
          a (r₁ - τ) y i j *
            (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
              (gradientCLM hΩ (h10ShiftedPositivePart hΩ u k))) y *
            (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
              (gradientCLM hΩ (h10ShiftedPositivePart hΩ u k))) y := by
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  filter_upwards [h10ShiftedPositivePart_gradientCoord hΩ u k j,
    h10ShiftedPositivePart_gradientCoord hΩ u k i] with y hj hi
  by_cases hy : (k : ℝ) < valueCLM hΩ u y
  · have hj' := hj.trans (Set.indicator_of_mem
      (s := {z : PDE.Vec d | (k : ℝ) < valueCLM hΩ u z}) hy _)
    have hi' := hi.trans (Set.indicator_of_mem
      (s := {z : PDE.Vec d | (k : ℝ) < valueCLM hΩ u z}) hy _)
    rw [hj', hi']
  · have hj' := hj.trans (Set.indicator_of_notMem
      (s := {z : PDE.Vec d | (k : ℝ) < valueCLM hΩ u z}) hy _)
    have hi' := hi.trans (Set.indicator_of_notMem
      (s := {z : PDE.Vec d | (k : ℝ) < valueCLM hΩ u z}) hy _)
    rw [hj', hi']
    ring

private theorem reverseTimeDrift_shiftedPositivePart_eq
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (r₁ τ : ℝ) (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (u : H10HilbertGraph hΩ) (k : ℝ≥0) :
      (∑ j : Fin d, ∫ y in Ω,
        reverseTimeDivergenceDrift r₁ a b τ y j *
          (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u)) y *
          valueCLM hΩ (h10ShiftedPositivePart hΩ u k) y) =
        ∑ j : Fin d, ∫ y in Ω,
          reverseTimeDivergenceDrift r₁ a b τ y j *
            (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
              (gradientCLM hΩ (h10ShiftedPositivePart hΩ u k))) y *
            valueCLM hΩ (h10ShiftedPositivePart hΩ u k) y := by
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  filter_upwards [h10ShiftedPositivePart_gradientCoord hΩ u k j,
    coeFn_valueCLM_h10ShiftedPositivePart hΩ u k] with y hj hw
  by_cases hy : (k : ℝ) < valueCLM hΩ u y
  · have hj' := hj.trans (Set.indicator_of_mem
      (s := {z : PDE.Vec d | (k : ℝ) < valueCLM hΩ u z}) hy _)
    rw [hj']
  · have hj' := hj.trans (Set.indicator_of_notMem
      (s := {z : PDE.Vec d | (k : ℝ) < valueCLM hΩ u z}) hy _)
    have hw0 : valueCLM hΩ (h10ShiftedPositivePart hΩ u k) y = 0 := by
      rw [hw, max_eq_right]
      exact sub_nonpos.mpr (le_of_not_gt hy)
    rw [hj', hw0]
    ring

private theorem reverseTimeScalar_shiftedPositivePart_le
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (r₁ τ : ℝ) (c : ℝ → PDE.Vec d → ℝ)
    (u : H10HilbertGraph hΩ) (k : ℝ≥0)
    (hScalarNonpos : ∀ᵐ y ∂PDE.volumeOn Ω,
      reverseTimeScalarCoefficient r₁ c τ y ≤ 0)
    (hScalarSquare : Integrable
      (fun y : PDE.Vec d => reverseTimeScalarCoefficient r₁ c τ y *
        valueCLM hΩ (h10ShiftedPositivePart hΩ u k) y *
          valueCLM hΩ (h10ShiftedPositivePart hΩ u k) y)
      (PDE.volumeOn Ω))
    (hScalarCross : Integrable
      (fun y : PDE.Vec d => reverseTimeScalarCoefficient r₁ c τ y *
        valueCLM hΩ u y * valueCLM hΩ (h10ShiftedPositivePart hΩ u k) y)
      (PDE.volumeOn Ω)) :
    (∫ y, reverseTimeScalarCoefficient r₁ c τ y * valueCLM hΩ u y *
      valueCLM hΩ (h10ShiftedPositivePart hΩ u k) y ∂PDE.volumeOn Ω) ≤
      ∫ y, reverseTimeScalarCoefficient r₁ c τ y *
        valueCLM hΩ (h10ShiftedPositivePart hΩ u k) y *
        valueCLM hΩ (h10ShiftedPositivePart hΩ u k) y ∂PDE.volumeOn Ω := by
  let q := fun y : PDE.Vec d => reverseTimeScalarCoefficient r₁ c τ y
  let w := fun y : PDE.Vec d => valueCLM hΩ (h10ShiftedPositivePart hΩ u k) y
  have hvalue := coeFn_valueCLM_h10ShiftedPositivePart hΩ u k
  have hremainder : Integrable (fun y => q y * (k : ℝ) * w y) (PDE.volumeOn Ω) := by
    apply (hScalarCross.sub hScalarSquare).congr
    filter_upwards [hvalue] with y hw
    dsimp only [q, w] at *
    by_cases hy : (k : ℝ) < valueCLM hΩ u y
    · have hwu : w y = valueCLM hΩ u y - (k : ℝ) := by
        simpa only [w, max_eq_left (sub_nonneg.mpr (le_of_lt hy))] using hw
      change valueCLM hΩ (h10ShiftedPositivePart hΩ u k) y =
        valueCLM hΩ u y - (k : ℝ) at hwu
      simp only [Pi.sub_apply]
      rw [hwu]
      ring
    · have hw0 : w y = 0 := by
        simpa only [w, max_eq_right (sub_nonpos.mpr (le_of_not_gt hy))] using hw
      change valueCLM hΩ (h10ShiftedPositivePart hΩ u k) y = 0 at hw0
      simp only [Pi.sub_apply, hw0, mul_zero]
      exact sub_self 0
  have hremainderNonpos : (∫ y, q y * (k : ℝ) * w y ∂PDE.volumeOn Ω) ≤ 0 := by
    rw [← integral_zero]
    apply integral_mono_ae hremainder (integrable_zero _ _ _)
    filter_upwards [hScalarNonpos, hvalue] with y hq hw
    have hwNonneg : 0 ≤ w y := by
      simpa only [w, hw] using le_max_right (valueCLM hΩ u y - (k : ℝ)) 0
    exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hq k.2) hwNonneg
  have hscalar :
      (∫ y, q y * valueCLM hΩ u y * w y ∂PDE.volumeOn Ω) ≤
        ∫ y, q y * w y * w y ∂PDE.volumeOn Ω := by
    have hadd : (∫ y, q y * valueCLM hΩ u y * w y ∂PDE.volumeOn Ω) =
        (∫ y, q y * w y * w y ∂PDE.volumeOn Ω) +
          ∫ y, q y * (k : ℝ) * w y ∂PDE.volumeOn Ω := by
      rw [← integral_add hScalarSquare hremainder]
      apply integral_congr_ae
      filter_upwards [hvalue] with y hw
      dsimp only [q, w] at *
      by_cases hy : (k : ℝ) < valueCLM hΩ u y
      · have hwu : w y = valueCLM hΩ u y - (k : ℝ) := by
          simpa only [w, max_eq_left (sub_nonneg.mpr (le_of_lt hy))] using hw
        change valueCLM hΩ (h10ShiftedPositivePart hΩ u k) y =
          valueCLM hΩ u y - (k : ℝ) at hwu
        rw [hwu]
        ring
      · have hw0 : w y = 0 := by
          simpa only [w, max_eq_right (sub_nonpos.mpr (le_of_not_gt hy))] using hw
        change valueCLM hΩ (h10ShiftedPositivePart hΩ u k) y = 0 at hw0
        rw [hw0]
        ring
    rw [hadd]
    linarith
  dsimp only [q, w] at hscalar
  exact hscalar

private theorem reverseTimeSpatialForm_apply_shiftedPositivePart_ge_of_scalar_le
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (r₁ τ : ℝ) (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (u : H10HilbertGraph hΩ) (k : ℝ≥0)
    (hscalar :
      (∫ y, reverseTimeScalarCoefficient r₁ c τ y * valueCLM hΩ u y *
        valueCLM hΩ (h10ShiftedPositivePart hΩ u k) y ∂PDE.volumeOn Ω) ≤
        ∫ y, reverseTimeScalarCoefficient r₁ c τ y *
          valueCLM hΩ (h10ShiftedPositivePart hΩ u k) y *
          valueCLM hΩ (h10ShiftedPositivePart hΩ u k) y ∂PDE.volumeOn Ω) :
    reverseTimeSpatialForm hΩ r₁ τ a b c u (h10ShiftedPositivePart hΩ u k) ≥
      reverseTimeSpatialForm hΩ r₁ τ a b c
        (h10ShiftedPositivePart hΩ u k) (h10ShiftedPositivePart hΩ u k) := by
  rw [reverseTimeSpatialForm_apply]
  rw [reverseTimePrincipal_shiftedPositivePart_eq hΩ r₁ τ a u k]
  rw [reverseTimeDrift_shiftedPositivePart_eq hΩ r₁ τ a b u k]
  rw [reverseTimeSpatialForm_apply]
  exact sub_le_sub_left hscalar _

/-- Testing the reverse-time spatial form against `(u - k)₊` dominates the
form with `(u - k)₊` in both slots when the reverse-time scalar coefficient is
nonpositive. -/
theorem reverseTimeSpatialForm_apply_shiftedPositivePart_ge
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (r₁ τ : ℝ) (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (u : H10HilbertGraph hΩ) (k : ℝ≥0)
    (hScalarNonpos : ∀ᵐ y ∂PDE.volumeOn Ω,
      reverseTimeScalarCoefficient r₁ c τ y ≤ 0)
    (hScalarSquare : Integrable
      (fun y : PDE.Vec d => reverseTimeScalarCoefficient r₁ c τ y *
        valueCLM hΩ (h10ShiftedPositivePart hΩ u k) y *
          valueCLM hΩ (h10ShiftedPositivePart hΩ u k) y)
      (PDE.volumeOn Ω))
    (hScalarCross : Integrable
      (fun y : PDE.Vec d => reverseTimeScalarCoefficient r₁ c τ y *
        valueCLM hΩ u y * valueCLM hΩ (h10ShiftedPositivePart hΩ u k) y)
      (PDE.volumeOn Ω)) :
    reverseTimeSpatialForm hΩ r₁ τ a b c u (h10ShiftedPositivePart hΩ u k) ≥
      reverseTimeSpatialForm hΩ r₁ τ a b c
        (h10ShiftedPositivePart hΩ u k) (h10ShiftedPositivePart hΩ u k) := by
  have hscalar := reverseTimeScalar_shiftedPositivePart_le hΩ r₁ τ c u k
    hScalarNonpos hScalarSquare hScalarCross
  exact reverseTimeSpatialForm_apply_shiftedPositivePart_ge_of_scalar_le
    hΩ r₁ τ a b c u k hscalar

end HypoellipticAleksandrov.Parabolic.Dirichlet
