module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonStability
public import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementReflection

/-! # Forward initial and lateral source comparison

Time reflection transports the signed backward bound to arbitrary forward cylinders.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Set

/-- Reflection transports an arbitrary open cylinder to the reversed time cylinder. -/
theorem timeReflection_mem_openCylinder_iff {d : ℕ} (a T : ℝ)
    (Ω : Set (PDE.Vec d)) (z : TimeVelocity d) :
    timeReflection z ∈ scalarParabolicOpenCylinder a T Ω ↔
      z ∈ scalarParabolicOpenCylinder (1 - T) (1 - a) Ω := by
  change (a < 1 - z.1 ∧ 1 - z.1 < T) ∧ z.2 ∈ Ω ↔
    ((1 - T < z.1 ∧ z.1 < 1 - a) ∧ z.2 ∈ Ω)
  constructor <;> rintro ⟨⟨hlo, hhi⟩, hy⟩ <;> refine ⟨⟨?_, ?_⟩, hy⟩ <;> linarith

/-- Reflection transports an arbitrary closed cylinder to the reversed time cylinder. -/
theorem timeReflection_mem_closedCylinder_iff {d : ℕ} (a T : ℝ)
    (Ω : Set (PDE.Vec d)) (z : TimeVelocity d) :
    timeReflection z ∈ scalarParabolicClosedCylinder a T Ω ↔
      z ∈ scalarParabolicClosedCylinder (1 - T) (1 - a) Ω := by
  change (a ≤ 1 - z.1 ∧ 1 - z.1 ≤ T) ∧ z.2 ∈ closure Ω ↔
    ((1 - T ≤ z.1 ∧ z.1 ≤ 1 - a) ∧ z.2 ∈ closure Ω)
  constructor <;> rintro ⟨⟨hlo, hhi⟩, hy⟩ <;> refine ⟨⟨?_, ?_⟩, hy⟩ <;> linarith

/-- A zero initial/lateral forward solution obeys the signed source time bound. -/
theorem abs_zeroBoundary_forward_le_time {d : ℕ} {Ω : Set (PDE.Vec d)} {a T : ℝ}
    (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (haT : a < T)
    (A : CoefficientField d) (hAc : IsContinuousCoefficient A)
    (hApsd : ∀ t y, (A t y).PosSemidef)
    (u : TimeVelocity d → ℝ)
    (hu : IsScalarC12On u (scalarParabolicOpenCylinder a T Ω))
    (hc : ContinuousOn u (scalarParabolicClosedCylinder a T Ω))
    (hi : ∀ y ∈ closure Ω, u (a, y) = 0)
    (hl : ∀ z ∈ Icc a T ×ˢ frontier Ω, u z = 0)
    (M : ℝ) (hM : 0 ≤ M)
    (hf : ∀ z ∈ scalarParabolicOpenCylinder a T Ω,
      |scalarTimeDerivative u z -
        matrixContraction (coefficientAt A z) (scalarSpatialHessian u z)| ≤ M) :
    ∀ z ∈ scalarParabolicClosedCylinder a T Ω, |u z| ≤ M * (z.1 - a) := by
  let F : ℝ → PDE.Vec d → ℝ := fun t y =>
    -(scalarTimeDerivative u (1 - t, y) -
      matrixContraction (A (1 - t) y) (scalarSpatialHessian u (1 - t, y)))
  have hopen : timeReflection ⁻¹' scalarParabolicOpenCylinder a T Ω =
      scalarParabolicOpenCylinder (1 - T) (1 - a) Ω := by
    ext z
    exact timeReflection_mem_openCylinder_iff a T Ω z
  have hreg := isScalarC12On_timeReflectedScalar hu
  rw [hopen] at hreg
  have hsol : IsClassicalBackwardDirichletSolution (1 - T) (1 - a) Ω
      (timeReflectedCoefficient A) (fun _ _ => 0) (fun _ _ => 0) F
      (fun _ => 0) (fun _ => 0) (timeReflectedScalar u) := by
    refine ⟨hc.comp continuous_timeReflection.continuousOn (fun z hz =>
      (timeReflection_mem_closedCylinder_iff a T Ω z).mpr hz), hreg, ?_, ?_, ?_⟩
    · intro z hz
      have hzu := (timeReflection_mem_openCylinder_iff a T Ω z).mpr hz
      rw [scalarParabolicZeroOrderOperator_apply,
        scalarTimeDerivative_timeReflectedScalar_C12 hu hzu,
        scalarSpatialHessian_timeReflectedScalar_C12]
      simp only [PDE.vecDot, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
      dsimp only [F, timeReflection, coefficientAt, timeReflectedCoefficient]
      ring
    · intro y hy
      change u (1 - (1 - a), y) = 0
      simpa only [sub_sub_cancel] using hi y hy
    · intro z hz
      apply hl (timeReflection z)
      exact ⟨⟨by dsimp [timeReflection]; linarith [hz.1.2],
        by dsimp [timeReflection]; linarith [hz.1.1]⟩, hz.2⟩
  have hbound := abs_zeroBoundary_solution_le_time hΩo hΩb (by linarith)
    (timeReflectedCoefficient A) (isContinuousCoefficient_timeReflected hAc)
    (fun t y => hApsd (1 - t) y) F M hM (fun z hz => by
      simpa only [F, abs_neg, timeReflection, coefficientAt] using
        hf (timeReflection z) ((timeReflection_mem_openCylinder_iff a T Ω z).mpr hz))
    (timeReflectedScalar u) hsol
  intro z hz
  have hz' : timeReflection z ∈
      scalarParabolicClosedCylinder (1 - T) (1 - a) Ω := by
    exact (timeReflection_mem_closedCylinder_iff (1 - T) (1 - a) Ω z).mpr
      (by simpa only [sub_sub_cancel] using hz)
  have hb := hbound (timeReflection z) hz'
  change |u (timeReflection (timeReflection z))| ≤ M * (1 - a - (1 - z.1)) at hb
  rw [timeReflection_involutive z] at hb
  convert hb using 1; ring

/-- A homogeneous replacement with the same forward traces has the sharp residual bound. -/
theorem abs_forward_replacement_error_le_time {d : ℕ} {Ω : Set (PDE.Vec d)}
    {a T : ℝ} (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (haT : a < T)
    (A : CoefficientField d) (hAc : IsContinuousCoefficient A)
    (hApsd : ∀ t y, (A t y).PosSemidef)
    (w v : TimeVelocity d → ℝ)
    (hw : IsScalarC12On w (scalarParabolicOpenCylinder a T Ω))
    (hv : IsScalarC12On v (scalarParabolicOpenCylinder a T Ω))
    (hwc : ContinuousOn w (scalarParabolicClosedCylinder a T Ω))
    (hvc : ContinuousOn v (scalarParabolicClosedCylinder a T Ω))
    (he : EqOn v w (({a} ×ˢ closure Ω) ∪ (Icc a T ×ˢ frontier Ω)))
    (hve : ∀ z ∈ scalarParabolicOpenCylinder a T Ω,
      scalarTimeDerivative v z =
        matrixContraction (coefficientAt A z) (scalarSpatialHessian v z))
    (M : ℝ) (hM : 0 ≤ M)
    (hf : ∀ z ∈ scalarParabolicOpenCylinder a T Ω,
      |scalarTimeDerivative w z -
        matrixContraction (coefficientAt A z) (scalarSpatialHessian w z)| ≤ M) :
    ∀ z ∈ scalarParabolicClosedCylinder a T Ω, |w z - v z| ≤ M * (z.1 - a) := by
  apply abs_zeroBoundary_forward_le_time hΩo hΩb haT A hAc hApsd
    (fun z => w z - v z) (isScalarC12On_sub hw hv) (hwc.sub hvc)
  · intro y hy
    exact sub_eq_zero.mpr (he (Or.inl ⟨mem_singleton a, hy⟩)).symm
  · intro z hz
    exact sub_eq_zero.mpr (he (Or.inr hz)).symm
  · exact hM
  · intro z hz
    rw [scalarTimeDerivative_sub hw hv hz, scalarSpatialHessian_sub hw hv hz]
    have hlin : matrixContraction (coefficientAt A z)
        (scalarSpatialHessian w z - scalarSpatialHessian v z) =
        matrixContraction (coefficientAt A z) (scalarSpatialHessian w z) -
          matrixContraction (coefficientAt A z) (scalarSpatialHessian v z) := by
      simp only [matrixContraction, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]
    rw [hlin, hve z hz]
    have hcancel : scalarTimeDerivative w z -
        matrixContraction (coefficientAt A z) (scalarSpatialHessian v z) -
          (matrixContraction (coefficientAt A z) (scalarSpatialHessian w z) -
            matrixContraction (coefficientAt A z) (scalarSpatialHessian v z)) =
        scalarTimeDerivative w z -
          matrixContraction (coefficientAt A z) (scalarSpatialHessian w z) := by ring
    rw [hcancel]
    exact hf z hz

/-- The forward replacement error is uniformly bounded over the entire finite horizon. -/
theorem abs_forward_replacement_error_le_horizon {d : ℕ} {Ω : Set (PDE.Vec d)}
    {a T : ℝ} (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (haT : a < T)
    (A : CoefficientField d) (hAc : IsContinuousCoefficient A)
    (hApsd : ∀ t y, (A t y).PosSemidef)
    (w v : TimeVelocity d → ℝ)
    (hw : IsScalarC12On w (scalarParabolicOpenCylinder a T Ω))
    (hv : IsScalarC12On v (scalarParabolicOpenCylinder a T Ω))
    (hwc : ContinuousOn w (scalarParabolicClosedCylinder a T Ω))
    (hvc : ContinuousOn v (scalarParabolicClosedCylinder a T Ω))
    (he : EqOn v w (({a} ×ˢ closure Ω) ∪ (Icc a T ×ˢ frontier Ω)))
    (hve : ∀ z ∈ scalarParabolicOpenCylinder a T Ω,
      scalarTimeDerivative v z =
        matrixContraction (coefficientAt A z) (scalarSpatialHessian v z))
    (M : ℝ) (hM : 0 ≤ M)
    (hf : ∀ z ∈ scalarParabolicOpenCylinder a T Ω,
      |scalarTimeDerivative w z -
        matrixContraction (coefficientAt A z) (scalarSpatialHessian w z)| ≤ M) :
    ∀ z ∈ scalarParabolicClosedCylinder a T Ω, |w z - v z| ≤ M * (T - a) := by
  intro z hz
  exact (abs_forward_replacement_error_le_time hΩo hΩb haT A hAc hApsd
    w v hw hv hwc hvc he hve M hM hf z hz).trans
      (mul_le_mul_of_nonneg_left (sub_le_sub_right hz.1.2 a) hM)

end HypoellipticAleksandrov.Parabolic.LocalHolder
