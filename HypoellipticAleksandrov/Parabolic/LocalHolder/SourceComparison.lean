module

public import HypoellipticAleksandrov.Parabolic.ScalarDirichletData
import HypoellipticAleksandrov.Parabolic.ScalarDirichletComparison
import HypoellipticAleksandrov.Parabolic.C2ToScalarC12

/-! # Signed-source comparison on bounded parabolic cylinders

The affine time barrier bounds supplied zero-boundary backward corrections. The
replacement construction reflects this estimate to the forward initial/lateral problem.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Set

/-- The backward source barrier, independent of velocity. -/
def sourceTimeBarrier {n : ℕ} (M T : ℝ) (z : TimeVelocity n) : ℝ := M * (T - z.1)

/-- The source time barrier is smooth. -/
theorem contDiff_sourceTimeBarrier {n : ℕ} (M T : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (@sourceTimeBarrier n M T) :=
  contDiff_const.mul (contDiff_const.sub contDiff_fst)

/-- The barrier's scalar time derivative is minus its amplitude. -/
theorem scalarTimeDerivative_sourceTimeBarrier {n : ℕ} (M T : ℝ) (z : TimeVelocity n) :
    scalarTimeDerivative (sourceTimeBarrier M T) z = -M := by
  change deriv (fun r : ℝ => M * (T - r)) z.1 = -M
  have h := ((hasDerivAt_const z.1 T).sub (hasDerivAt_id z.1)).const_mul M
  simpa only [Pi.sub_apply, id_eq, zero_sub, mul_neg, mul_one] using h.deriv

/-- Velocity differentiation annihilates the time barrier. -/
theorem scalarSpatialGradient_sourceTimeBarrier {n : ℕ} (M T : ℝ) (z : TimeVelocity n) :
    scalarSpatialGradient (sourceTimeBarrier M T) z = 0 := by
  ext i
  simp only [scalarSpatialGradient, sourceTimeBarrier, PDE.classicalGradient,
    fderiv_const_apply, zero_apply, Pi.zero_apply]

/-- The time barrier has zero spatial Hessian. -/
theorem scalarSpatialHessian_sourceTimeBarrier {n : ℕ} (M T : ℝ) (z : TimeVelocity n) :
    scalarSpatialHessian (sourceTimeBarrier M T) z = 0 := by
  have heq : (fun y : PDE.Vec n =>
      PDE.classicalGradient (fun w => sourceTimeBarrier M T (z.1, w)) y) =
      fun _ => (0 : PDE.Vec n) := by
    funext y
    exact scalarSpatialGradient_sourceTimeBarrier M T (z.1, y)
  ext i j
  change (fderiv ℝ (fun y : PDE.Vec n =>
    PDE.classicalGradient (fun w => sourceTimeBarrier M T (z.1, w)) y) z.2
      (PDE.basisVec i)) j = 0
  rw [heq, fderiv_const_apply]
  rfl

/-- The scalar backward operator of the barrier is the constant source minus M. -/
theorem scalarOperator_sourceTimeBarrier {n : ℕ} (A : CoefficientField n)
    (M T : ℝ) (z : TimeVelocity n) :
    scalarParabolicZeroOrderOperator A (fun _ _ => 0) (fun _ _ => 0)
      (sourceTimeBarrier M T) z = -M := by
  rw [scalarParabolicZeroOrderOperator_apply, scalarTimeDerivative_sourceTimeBarrier,
    scalarSpatialGradient_sourceTimeBarrier, scalarSpatialHessian_sourceTimeBarrier]
  simp only [matrixContraction, Matrix.zero_apply, mul_zero, Finset.sum_const_zero,
    PDE.vecDot, Pi.zero_apply, zero_mul, add_zero]

/-- The barrier has its literal terminal and lateral boundary data. -/
theorem sourceTimeBarrier_isClassicalBackward {n : ℕ} (A : CoefficientField n)
    (a T M : ℝ) (Ω : Set (PDE.Vec n)) :
    IsClassicalBackwardDirichletSolution a T Ω A (fun _ _ => 0) (fun _ _ => 0)
      (fun _ _ => -M) (fun _ => 0) (sourceTimeBarrier M T) (sourceTimeBarrier M T) := by
  refine ⟨(contDiff_sourceTimeBarrier M T).continuous.continuousOn,
    isScalarC12On_of_contDiff_two
      ((contDiff_sourceTimeBarrier M T).of_le (by simp)) _, ?_, ?_, ?_⟩
  · intro z hz
    exact scalarOperator_sourceTimeBarrier A M T z
  · intro y hy
    simp only [sourceTimeBarrier, sub_self, mul_zero]
  · intro z hz
    rfl

/-- A signed bounded source gives the sharp finite-horizon bound for zero-boundary solutions. -/
theorem abs_zeroBoundary_solution_le_time {n : ℕ} {Ω : Set (PDE.Vec n)} {a T : ℝ}
    (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (haT : a < T)
    (A : CoefficientField n) (hAc : IsContinuousCoefficient A)
    (hApsd : ∀ t v, (A t v).PosSemidef)
    (F : ℝ → PDE.Vec n → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hF : ∀ z ∈ scalarParabolicOpenCylinder a T Ω, |F z.1 z.2| ≤ M)
    (u : TimeVelocity n → ℝ)
    (hu : IsClassicalBackwardDirichletSolution a T Ω A
      (fun _ _ => 0) (fun _ _ => 0) F (fun _ => 0) (fun _ => 0) u) :
    ∀ z ∈ scalarParabolicClosedCylinder a T Ω, |u z| ≤ M * (T - z.1) := by
  have hupper := le_on_closedCylinder_of_isClassicalBackwardDirichletSolution
    hΩo hΩb haT A (fun _ _ => 0) (fun _ _ => 0) hAc continuous_const hApsd
    (fun _ _ => le_rfl) F (fun _ _ => -M) (fun _ => 0) (fun _ => 0)
    (fun _ => 0) (sourceTimeBarrier M T) u (sourceTimeBarrier M T)
    hu (sourceTimeBarrier_isClassicalBackward A a T M Ω)
    (fun z hz => (abs_le.mp (hF z hz)).1) (fun _ _ => le_rfl)
    (fun z hz => mul_nonneg hM (sub_nonneg.mpr hz.1.2))
  have hlower := le_on_closedCylinder_of_isClassicalBackwardDirichletSolution
    hΩo hΩb haT A (fun _ _ => 0) (fun _ _ => 0) hAc continuous_const hApsd
    (fun _ _ => le_rfl) (fun _ _ => -(-M)) F (fun _ => 0) (fun _ => 0)
    (sourceTimeBarrier (-M) T) (fun _ => 0) (sourceTimeBarrier (-M) T) u
    (sourceTimeBarrier_isClassicalBackward A a T (-M) Ω) hu
    (fun z hz => by simpa only [neg_neg] using (abs_le.mp (hF z hz)).2) (fun _ _ => le_rfl)
    (fun z hz => mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hM)
      (sub_nonneg.mpr hz.1.2))
  intro z hz
  apply abs_le.mpr
  constructor
  · simpa only [sourceTimeBarrier, neg_mul] using hlower z hz
  · exact hupper z hz

end HypoellipticAleksandrov.Parabolic.LocalHolder
