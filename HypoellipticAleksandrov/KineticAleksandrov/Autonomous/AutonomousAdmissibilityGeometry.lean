module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ScalarAdapters
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.AdmissibilityCalculus
import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.GreenPotentialsRegularity
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonLinear
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonLinear
import Mathlib.Tactic

/-! # The autonomous lift and smooth-near test regularity -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Parabolic Holder Set MeasureTheory Evolution TheoremA
open scoped MatrixOrder

/-- The scalar autonomous lift is Borel on the literal kinetic carrier. -/
theorem autonomous_lift_measurable {a : ℝ → ℝ → ℝ}
    (ha : Measurable (Function.uncurry a)) :
    Measurable (fullKineticCoefficientAt (autonomousCoefficient a)) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  exact ha.comp (((continuous_apply 0).comp continuous_position).measurable.prodMk
    (((continuous_apply 0).comp continuous_velocity).measurable))

/-- The one-dimensional lift is symmetric at every point. -/
theorem autonomous_lift_symm (a : ℝ → ℝ → ℝ) (P : Point) :
    (fullKineticCoefficientAt (autonomousCoefficient a) P).IsSymm := by
  ext i j
  rfl

/-- The scalar range gives pointwise matrix ellipticity without an exceptional set. -/
theorem autonomous_lift_elliptic {a : ℝ → ℝ → ℝ} {lam Lam : ℝ}
    (hb : ∀ x v, lam ≤ a x v ∧ a x v ≤ Lam) (P : Point) :
    lam • (1 : PDE.Mat 1) ≤ fullKineticCoefficientAt (autonomousCoefficient a) P ∧
      fullKineticCoefficientAt (autonomousCoefficient a) P ≤ Lam • (1 : PDE.Mat 1) := by
  have he : fullKineticCoefficientAt (autonomousCoefficient a) P =
      a (P.position 0) (P.velocity 0) • (1 : PDE.Mat 1) := by
    ext i j
    fin_cases i
    fin_cases j
    simp [fullKineticCoefficientAt, autonomousCoefficient]
  rw [he]
  have hI : (0 : PDE.Mat 1) ≤ 1 :=
    Matrix.nonneg_iff_posSemidef.mpr Matrix.PosSemidef.one
  exact ⟨smul_le_smul_of_nonneg_right (hb _ _).1 hI,
    smul_le_smul_of_nonneg_right (hb _ _).2 hI⟩

/-- Source-near smooth tests have the existing anisotropic classical regularity. -/
theorem smoothNear_regular {psi : Point → ℝ} {E : Set Point}
    (hpsi : IsSmoothNear psi E) : ∃ U : Set Point,
      IsOpen U ∧ E ⊆ U ∧ IsKineticC112On psi U := by
  obtain ⟨U, hU, hEU, hs⟩ := hpsi
  refine ⟨U, hU, hEU, isKineticC112On_of_contDiffOn hU ?_⟩
  have h := hs.comp (evolutionProdCLE 1).contDiff.contDiffOn (by
    intro x hx
    exact ⟨evolutionHomeomorph 1 x, hx, rfl⟩)
  exact h

/-- The full backward operator is additive on the existing C112 class. -/
theorem autonomous_operator_add {u v : Point → ℝ} {D : Set Point}
    (hu : IsKineticC112On u D) (hv : IsKineticC112On v D)
    (a : ℝ → ℝ → ℝ) {P : Point} (hP : P ∈ D) :
    autonomousScalarOperator a (fun Q => u Q + v Q) P =
      autonomousScalarOperator a u P + autonomousScalarOperator a v P := by
  rw [autonomousScalarOperator_apply,
    comparison_time_add (hu.timeSlice_differentiableAt hP) (hv.timeSlice_differentiableAt hP),
    show kineticPositionGradient (fun Q => u Q + v Q) P =
      kineticPositionGradient u P + kineticPositionGradient v P from classicalGradient_add
        ((hu.positionSlice_contDiffAt hP).differentiableAt (by norm_num))
        ((hv.positionSlice_contDiffAt hP).differentiableAt (by norm_num)),
    comparison_hessian_add (hu.velocitySlice_contDiffAt hP) (hv.velocitySlice_contDiffAt hP)]
  simp only [autonomousScalarOperator_apply, Pi.add_apply, Matrix.add_apply]
  ring

/-- Scalar multiplication commutes with the autonomous operator on C112 functions. -/
theorem autonomous_operator_const_mul {u : Point → ℝ} {D : Set Point}
    (hu : IsKineticC112On u D) (c : ℝ) (a : ℝ → ℝ → ℝ)
    {P : Point} (hP : P ∈ D) :
    autonomousScalarOperator a (fun Q => c * u Q) P = c * autonomousScalarOperator a u P := by
  rw [autonomousScalarOperator_apply,
    show kineticTimeDerivative (fun Q => c * u Q) P = c * kineticTimeDerivative u P from
      deriv_const_mul c (hu.timeSlice_differentiableAt hP),
    show kineticPositionGradient (fun Q => c * u Q) P = c • kineticPositionGradient u P from
      classicalGradient_const_mul c
        ((hu.positionSlice_contDiffAt hP).differentiableAt (by norm_num))]
  have hh : kineticVelocityHessian (fun Q => c * u Q) P = c • kineticVelocityHessian u P := by
    simp only [kineticVelocityHessian_eq_sliceHessian]
    exact sliceHessian_const_mul c (hu.velocitySlice_contDiffAt hP)
  rw [hh]
  simp only [autonomousScalarOperator_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
  ring

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
