module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.SmoothFamilyError
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.MollifySource
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-! # Positive sources under a fixed-function change of autonomous coefficients -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory HypoellipticAleksandrov.Parabolic
open scoped ENNReal Matrix.Norms.Elementwise

/-- Entrywise measurable autonomous coefficients and genuine smooth jets
give a measurable operator. -/
theorem measurable_backwardOperator_of_joint_smooth {d : ℕ}
    (A : XV d → PDE.Mat d) (hA : ∀ i k, Measurable (fun q => A q i k))
    (u : KineticPoint d → ℝ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × XV d =>
      u ((KineticPoint.equivProd d).symm q))) :
    Measurable (backwardOperator (fun _t x v => A (x, v)) u) := by
  have hr := isKineticC112On_univ_of_joint_smooth u hu
  have ht := (continuousOn_univ.mp hr.continuousOn_kineticTimeDerivative).measurable
  have hx := (continuousOn_univ.mp hr.continuousOn_kineticPositionGradient).measurable
  have hv i k : Measurable (fun P => kineticVelocityHessian u P i k) :=
    ((continuous_apply k).comp ((continuous_apply i).comp
      (continuousOn_univ.mp hr.continuousOn_kineticVelocityHessian))).measurable
  have hsp : Measurable (fun P : KineticPoint d => (P.position, P.velocity)) :=
    (continuous_position.prodMk continuous_velocity).measurable
  have hT : Measurable (fun P => PDE.vecDot P.velocity (kineticPositionGradient u P)) := by
    unfold PDE.vecDot
    exact Finset.measurable_sum _ (fun i _ =>
      ((measurable_pi_apply i).comp continuous_velocity.measurable).mul
        ((measurable_pi_apply i).comp hx))
  have hC : Measurable (fun P => matrixContraction (A (P.position, P.velocity))
      (kineticVelocityHessian u P)) := by
    unfold matrixContraction
    exact Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _ (fun k _ =>
      ((hA i k).comp hsp).mul
        (hv i k)))
  exact (ht.add hT).sub hC

/-- The full backward-operator change is minus the exact coefficient Hessian error. -/
theorem backwardOperator_coefficient_change {d : ℕ} (A B : XV d → PDE.Mat d)
    (u : KineticPoint d → ℝ) (P : KineticPoint d) :
    backwardOperator (fun _t x v => B (x, v)) u P =
      backwardOperator (fun _t x v => A (x, v)) u P -
        matrixContraction (B (P.position, P.velocity) - A (P.position, P.velocity))
          (kineticVelocityHessian u P) := by
  unfold backwardOperator fullKineticCoefficientAt matrixContraction
  simp only [Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]
  ring

/-- The positive source norm increases by at most the full contraction-error norm. -/
theorem positive_source_norm_le_coefficient_error {d : ℕ}
    (A B : XV d → PDE.Mat d)
    (hA : ∀ i k, Measurable (fun q => A q i k))
    (hB : ∀ i k, Measurable (fun q => B q i k))
    (u : KineticPoint d → ℝ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × XV d =>
      u ((KineticPoint.equivProd d).symm q)))
    (nu : Measure (KineticPoint d)) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    eLpNorm (fun P => max (backwardOperator (fun _t x v => B (x, v)) u P) 0) p nu ≤
      eLpNorm (fun P => max (backwardOperator (fun _t x v => A (x, v)) u P) 0) p nu +
      eLpNorm (fun P => matrixContraction (B (P.position, P.velocity) - A (P.position, P.velocity))
        (kineticVelocityHessian u P)) p nu := by
  let E := fun P => matrixContraction (B (P.position, P.velocity) - A (P.position, P.velocity))
    (kineticVelocityHessian u P)
  have hma := measurable_backwardOperator_of_joint_smooth A hA u hu
  have hmb := measurable_backwardOperator_of_joint_smooth B hB u hu
  have he : Measurable E := by
    have h := hma.sub hmb
    convert h using 1
    funext P
    simp only [Pi.sub_apply]
    rw [backwardOperator_coefficient_change A B u P]
    dsimp [E]
    ring
  have hf := (hmb.max (measurable_const (a := (0 : ℝ)))).aestronglyMeasurable (μ := nu)
  have hm := eLpNorm_mono_ae_real (p := p) hf
    (Filter.Eventually.of_forall (fun P => show
      ‖max (backwardOperator (fun _t x v => B (x, v)) u P) 0‖ ≤
        max (backwardOperator (fun _t x v => A (x, v)) u P) 0 + ‖E P‖ from by
      rw [Real.norm_of_nonneg (le_max_right _ _), backwardOperator_coefficient_change A B u P]
      simpa only [sub_eq_add_neg, abs_neg, Real.norm_eq_abs] using!
        positive_part_add_le (backwardOperator (fun _t x v => A (x, v)) u P)
          (max (backwardOperator (fun _t x v => A (x, v)) u P) 0) (-(E P))
          (le_max_right _ _) (le_max_left _ _)))
  exact hm.trans ((eLpNorm_add_le hp).trans_eq
    (by rw [eLpNorm_norm E he.aestronglyMeasurable]))

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
