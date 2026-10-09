module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelContract
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonConstant
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonGeometry
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-! # Source localisation and the perturbed backward operator -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov.Parabolic MeasureTheory Set
open scoped ENNReal

/-- Backward cylinders are open in the existing physical coordinate topology. -/
theorem isOpen_backwardCylinder {d : ℕ} (P₀ : KineticPoint d) (R : ℝ) (hR : 0 < R) :
    IsOpen (backwardCylinder P₀ R) := by
  have ho := isOpen_forwardCylinder (kineticReflection P₀) R hR
  rw [← kineticReflection_image_backwardCylinder P₀ R hR] at ho
  exact (kineticReflectionHomeomorph d).isOpen_image.mp ho

/-- Local continuity of the solution suffices for its positive-set source localisation. -/
theorem borelSource_memLp {d : ℕ} {D : Set (KineticPoint d)} (hD : IsOpen D)
    (localised : Bool) (u f : KineticPoint d → ℝ) (hu : ContinuousOn u D)
    {p : ℝ≥0∞} (hf : MemLp (fun P => max (f P) 0) p (volume.restrict D)) :
    MemLp (borelSource localised u f) p (volume.restrict D) := by
  cases localised
  · exact hf
  · have hS : MeasurableSet (D ∩ {P | 0 < u P}) :=
      (hu.isOpen_inter_preimage hD isOpen_Ioi).measurableSet
    have heq : (D ∩ {P | 0 < u P}).indicator (fun P => max (f P) 0) =ᵐ[volume.restrict D]
        borelSource true u f := by
      filter_upwards [ae_restrict_mem hD.measurableSet] with P hP
      simp only [indicator,mem_inter_iff,mem_ofPred_eq,hP,true_and,borelSource,
        ite_true]
    exact (hf.indicator hS).ae_eq heq

/-- The operator change is precisely minus the coefficient Hessian contraction. -/
theorem borel_backwardOperator_sub {d : ℕ} (C A : CoefficientField d)
    (u : KineticPoint d → ℝ) (P : KineticPoint d) :
    backwardOperatorOfTimeVelocityCoefficient C u P -
      backwardOperatorOfTimeVelocityCoefficient A u P =
      -matrixContraction (C P.time P.velocity - A P.time P.velocity)
        (kineticVelocityHessian u P) := by
  rw [backwardOperatorOfTimeVelocityCoefficient_apply,
    backwardOperatorOfTimeVelocityCoefficient_apply]
  unfold matrixContraction
  simp only [Matrix.sub_apply,sub_mul,Finset.sum_sub_distrib]
  ring

end HypoellipticAleksandrov.KineticAleksandrov
