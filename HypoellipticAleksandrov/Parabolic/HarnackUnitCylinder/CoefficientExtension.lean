module

public import HypoellipticAleksandrov.Coefficients.ParabolicRegularization
public import HypoellipticAleksandrov.Parabolic.LocalClassical

/-! # Borel midpoint extension of locally continuous coefficients -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Set MeasureTheory

/-- The product measurable structure on finite coefficient matrices. -/
local instance unitCylinderMatrixMeasurableSpace (d : ℕ) : MeasurableSpace (PDE.Mat d) := by
  unfold PDE.Mat Matrix
  infer_instance

/-- Local continuity suffices for a Borel midpoint extension from an open set. -/
theorem isBorel_midpointExtension_of_continuousOn
    {d : ℕ} {U : Set (TimeVelocity d)} {B : CoefficientField d}
    (hU : IsOpen U) (hB : IsContinuousCoefficientOn B U) (lam Lam : ℝ) :
    IsBorelCoefficient
      (extendCoefficientByMidpoint B U (ellipticityMidpoint d lam Lam)) := by
  classical
  change Measurable (U.piecewise (coefficientAt B) (fun _ => ellipticityMidpoint d lam Lam))
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  have hc : ContinuousOn (fun z => coefficientAt B z i j) U :=
    (continuous_apply j).comp_continuousOn
      ((continuous_apply i).comp_continuousOn hB)
  have hm := hc.measurable_piecewise
    (g := fun _ => ellipticityMidpoint d lam Lam i j) continuousOn_const hU.measurableSet
  convert hm using 1
  funext z
  by_cases hz : z ∈ U <;> simp only [Set.piecewise, hz, ite_true, ite_false]

end HypoellipticAleksandrov.Parabolic
