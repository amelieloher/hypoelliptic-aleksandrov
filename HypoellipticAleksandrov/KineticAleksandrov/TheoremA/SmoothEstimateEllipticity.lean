module

public import HypoellipticAleksandrov.Coefficients.Ellipticity
import Mathlib.MeasureTheory.Measure.OpenPos

/-! # Everywhere ellipticity of continuous time--velocity coefficients -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.TheoremA
open MeasureTheory Set
open scoped MatrixOrder Matrix.Norms.Elementwise

/-- A continuous coefficient's almost-everywhere lower bound holds everywhere. -/
theorem lowerEllipticity_of_continuous_ae {d : ℕ} {lam : ℝ}
    {A : CoefficientField d} (hA : IsContinuousCoefficient A)
    (hlo : HasLowerEllipticityAE lam A) : HasLowerEllipticity lam A := by
  have hc : IsClosed {z : ℝ × PDE.Vec d | lam • (1 : PDE.Mat d) ≤ coefficientAt A z} :=
    isClosed_le continuous_const hA
  have hd := (volume : Measure (ℝ × PDE.Vec d)).dense_of_ae hlo
  intro t v
  exact hc.closure_subset (hd (t, v))

/-- A continuous coefficient's almost-everywhere upper bound holds everywhere. -/
theorem upperEllipticity_of_continuous_ae {d : ℕ} {Lam : ℝ}
    {A : CoefficientField d} (hA : IsContinuousCoefficient A)
    (hhi : HasUpperEllipticityAE Lam A) : HasUpperEllipticity Lam A := by
  have hc : IsClosed {z : ℝ × PDE.Vec d | coefficientAt A z ≤ Lam • (1 : PDE.Mat d)} :=
    isClosed_le hA continuous_const
  have hd := (volume : Measure (ℝ × PDE.Vec d)).dense_of_ae hhi
  intro t v
  exact hc.closure_subset (hd (t, v))

/-- Smoothness supplies the continuity needed to recover both pointwise bounds. -/
theorem ellipticity_of_smooth_ae {d : ℕ} {lam Lam : ℝ}
    {A : CoefficientField d} (hA : IsSmoothCoefficient A)
    (hlo : HasLowerEllipticityAE lam A) (hhi : HasUpperEllipticityAE Lam A) :
    HasLowerEllipticity lam A ∧ HasUpperEllipticity Lam A :=
  ⟨lowerEllipticity_of_continuous_ae hA.continuous hlo,
    upperEllipticity_of_continuous_ae hA.continuous hhi⟩

end HypoellipticAleksandrov.KineticAleksandrov.TheoremA
