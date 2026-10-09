module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Realization
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Matrix.Order

/-! # Scalar coefficient consequences of the Section Two hypotheses -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation
open HypoellipticAleksandrov SectionTwo
open scoped ContDiff MatrixOrder

/-- Full smoothness restricts to the time--velocity coefficient. -/
theorem sectionTwoCoefficient_smooth {d : ℕ} {lam Lam : ℝ} {B : CoefficientField d}
    (hB : IsSectionTwoCoefficient lam Lam B) : IsSmoothCoefficient B := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  have he : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : ℝ × PDE.Vec d => (q.1, (q.2, (0 : PDE.Vec d)))) := by fun_prop
  exact (hB.2.2.1 i j).comp he

/-- Lower ellipticity implies positive semidefiniteness. -/
theorem sectionTwoCoefficient_posSemidef {d : ℕ} {lam Lam : ℝ}
    {B : CoefficientField d} (hB : IsSectionTwoCoefficient lam Lam B) (r : ℝ)
    (v : PDE.Vec d) : (B r v).PosSemidef := by
  have hzero : (0 : PDE.Mat d) ≤ lam • (1 : PDE.Mat d) :=
    smul_nonneg hB.1.le (Matrix.nonneg_iff_posSemidef.mpr Matrix.PosSemidef.one)
  exact Matrix.nonneg_iff_posSemidef.mp (hzero.trans (hB.2.2.2.2.1 r v))

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
