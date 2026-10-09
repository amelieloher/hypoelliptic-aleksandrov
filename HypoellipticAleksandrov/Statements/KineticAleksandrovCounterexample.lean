module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Construction
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Setting
public import HypoellipticAleksandrov.KineticAleksandrov.Operator
public import HypoellipticAleksandrov.Geometry.KineticPointMeasure
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Counterexample below the critical exponent

Companion paper, Proposition C.1.
-/

@[expose] public section

open Filter MeasureTheory
open scoped MatrixOrder

namespace HypoellipticAleksandrov.KineticAleksandrov

/-- Autonomous counterexamples below `4d`, with shared fixed bounds and cylinder. -/
theorem kinetic_aleksandrov_autonomous_counterexample
    (d : ℕ) (hd : 1 ≤ d) (p : ℝ) (hp : 1 ≤ p) (hpd : p < 4 * (d : ℝ)) :
    ∃ lam Lam : ℝ, ∃ P₀ : KineticPoint d, ∃ R : ℝ,
      0 < lam ∧ lam ≤ Lam ∧ 0 < R ∧
      ((∃ A : (PDE.Vec d × PDE.Vec d) → PDE.Mat d,
        ∃ U : ℕ → KineticPoint d → ℝ,
          (∀ i k, Measurable (fun z => A z i k)) ∧
          (∀ z, lam • (1 : PDE.Mat d) ≤ A z ∧ A z ≤ Lam • (1 : PDE.Mat d)) ∧
          (∀ j, ContDiff ℝ (⊤ : ℕ∞)
            (fun q : ℝ × (PDE.Vec d × PDE.Vec d) =>
              U j ((KineticPoint.equivProd d).symm q))) ∧
          (∀ j P, 0 ≤ U j P) ∧
          (∀ j P, P ∈ initialFullLateralBoundary P₀ R → U j P = 0) ∧
          (∀ j, ∃ P ∈ backwardCylinder P₀ R, (1 / 4 : ℝ) ≤ U j P) ∧
          Tendsto (fun j => eLpNorm
            (fun P => max (backwardOperator (fun _t x v => A (x, v)) (U j) P) 0)
            (ENNReal.ofReal p) (volume.restrict (backwardCylinder P₀ R)))
            atTop (nhds 0)) ∧
       (∃ A : ℕ → (PDE.Vec d × PDE.Vec d) → PDE.Mat d,
        ∃ U : ℕ → KineticPoint d → ℝ,
          (∀ j i k, ContDiff ℝ (⊤ : ℕ∞) (fun z => A j z i k)) ∧
          (∀ j z, lam • (1 : PDE.Mat d) ≤ A j z ∧
            A j z ≤ Lam • (1 : PDE.Mat d)) ∧
          (∀ j, ContDiff ℝ (⊤ : ℕ∞)
            (fun q : ℝ × (PDE.Vec d × PDE.Vec d) =>
              U j ((KineticPoint.equivProd d).symm q))) ∧
          (∀ j P, 0 ≤ U j P) ∧
          (∀ j P, P ∈ initialFullLateralBoundary P₀ R → U j P = 0) ∧
          (∀ j, ∃ P ∈ backwardCylinder P₀ R, (1 / 4 : ℝ) ≤ U j P) ∧
          Tendsto (fun j => eLpNorm
            (fun P => max (backwardOperator (fun _t x v => A j (x, v)) (U j) P) 0)
            (ENNReal.ofReal p) (volume.restrict (backwardCylinder P₀ R)))
            atTop (nhds 0))) := by
  exact HypoellipticAleksandrov.KineticAleksandrov.kinetic_aleksandrov_autonomous_counterexample_aux
    d hd p hp hpd

end HypoellipticAleksandrov.KineticAleksandrov
