module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionMeasurableConstruction
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.SmoothFamily

/-! # The unconditional Appendix C counterexample -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov
open Filter MeasureTheory Counterexample
open scoped MatrixOrder

/-- Autonomous counterexamples for every finite exponent below `4d`, with fixed shared
ellipticity bounds and cylinder, constructed internally in both coefficient classes. -/
theorem kinetic_aleksandrov_autonomous_counterexample_aux
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
  apply construction_of_families ?_ d hd p hp hpd
  intro d hd p hp hpd
  have hm := measurableFamily_holds d hd p hp hpd
  exact ⟨hm, smoothFamily_of_measurable hp
    (counterParameters_pos d hd p hp hpd).2.2 hm⟩

end HypoellipticAleksandrov.KineticAleksandrov
