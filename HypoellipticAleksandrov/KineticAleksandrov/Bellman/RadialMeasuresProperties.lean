module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.RadialMeasuresComparison
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.RadialMeasuresNonzero
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.RadialMeasuresDegree

/-! # Radon, comparison, nontriviality, and degree properties of the literal radial pair -/

@[expose] public section
noncomputable section
open MeasureTheory
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- All measure-theoretic adjoint requirements hold before stationarity is established. -/
theorem radial_bellman_measure_properties (lam Lam alpha : ℝ) (_hlam : 0 < lam)
    (_hLam : lam ≤ Lam) (_ha : 0 < alpha) (_ha1 : alpha < 1)
    (pi : Measure (BellmanSphere × BellmanCoefficient lam Lam)) [IsProbabilityMeasure pi] :
    IsBellmanRadon (radialMu alpha pi) ∧ IsBellmanRadon (radialEta alpha pi) ∧
      (radialMu alpha pi ≠ 0 ∨ radialEta alpha pi ≠ 0) ∧
      ENNReal.ofReal lam • radialMu alpha pi ≤ radialEta alpha pi ∧
      radialEta alpha pi ≤ ENNReal.ofReal Lam • radialMu alpha pi ∧
      HasBellmanDensityDegree (2 + alpha) (radialMu alpha pi) ∧
      HasBellmanDensityDegree (2 + alpha) (radialEta alpha pi) := by
  obtain ⟨hm, he⟩ := radial_bellman_measures_radon alpha pi
  obtain ⟨hlo, hhi⟩ := radial_bellman_measures_comparison alpha pi
  exact ⟨hm, he, Or.inl (radialMu_ne_zero alpha pi), hlo, hhi,
    radialMu_densityDegree alpha pi, radialEta_densityDegree alpha pi⟩

end HypoellipticAleksandrov.KineticAleksandrov
