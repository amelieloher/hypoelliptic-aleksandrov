module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionGeometry
public import HypoellipticAleksandrov.Geometry.KineticPointMeasure

/-! # Sequence-constructor interface for the Appendix C construction

The family propositions are the two conjuncts of the construction's conclusion. Parameters
are selected from the internally proved profile and fixed-cylinder geometry.
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open Filter MeasureTheory
open scoped MatrixOrder

/-- The subcritical exponent is fixed before all profile and sequence choices. -/
noncomputable def counterAlpha (d : ℕ) (p : ℝ) : ℝ := by
  classical
  exact if h : 1 ≤ d ∧ 1 ≤ p ∧ p < 4 * (d : ℝ) then
    (exists_subcritical_alpha d h.1 p h.2.1 h.2.2).choose else 1 / 2

/-- The selected exponent satisfies the full source range and positive norm exponent. -/
theorem counterAlpha_spec (d : ℕ) (hd : 1 ≤ d) (p : ℝ)
    (hp : 1 ≤ p) (hpd : p < 4 * (d : ℝ)) :
    0 < counterAlpha d p ∧ counterAlpha d p < 1 ∧
      0 < counterAlpha d p - 2 + 4 * (d : ℝ) / p := by
  classical
  simp only [counterAlpha, dite_eq_left (And.intro hd (And.intro hp hpd))]
  exact (exists_subcritical_alpha d hd p hp hpd).choose_spec

/-- The internally proved profile at the one fixed selected exponent. -/
theorem counterProfileFor (d : ℕ) (hd : 1 ≤ d) (p : ℝ)
    (hp : 1 ≤ p) (hpd : p < 4 * (d : ℝ)) :
    CounterProfileStatement d (counterAlpha d p) :=
  counterProfile_holds d hd (counterAlpha d p)
    (counterAlpha_spec d hd p hp hpd).1 (counterAlpha_spec d hd p hp hpd).2.1

/-- Joint ellipticity bounds and cylinder parameters, independent of the sequence index. -/
noncomputable def counterParameters (d : ℕ) (p : ℝ) : ℝ × ℝ × KineticPoint d × ℝ := by
  classical
  exact if hvalid : 1 ≤ d ∧ 1 ≤ p ∧ p < 4 * (d : ℝ) then
    let h := counterProfileFor d hvalid.1 p hvalid.2.1 hvalid.2.2
    let geom := construction_fixed_geometry_of_profile hvalid.1
      (counterAlpha_spec d hvalid.1 p hvalid.2.1 hvalid.2.2).1 h
    let mu := geom.choose_spec.choose
    let S := geom.choose_spec.choose_spec.choose
    (profileLowerEllipticity h, profileUpperEllipticity h, ⟨barrierTime mu, 0, 0⟩, S)
  else (1, 1, ⟨0, 0, 0⟩, 1)

/-- The selected joint parameters have the required positive bounds and cylinder radius. -/
theorem counterParameters_pos (d : ℕ) (hd : 1 ≤ d) (p : ℝ)
    (hp : 1 ≤ p) (hpd : p < 4 * (d : ℝ)) :
    0 < (counterParameters d p).1 ∧
      (counterParameters d p).1 ≤ (counterParameters d p).2.1 ∧
      0 < (counterParameters d p).2.2.2 := by
  classical
  let h := counterProfileFor d hd p hp hpd
  let geom := construction_fixed_geometry_of_profile hd (counterAlpha_spec d hd p hp hpd).1 h
  have hs := geom.choose_spec.choose_spec.choose_spec
  have hp0 := (selectedProfile_spec h).1
  have hp1 := (selectedProfile_spec h).2.1
  simpa only [counterParameters, dite_eq_left (And.intro hd (And.intro hp hpd))] using
    And.intro hp0 (And.intro hp1 hs.2.2.1)

/-- The measurable-coefficient family statement. -/
def MeasurableFamilyStatement (d : ℕ) (p lam Lam : ℝ) (P₀ : KineticPoint d)
    (R : ℝ) : Prop :=
  ∃ A : (PDE.Vec d × PDE.Vec d) → PDE.Mat d,
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
            atTop (nhds 0)

/-- The smooth-coefficient family statement. -/
def SmoothFamilyStatement (d : ℕ) (p lam Lam : ℝ) (P₀ : KineticPoint d)
    (R : ℝ) : Prop :=
  ∃ A : ℕ → (PDE.Vec d × PDE.Vec d) → PDE.Mat d,
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
            atTop (nhds 0)

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

namespace HypoellipticAleksandrov.KineticAleksandrov

open Counterexample Filter MeasureTheory
open scoped MatrixOrder

/-- The two family statements at the one selected tuple give the construction. -/
theorem construction_of_families
    (hfamilies : ∀ d : ℕ, 1 ≤ d → ∀ p : ℝ, 1 ≤ p → p < 4 * (d : ℝ) →
      let params := counterParameters d p
      MeasurableFamilyStatement d p params.1 params.2.1 params.2.2.1 params.2.2.2 ∧
      SmoothFamilyStatement d p params.1 params.2.1 params.2.2.1 params.2.2.2)
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
  have hpos := counterParameters_pos d hd p hp hpd
  have hf := hfamilies d hd p hp hpd
  exact ⟨(counterParameters d p).1, (counterParameters d p).2.1,
    (counterParameters d p).2.2.1, (counterParameters d p).2.2.2,
    hpos.1, hpos.2.1, hpos.2.2, hf.1, hf.2⟩

end HypoellipticAleksandrov.KineticAleksandrov
