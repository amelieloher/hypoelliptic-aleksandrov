module

public import HypoellipticAleksandrov.KineticAleksandrov.Geometry
public import HypoellipticAleksandrov.KineticAleksandrov.Operator
public import HypoellipticAleksandrov.Geometry.KineticPointMeasure
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Proposed Section 6 setting

Predicates for companion paper, Section 9.
The operator, affine map, quasi-distance and forward stack are reused from
KineticAleksandrov.Operator and Geometry with their usual meanings.
Smoothness is expressed in the existing product coordinates, not through a
new differential structure on KineticPoint.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Set MeasureTheory
open scoped ENNReal

/-- Smooth on an open neighbourhood of the specified set, in (t,x,v) coordinates. -/
def IsSmoothNear {d : ℕ} (psi : KineticPoint d → ℝ) (E : Set (KineticPoint d)) : Prop :=
  ∃ U : Set (KineticPoint d), IsOpen U ∧ E ⊆ U ∧
    ContDiffOn ℝ (⊤ : ℕ∞) (psi ∘ (KineticPoint.equivProd d).symm)
      ((KineticPoint.equivProd d) '' U)

/-- The local neighbourhood Ω_{R₀,𝒞} in the source Hölder estimate. -/
def holderNeighbourhood {d : ℕ} (R₀ : ℝ) (K : Set (KineticPoint d)) :
    Set (KineticPoint d) :=
  ⋃ P ∈ K, backwardCylinder P (2 * R₀)

/-- Literal oscillation: supremum of values minus infimum of values. -/
def oscillationOn {d : ℕ} (u : KineticPoint d → ℝ) (E : Set (KineticPoint d)) : ℝ :=
  sSup (u '' E) - sInf (u '' E)

/-- The localised positive source in e:amp, including its superlevel indicator. -/
def localizedSource {d : ℕ} (A : FullKineticCoefficient d)
    (psi u : KineticPoint d → ℝ) : KineticPoint d → ℝ :=
  {P | u P < psi P}.indicator (fun P => max (backwardOperator A psi P) 0)

/-- Source-defined admissible supersolution with Aleksandrov data (p,C_A).
The coefficient is an explicit parameter because the predicate contains P_A.
Under the standing bounded elliptic Borel coefficient assumptions, the local
source norm is finite for every smooth-near-closure barrier; `toReal` is then
its ordinary real Lp norm, as in the Aleksandrov estimate. -/
def IsAdmissibleSupersolution {d : ℕ} (A : FullKineticCoefficient d)
    (O : Set (KineticPoint d)) (p C_A : ℝ) (u : KineticPoint d → ℝ) : Prop :=
  ContinuousOn u O ∧
    ∀ (P₀ : KineticPoint d) (R : ℝ), 0 < R →
      closure (backwardCylinder P₀ R) ⊆ O →
      ∀ psi : KineticPoint d → ℝ,
        IsSmoothNear psi (closure (backwardCylinder P₀ R)) →
        sSup ((fun P => psi P - u P) '' closure (backwardCylinder P₀ R)) ≤
          sSup ((fun P => max (psi P - u P) 0) '' kineticBoundary P₀ R) +
            C_A * R ^ (2 - (4 * (d : ℝ) + 2) / p) *
              (eLpNorm (localizedSource A psi u) (ENNReal.ofReal p)
                (volume.restrict (backwardCylinder P₀ R))).toReal

/-- A source-defined admissible solution: both u and -u are admissible supersolutions. -/
def IsAdmissibleSolution {d : ℕ} (A : FullKineticCoefficient d)
    (O : Set (KineticPoint d)) (p C_A : ℝ) (u : KineticPoint d → ℝ) : Prop :=
  IsAdmissibleSupersolution A O p C_A u ∧
    IsAdmissibleSupersolution A O p C_A (fun P => -u P)

end HypoellipticAleksandrov.KineticAleksandrov.Holder
