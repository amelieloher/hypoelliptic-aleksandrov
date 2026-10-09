-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import Mathlib

/-!
# Kinetic Aleksandrov and Hölder estimates for measurable coefficients `A(t,x,v)`

A standalone, Mathlib-only statement of the kinetic Aleksandrov maximum principle and the interior
Hölder estimate for the backward kinetic operator `P_A u = ∂ₜu + v · ∇ₓu - A(t,x,v) : D²ᵥu`,
where the symmetric coefficient `A` is merely Borel measurable in `(t,x,v)` and satisfies
`λ I ≤ A ≤ Λ I` almost everywhere.

* `kinetic_aleksandrov_fullCoefficient`: for `p ≥ 1 + (128 d²/3)(Λ/λ)²` there is a constant `C`,
  depending only on `d, λ, Λ, p`, such that a `C^{1,1,2}` subsolution `P_A u ≤ f` (a.e.) on a
  backward kinetic cylinder of radius `R`, continuous up to the closure, satisfies at every point
  of the closed cylinder
  `u ≤ sup_{∂_kin} u₊ + C R^{2-(4d+2)/p} ‖f₊ 1_{u>0}‖_{L^p}`.
* `kinetic_holder_fullCoefficient`: a bounded `C^{1,1,2}` solution of `P_A u = 0` a.e. on an open
  set `Ω` is Hölder continuous on every compact `K` whose doubled backward cylinders of radius
  `2R₀` stay in `Ω`, with exponent `α` and constant `C` depending only on `d, λ, Λ`, in the kinetic
  quasi-distance and relative to the oscillation on the neighbourhood `⋃_{P ∈ K} Q_{2R₀}(P)`.
* `kinetic_holder_of_aleksandrov`: the abstract implication, Aleksandrov principle `⇒` Hölder:
  the same Hölder conclusion for bounded functions `u` such that `u` and `-u` are admissible
  supersolutions (the Aleksandrov-type estimate holds against every smooth barrier `ψ`, with the
  localised positive source `(P_A ψ)₊ 1_{u<ψ}`) with data `(p, C_A)`.

Space is `PDE.Vec d = Fin d → ℝ`. Kinetic points are triples `(t, x, v)` with the topology and
Lebesgue measure of the product `ℝ × ℝ^d × ℝ^d`; Euclidean balls, spheres and norms are the round
ones (defined explicitly below, not the supremum norm of `Fin d → ℝ`). The relative position in
free-transport coordinates is `x - x₀ - (t - t₀) v₀`. Sources: the adjoint-smoothing proof of the
kinetic Aleksandrov estimate for coefficients `A(t,x,v)` at https://weneedabp.github.io/; A. Loher,
C. Mooney and C. Mouhot, *From Döblin to Aleksandrov* (https://amelieloher.github.io/DF-visual-paper/),
Theorem 9.1.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal MatrixOrder

namespace FullCoefficientChallenge

/-! ## Ambient carriers and Euclidean geometry -/

/-- The native coordinate model of `ℝ^d`. -/
abbrev Vec (d : ℕ) := Fin d → ℝ

/-- Real `d × d` matrices. -/
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℝ

/-- The `i`th coordinate basis vector. -/
def basisVec {d : ℕ} (i : Fin d) : Vec d := Pi.single i (1 : ℝ)

/-- The Euclidean dot product. -/
def vecDot {d : ℕ} (x y : Vec d) : ℝ := ∑ i, x i * y i

/-- The square of the Euclidean norm. -/
def vecNormSq {d : ℕ} (x : Vec d) : ℝ := vecDot x x

/-- The Euclidean norm. -/
def vecEuclideanNorm {d : ℕ} (x : Vec d) : ℝ := Real.sqrt (vecNormSq x)

/-- Euclidean squared distance. -/
def euclideanSqDist {d : ℕ} (x y : Vec d) : ℝ := vecNormSq (x - y)

/-- The round Euclidean open ball of radius `R` (defined by the squared radius `R ^ 2`). -/
def euclideanBall {d : ℕ} (x₀ : Vec d) (R : ℝ) : Set (Vec d) :=
  {x | euclideanSqDist x x₀ < R ^ 2}

/-- The round Euclidean sphere of radius `R` (defined by the squared radius `R ^ 2`). -/
def euclideanSphere {d : ℕ} (x₀ : Vec d) (R : ℝ) : Set (Vec d) :=
  {x | euclideanSqDist x x₀ = R ^ 2}

/-- The gradient of `f : ℝ^d → ℝ` through the Fréchet derivative (junk value `0` when `f` is not
differentiable at `x`). -/
def classicalGradient {d : ℕ} (f : Vec d → ℝ) (x : Vec d) : Vec d :=
  fun i => (fderiv ℝ f x) (basisVec i)

/-- The entrywise Frobenius contraction `∑ᵢⱼ Aᵢⱼ Hᵢⱼ` of two matrices. -/
def matrixContraction {d : ℕ} (A H : Mat d) : ℝ := ∑ i, ∑ j, A i j * H i j

/-! ## Kinetic points -/

/-- A point `(t, x, v)` of kinetic spacetime in dimension `d`. -/
structure KineticPoint (d : ℕ) where
  /-- Time coordinate. -/
  time : ℝ
  /-- Position coordinate. -/
  position : Vec d
  /-- Velocity coordinate. -/
  velocity : Vec d

/-- The coordinate equivalence with `ℝ × (ℝ^d × ℝ^d)`. -/
def KineticPoint.equivProd (d : ℕ) : KineticPoint d ≃ ℝ × (Vec d × Vec d) where
  toFun z := (z.time, (z.position, z.velocity))
  invFun z := ⟨z.1, z.2.1, z.2.2⟩
  left_inv z := by cases z; rfl
  right_inv z := by rcases z with ⟨t, x, v⟩; rfl

/-- The standard product metric transported to kinetic points. It supplies only the topology
(closures, continuity); the Euclidean geometry is the explicit one above. -/
instance (d : ℕ) : MetricSpace (KineticPoint d) :=
  MetricSpace.induced (KineticPoint.equivProd d) (KineticPoint.equivProd d).injective inferInstance

/-- Borel measurable sets of kinetic points. -/
instance KineticPoint.instMeasurableSpace (d : ℕ) : MeasurableSpace (KineticPoint d) :=
  borel (KineticPoint d)

/-- The measurable structure on kinetic points is the Borel structure. -/
instance KineticPoint.instBorelSpace (d : ℕ) : BorelSpace (KineticPoint d) := ⟨rfl⟩

/-- Product Lebesgue measure transported to kinetic points in the order `(t, x, v)`. -/
instance KineticPoint.instMeasureSpace (d : ℕ) : MeasureSpace (KineticPoint d) where
  volume := Measure.map (KineticPoint.equivProd d).symm
    (volume : Measure (ℝ × (Vec d × Vec d)))

/-! ## Classical `C^{1,1,2}` regularity and the backward operator -/

/-- The time derivative with position and velocity held fixed. -/
def kineticTimeDerivative {d : ℕ} (u : KineticPoint d → ℝ) (z : KineticPoint d) : ℝ :=
  deriv (fun r => u ⟨r, z.position, z.velocity⟩) z.time

/-- The position gradient with time and velocity held fixed. -/
def kineticPositionGradient {d : ℕ} (u : KineticPoint d → ℝ) (z : KineticPoint d) : Vec d :=
  classicalGradient (fun x => u ⟨z.time, x, z.velocity⟩) z.position

/-- The velocity gradient with time and position held fixed. -/
def kineticVelocityGradient {d : ℕ} (u : KineticPoint d → ℝ) (z : KineticPoint d) : Vec d :=
  classicalGradient (fun v => u ⟨z.time, z.position, v⟩) z.velocity

/-- The velocity Hessian, indexed as `D_i (D_j u)`. -/
def kineticVelocityHessian {d : ℕ} (u : KineticPoint d → ℝ) (z : KineticPoint d) : Mat d :=
  fun i j =>
    (fderiv ℝ (fun v : Vec d => classicalGradient (fun w : Vec d => u ⟨z.time, z.position, w⟩) v)
      z.velocity (basisVec i)) j

/-- The anisotropic kinetic `C^{1,1,2}` regularity on a set `D`: one time, one position and two
velocity derivatives on the separate slices, all continuous on `D`. -/
def IsKineticC112On {d : ℕ} (u : KineticPoint d → ℝ) (D : Set (KineticPoint d)) : Prop :=
  ContinuousOn u D ∧
    (∀ z ∈ D, DifferentiableAt ℝ (fun r => u ⟨r, z.position, z.velocity⟩) z.time) ∧
    (∀ z ∈ D, ContDiffAt ℝ 1 (fun x => u ⟨z.time, x, z.velocity⟩) z.position) ∧
    (∀ z ∈ D, ContDiffAt ℝ 2 (fun v => u ⟨z.time, z.position, v⟩) z.velocity) ∧
    ContinuousOn (kineticTimeDerivative u) D ∧
    ContinuousOn (kineticPositionGradient u) D ∧
    ContinuousOn (kineticVelocityGradient u) D ∧
    ContinuousOn (kineticVelocityHessian u) D

/-- A full matrix coefficient `A(t, x, v)`. -/
abbrev FullKineticCoefficient (d : ℕ) := ℝ → Vec d → Vec d → Mat d

/-- Evaluation of a full kinetic coefficient at a kinetic point. -/
def fullKineticCoefficientAt {d : ℕ} (A : FullKineticCoefficient d) (z : KineticPoint d) :
    Mat d :=
  A z.time z.position z.velocity

/-- The backward kinetic operator `P_A u = ∂ₜu + v · ∇ₓu - A : D²ᵥu` with full coefficient
`A t x v`. -/
def backwardOperator {d : ℕ} (A : FullKineticCoefficient d) (u : KineticPoint d → ℝ)
    (z : KineticPoint d) : ℝ :=
  kineticTimeDerivative u z + vecDot z.velocity (kineticPositionGradient u z) -
    matrixContraction (fullKineticCoefficientAt A z) (kineticVelocityHessian u z)

/-! ## Backward cylinders, kinetic boundary, quasi-distance -/

/-- Relative velocity of `P` with respect to the centre `P₀`. -/
def relativeVelocity {d : ℕ} (P₀ P : KineticPoint d) : Vec d := P.velocity - P₀.velocity

/-- Relative position in free-transport coordinates based at `P₀`:
`x - x₀ - (t - t₀) v₀`. -/
def relativePosition {d : ℕ} (P₀ P : KineticPoint d) : Vec d :=
  P.position - P₀.position - (P.time - P₀.time) • P₀.velocity

/-- The open backward kinetic cylinder with time, velocity and position radii `R²`, `R`, `R³`. -/
def backwardCylinder {d : ℕ} (P₀ : KineticPoint d) (R : ℝ) : Set (KineticPoint d) :=
  {P | P₀.time - R ^ 2 < P.time ∧ P.time < P₀.time ∧
    P.velocity ∈ euclideanBall P₀.velocity R ∧
    relativePosition P₀ P ∈ euclideanBall (0 : Vec d) (R ^ 3)}

/-- The kinetic boundary: the closure of the cylinder intersected with the bottom face, the
velocity sphere, or the inflow part of the relative-position sphere. -/
def kineticBoundary {d : ℕ} (P₀ : KineticPoint d) (R : ℝ) : Set (KineticPoint d) :=
  closure (backwardCylinder P₀ R) ∩
    ({P | P.time = P₀.time - R ^ 2} ∪
      {P | P.velocity ∈ euclideanSphere P₀.velocity R} ∪
      {P | relativePosition P₀ P ∈ euclideanSphere (0 : Vec d) (R ^ 3) ∧
        vecDot (relativeVelocity P₀ P) (relativePosition P₀ P) ≤ 0})

/-- The kinetic quasi-distance. -/
def quasiDistance {d : ℕ} (P P' : KineticPoint d) : ℝ :=
  Real.sqrt |P.time - P'.time| +
    vecEuclideanNorm (P.velocity - P'.velocity) +
    Real.rpow
      (max
        (vecEuclideanNorm (P'.position - P.position - (P'.time - P.time) • P.velocity))
        (vecEuclideanNorm (P.position - P'.position - (P.time - P'.time) • P'.velocity)))
      (1 / 3 : ℝ)

/-- The neighbourhood `⋃_{P ∈ K} Q_{2R₀}(P)` of `K` appearing in the Hölder estimate. -/
def holderNeighbourhood {d : ℕ} (R₀ : ℝ) (K : Set (KineticPoint d)) : Set (KineticPoint d) :=
  ⋃ P ∈ K, backwardCylinder P (2 * R₀)

/-- Oscillation `sup u - inf u` over a set `E` (real `sSup`/`sInf`, so junk `0` values when `u`
is unbounded on `E` or `E` is empty). -/
def oscillationOn {d : ℕ} (u : KineticPoint d → ℝ) (E : Set (KineticPoint d)) : ℝ :=
  sSup (u '' E) - sInf (u '' E)

/-! ## Admissible solutions (for the abstract Hölder theorem) -/

/-- Smooth on an open neighbourhood of `E`, in `(t, x, v)` coordinates. -/
def IsSmoothNear {d : ℕ} (psi : KineticPoint d → ℝ) (E : Set (KineticPoint d)) : Prop :=
  ∃ U : Set (KineticPoint d), IsOpen U ∧ E ⊆ U ∧
    ContDiffOn ℝ (⊤ : ℕ∞) (psi ∘ (KineticPoint.equivProd d).symm)
      ((KineticPoint.equivProd d) '' U)

/-- The localised positive source `(P_A ψ)₊ 1_{u < ψ}`. -/
def localizedSource {d : ℕ} (A : FullKineticCoefficient d) (psi u : KineticPoint d → ℝ) :
    KineticPoint d → ℝ :=
  {P | u P < psi P}.indicator (fun P => max (backwardOperator A psi P) 0)

/-- `u` is an admissible supersolution on `O` with Aleksandrov data `(p, C_A)`: it is continuous on
`O`, and on every backward cylinder with closure in `O`, against every barrier `ψ` smooth near
the closed cylinder, `sup (ψ - u) ≤ sup_{∂_kin} (ψ - u)₊ + C_A R^{2-(4d+2)/p} ‖(P_A ψ)₊ 1_{u<ψ}‖_{L^p}`. -/
def IsAdmissibleSupersolution {d : ℕ} (A : FullKineticCoefficient d) (O : Set (KineticPoint d))
    (p C_A : ℝ) (u : KineticPoint d → ℝ) : Prop :=
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

/-- `u` is an admissible solution: both `u` and `-u` are admissible supersolutions. -/
def IsAdmissibleSolution {d : ℕ} (A : FullKineticCoefficient d) (O : Set (KineticPoint d))
    (p C_A : ℝ) (u : KineticPoint d → ℝ) : Prop :=
  IsAdmissibleSupersolution A O p C_A u ∧ IsAdmissibleSupersolution A O p C_A (fun P => -u P)

/-! ## Main theorems -/

/-- The kinetic Aleksandrov estimate for full coefficients, localised to the positivity set of
`u`, with the uniform constant quantified before the data. -/
theorem kinetic_aleksandrov_fullCoefficient
    (d : ℕ) (hd : 1 ≤ d) (lam Lam p : ℝ)
    (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hp : 1 + 128 * (d : ℝ) ^ 2 * (Lam / lam) ^ 2 / 3 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (P₀ : KineticPoint d) (R : ℝ), 0 < R →
      ∀ (A : FullKineticCoefficient d),
        Measurable (fullKineticCoefficientAt A) →
        (∀ P : KineticPoint d, (fullKineticCoefficientAt A P).IsSymm) →
        (∀ᵐ P ∂(volume : Measure (KineticPoint d)),
          lam • (1 : Mat d) ≤ fullKineticCoefficientAt A P) →
        (∀ᵐ P ∂(volume : Measure (KineticPoint d)),
          fullKineticCoefficientAt A P ≤ Lam • (1 : Mat d)) →
      ∀ (f u : KineticPoint d → ℝ),
        Measurable (fun P : backwardCylinder P₀ R => f P) →
        ContinuousOn u (closure (backwardCylinder P₀ R)) →
        IsKineticC112On u (backwardCylinder P₀ R) →
        (∀ᵐ P ∂(volume.restrict (backwardCylinder P₀ R)),
          backwardOperator A u P ≤ f P) →
        MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
          (volume.restrict (backwardCylinder P₀ R)) →
        ∀ P ∈ closure (backwardCylinder P₀ R),
          u P ≤ sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) +
            C * R ^ (2 - (4 * (d : ℝ) + 2) / p) *
              (eLpNorm ({P | 0 < u P}.indicator (fun P => max (f P) 0)) (ENNReal.ofReal p)
                (volume.restrict (backwardCylinder P₀ R))).toReal := by
  sorry

/-- The interior Hölder estimate for full coefficients. -/
theorem kinetic_holder_fullCoefficient
    (d : ℕ) (hd : 1 ≤ d) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ alpha C : ℝ, 0 < alpha ∧ alpha ≤ 1 ∧
      ∀ A : FullKineticCoefficient d,
        Measurable (fullKineticCoefficientAt A) →
        (∀ P : KineticPoint d, (fullKineticCoefficientAt A P).IsSymm) →
        (∀ᵐ P ∂(volume : Measure (KineticPoint d)),
          lam • (1 : Mat d) ≤ fullKineticCoefficientAt A P) →
        (∀ᵐ P ∂(volume : Measure (KineticPoint d)),
          fullKineticCoefficientAt A P ≤ Lam • (1 : Mat d)) →
      ∀ (Omega : Set (KineticPoint d)), IsOpen Omega →
      ∀ (u : KineticPoint d → ℝ),
        (∃ M : ℝ, ∀ P ∈ Omega, |u P| ≤ M) →
        IsKineticC112On u Omega →
        (∀ᵐ P ∂(volume.restrict Omega), backwardOperator A u P = 0) →
      ∀ (K : Set (KineticPoint d)), K ⊆ Omega → IsCompact K →
      ∀ (R₀ : ℝ), 0 < R₀ →
        (∀ P ∈ K, closure (backwardCylinder P (2 * R₀)) ⊆ Omega) →
      ∀ P ∈ K, ∀ P' ∈ K,
        |u P - u P'| ≤ C * oscillationOn u (holderNeighbourhood R₀ K) *
          (quasiDistance P P' / R₀) ^ alpha := by
  sorry

/-- Source Theorem `t:holder`: the Aleksandrov principle implies Hölder continuity, uniformly over
full coefficients and all solution and domain data. -/
theorem kinetic_holder_of_aleksandrov
    (d : ℕ) (hd : 1 ≤ d) (lam Lam p C_A : ℝ)
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (hp : 1 ≤ p) :
    ∃ alpha C : ℝ, 0 < alpha ∧ alpha ≤ 1 ∧
      ∀ A : FullKineticCoefficient d,
        Measurable (fullKineticCoefficientAt A) →
        (∀ P : KineticPoint d, (fullKineticCoefficientAt A P).IsSymm) →
        (∀ᵐ P ∂(volume : Measure (KineticPoint d)),
          lam • (1 : Mat d) ≤ fullKineticCoefficientAt A P) →
        (∀ᵐ P ∂(volume : Measure (KineticPoint d)),
          fullKineticCoefficientAt A P ≤ Lam • (1 : Mat d)) →
      ∀ (Omega : Set (KineticPoint d)), IsOpen Omega →
      ∀ (u : KineticPoint d → ℝ),
        (∃ M : ℝ, ∀ P ∈ Omega, |u P| ≤ M) →
        IsAdmissibleSolution A Omega p C_A u →
      ∀ (K : Set (KineticPoint d)), K ⊆ Omega → IsCompact K →
      ∀ (R₀ : ℝ), 0 < R₀ →
        (∀ P ∈ K, closure (backwardCylinder P (2 * R₀)) ⊆ Omega) →
      ∀ P ∈ K, ∀ P' ∈ K,
        |u P - u P'| ≤ C * oscillationOn u (holderNeighbourhood R₀ K) *
          (quasiDistance P P' / R₀) ^ alpha := by
  sorry

end FullCoefficientChallenge
