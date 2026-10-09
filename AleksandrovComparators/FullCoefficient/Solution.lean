-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import Mathlib
public import HypoellipticAleksandrov.Statements.KineticAleksandrovFullCoefficient
public import HypoellipticAleksandrov.Statements.HolderFullCoefficient
public import HypoellipticAleksandrov.Statements.KineticHolder

/-!
# Solution: kinetic Aleksandrov and Hölder estimates for coefficients `A(t,x,v)`, proved

This file repeats `Challenge.lean` verbatim and proves each theorem from the corresponding
statement of the library `HypoellipticAleksandrov`. The library's `KineticPoint` is a distinct
structure; the `Bridge` section transports along the coordinate homeomorphism `Bridge.ofLib`,
which preserves volume.

The Challenge statement follows.

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

/-! ## Bridge to the library carrier

The library's `HypoellipticAleksandrov.KineticPoint d` is a distinct structure with the same three
fields. `Bridge.ofLib` and `Bridge.toLib` are the inverse coordinate maps; `Bridge.homeo` shows that
they are homeomorphisms, and `Bridge.measurePreserving_ofLib` that they preserve volume. Every
Challenge notion is the library notion transported along `ofLib`. -/

namespace Bridge

/-- The library's kinetic point. -/
abbrev LP (d : ℕ) := HypoellipticAleksandrov.KineticPoint d

/-- Library points to Challenge points. -/
def ofLib {d : ℕ} (z : LP d) : KineticPoint d := ⟨z.time, z.position, z.velocity⟩

/-- Challenge points to library points. -/
def toLib {d : ℕ} (z : KineticPoint d) : LP d := ⟨z.time, z.position, z.velocity⟩

theorem ofLib_toLib {d : ℕ} (z : KineticPoint d) : ofLib (toLib z) = z := rfl

theorem toLib_ofLib {d : ℕ} (z : LP d) : toLib (ofLib z) = z := rfl

theorem ofLib_surjective (d : ℕ) : Function.Surjective (ofLib : LP d → KineticPoint d) :=
  fun z => ⟨toLib z, rfl⟩

/-- The Challenge coordinate map is an isometry onto the product. -/
def isoProd (d : ℕ) : KineticPoint d ≃ᵢ ℝ × (Vec d × Vec d) where
  toEquiv := KineticPoint.equivProd d
  isometry_toFun :=
    MetricSpace.isometry_induced (KineticPoint.equivProd d) (KineticPoint.equivProd d).injective

/-- `ofLib` as a homeomorphism. -/
def homeo (d : ℕ) : LP d ≃ₜ KineticPoint d :=
  (HypoellipticAleksandrov.KineticPoint.homeomorphProd d).trans (isoProd d).toHomeomorph.symm

theorem homeo_coe (d : ℕ) : ⇑(homeo d) = (ofLib : LP d → KineticPoint d) := rfl

theorem continuous_ofLib (d : ℕ) : Continuous (ofLib : LP d → KineticPoint d) :=
  (homeo d).continuous

theorem measurable_ofLib (d : ℕ) : Measurable (ofLib : LP d → KineticPoint d) :=
  (continuous_ofLib d).measurable

theorem measurableEmbedding_ofLib (d : ℕ) :
    MeasurableEmbedding (ofLib : LP d → KineticPoint d) :=
  (homeo d).toMeasurableEquiv.measurableEmbedding

/-- The library's kinetic volume corresponds to the Challenge's under `ofLib`. -/
theorem measurePreserving_ofLib (d : ℕ) :
    MeasurePreserving (ofLib : LP d → KineticPoint d) volume volume := by
  refine ⟨measurable_ofLib d, ?_⟩
  change Measure.map ofLib
    (Measure.map (HypoellipticAleksandrov.KineticPoint.equivProd d).symm
      (volume : Measure (ℝ × (Vec d × Vec d)))) =
    Measure.map (KineticPoint.equivProd d).symm (volume : Measure (ℝ × (Vec d × Vec d)))
  rw [Measure.map_map (measurable_ofLib d)
    (HypoellipticAleksandrov.KineticPoint.measurable_equivProd_symm d)]
  rfl

theorem measurePreserving_restrict_ofLib (d : ℕ) (S : Set (KineticPoint d)) :
    MeasurePreserving (ofLib : LP d → KineticPoint d)
      (volume.restrict (ofLib ⁻¹' S)) (volume.restrict S) :=
  (measurePreserving_ofLib d).restrict_preimage_emb (measurableEmbedding_ofLib d) S

theorem image_comp_ofLib {d : ℕ} (g : KineticPoint d → ℝ) (S : Set (KineticPoint d)) :
    (fun P : LP d => g (ofLib P)) '' (ofLib ⁻¹' S) = g '' S := by
  change (g ∘ ofLib) '' (ofLib ⁻¹' S) = g '' S
  rw [Set.image_comp, (ofLib_surjective d).image_preimage]

theorem eLpNorm_comp_ofLib {d : ℕ} (g : KineticPoint d → ℝ) (p : ℝ≥0∞) (S : Set (KineticPoint d)) :
    eLpNorm (fun P : LP d => g (ofLib P)) p (volume.restrict (ofLib ⁻¹' S)) =
      eLpNorm g p (volume.restrict S) := by
  rw [← (measurePreserving_restrict_ofLib d S).map_eq,
    (measurableEmbedding_ofLib d).eLpNorm_map_measure]
  rfl

/-! ### Geometry -/

theorem cylinder_preimage {d : ℕ} (P₀ : KineticPoint d) (R : ℝ) :
    ofLib ⁻¹' backwardCylinder P₀ R =
      HypoellipticAleksandrov.KineticAleksandrov.backwardCylinder (toLib P₀) R := rfl

theorem closure_cylinder_preimage {d : ℕ} (P₀ : KineticPoint d) (R : ℝ) :
    ofLib ⁻¹' closure (backwardCylinder P₀ R) =
      closure (HypoellipticAleksandrov.KineticAleksandrov.backwardCylinder (toLib P₀) R) := by
  rw [← cylinder_preimage, ← homeo_coe, (homeo d).preimage_closure]

theorem boundary_preimage {d : ℕ} (P₀ : KineticPoint d) (R : ℝ) :
    ofLib ⁻¹' kineticBoundary P₀ R =
      HypoellipticAleksandrov.KineticAleksandrov.kineticBoundary (toLib P₀) R := by
  unfold kineticBoundary HypoellipticAleksandrov.KineticAleksandrov.kineticBoundary
  rw [preimage_inter, closure_cylinder_preimage]
  rfl

theorem holderNeighbourhood_preimage {d : ℕ} (R₀ : ℝ) (K : Set (KineticPoint d)) :
    ofLib ⁻¹' holderNeighbourhood R₀ K =
      HypoellipticAleksandrov.KineticAleksandrov.Holder.holderNeighbourhood R₀
        (ofLib ⁻¹' K : Set (LP d)) := by
  ext z
  simp only [holderNeighbourhood,
    HypoellipticAleksandrov.KineticAleksandrov.Holder.holderNeighbourhood, mem_preimage,
    mem_iUnion, exists_prop]
  constructor
  · rintro ⟨Q, hQ, hz⟩
    exact ⟨toLib Q, hQ, hz⟩
  · rintro ⟨P, hP, hz⟩
    exact ⟨ofLib P, hP, hz⟩

theorem oscillationOn_comp {d : ℕ} (u : KineticPoint d → ℝ) (S : Set (KineticPoint d)) :
    HypoellipticAleksandrov.KineticAleksandrov.Holder.oscillationOn
        (fun P : LP d => u (ofLib P)) (ofLib ⁻¹' S) = oscillationOn u S := by
  unfold oscillationOn HypoellipticAleksandrov.KineticAleksandrov.Holder.oscillationOn
  rw [image_comp_ofLib u S]

/-! ### Regularity and the operator -/

theorem isKineticC112On_comp {d : ℕ} {u : KineticPoint d → ℝ} {D : Set (KineticPoint d)}
    (h : IsKineticC112On u D) :
    HypoellipticAleksandrov.Parabolic.IsKineticC112On (fun P : LP d => u (ofLib P))
      (ofLib ⁻¹' D) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  have hm : Set.MapsTo (ofLib : LP d → KineticPoint d) (ofLib ⁻¹' D) D := mapsTo_preimage _ _
  have hc := (continuous_ofLib d).continuousOn (s := (ofLib ⁻¹' D : Set (LP d)))
  exact ⟨h1.comp hc hm, fun z hz => h2 _ hz, fun z hz => h3 _ hz, fun z hz => h4 _ hz,
    h5.comp hc hm, h6.comp hc hm, h7.comp hc hm, h8.comp hc hm⟩

theorem backwardOperator_comp {d : ℕ} (A : FullKineticCoefficient d) (u : KineticPoint d → ℝ)
    (z : LP d) :
    HypoellipticAleksandrov.KineticAleksandrov.backwardOperator A (fun P : LP d => u (ofLib P))
      z = backwardOperator A u (ofLib z) := rfl

theorem coefficient_measurable {d : ℕ} {A : FullKineticCoefficient d}
    (h : Measurable (fullKineticCoefficientAt A)) :
    Measurable (HypoellipticAleksandrov.KineticAleksandrov.fullKineticCoefficientAt A) :=
  h.comp (measurable_ofLib d)

theorem ae_transfer {d : ℕ} {p : KineticPoint d → Prop} (h : ∀ᵐ P ∂(volume : Measure (KineticPoint d)), p P) :
    ∀ᵐ P ∂(volume : Measure (LP d)), p (ofLib P) :=
  (measurePreserving_ofLib d).quasiMeasurePreserving.ae h

theorem ae_restrict_transfer {d : ℕ} {S : Set (KineticPoint d)} {p : KineticPoint d → Prop}
    (h : ∀ᵐ P ∂(volume.restrict S), p P) :
    ∀ᵐ P ∂(volume.restrict (ofLib ⁻¹' S) : Measure (LP d)), p (ofLib P) :=
  (measurePreserving_restrict_ofLib d S).quasiMeasurePreserving.ae h

/-! ### Admissible supersolutions -/

theorem isSmoothNear_of_lib {d : ℕ} (psi' : LP d → ℝ) (E : Set (KineticPoint d))
    (h : HypoellipticAleksandrov.KineticAleksandrov.Holder.IsSmoothNear psi' (ofLib ⁻¹' E)) :
    IsSmoothNear (fun Q => psi' (toLib Q)) E := by
  obtain ⟨U', hU', hE, hsm⟩ := h
  refine ⟨ofLib '' U', (homeo d).isOpenMap U' hU', ?_, ?_⟩
  · intro Q hQ
    exact ⟨toLib Q, hE hQ, rfl⟩
  · have h2 : (KineticPoint.equivProd d) '' (ofLib '' U') =
        (HypoellipticAleksandrov.KineticPoint.equivProd d) '' U' := by
      ext y
      constructor
      · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
        exact ⟨z, hz, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨ofLib z, ⟨z, hz, rfl⟩, rfl⟩
    rw [h2]
    exact hsm

theorem admissibleSupersolution_comp {d : ℕ} {A : FullKineticCoefficient d}
    {Ω : Set (KineticPoint d)} {p C_A : ℝ} {w : KineticPoint d → ℝ}
    (h : IsAdmissibleSupersolution A Ω p C_A w) :
    HypoellipticAleksandrov.KineticAleksandrov.Holder.IsAdmissibleSupersolution A
      (ofLib ⁻¹' Ω) p C_A (fun P : LP d => w (ofLib P)) := by
  refine ⟨h.1.comp (continuous_ofLib d).continuousOn (mapsTo_preimage _ _), ?_⟩
  intro P₀' R hR hcl psi' hsm
  have hcl' : closure (backwardCylinder (ofLib P₀') R) ⊆ Ω := by
    intro Q hQ
    have h1 : toLib Q ∈ ofLib ⁻¹' closure (backwardCylinder (ofLib P₀') R) := hQ
    rw [closure_cylinder_preimage, toLib_ofLib] at h1
    exact hcl h1
  have hsm' : IsSmoothNear (fun Q => psi' (toLib Q)) (closure (backwardCylinder (ofLib P₀') R)) := by
    refine isSmoothNear_of_lib psi' _ ?_
    rw [closure_cylinder_preimage]
    exact hsm
  have key := h.2 (ofLib P₀') R hR hcl' (fun Q => psi' (toLib Q)) hsm'
  have e1 : (fun P : LP d => psi' P - w (ofLib P)) '' closure
      (HypoellipticAleksandrov.KineticAleksandrov.backwardCylinder P₀' R) =
      (fun Q => psi' (toLib Q) - w Q) '' closure (backwardCylinder (ofLib P₀') R) := by
    rw [← image_comp_ofLib (fun Q => psi' (toLib Q) - w Q), closure_cylinder_preimage]
    rfl
  have e2 : (fun P : LP d => max (psi' P - w (ofLib P)) 0) ''
      HypoellipticAleksandrov.KineticAleksandrov.kineticBoundary P₀' R =
      (fun Q => max (psi' (toLib Q) - w Q) 0) '' kineticBoundary (ofLib P₀') R := by
    rw [← image_comp_ofLib (fun Q => max (psi' (toLib Q) - w Q) 0), boundary_preimage]
    rfl
  have e3 : HypoellipticAleksandrov.KineticAleksandrov.Holder.localizedSource A psi'
      (fun P : LP d => w (ofLib P)) =
      fun P : LP d => localizedSource A (fun Q => psi' (toLib Q)) w (ofLib P) := by
    funext P
    rfl
  have e4 : eLpNorm (fun P : LP d => localizedSource A (fun Q => psi' (toLib Q)) w (ofLib P))
      (ENNReal.ofReal p) (volume.restrict
        (HypoellipticAleksandrov.KineticAleksandrov.backwardCylinder P₀' R)) =
      eLpNorm (localizedSource A (fun Q => psi' (toLib Q)) w) (ENNReal.ofReal p)
        (volume.restrict (backwardCylinder (ofLib P₀') R)) :=
    eLpNorm_comp_ofLib (localizedSource A (fun Q => psi' (toLib Q)) w)
      (ENNReal.ofReal p) (backwardCylinder (ofLib P₀') R)
  rw [e3, e4]
  exact (congrArg sSup e1).trans_le (key.trans_eq (by rw [e2]))

end Bridge

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
  obtain ⟨C, hC, hmain⟩ :=
    HypoellipticAleksandrov.KineticAleksandrov.kinetic_aleksandrov_fullCoefficient
      d hd lam Lam p hlam hLam hp
  refine ⟨C, hC, ?_⟩
  intro P₀ R hR A hmeas hsymm hlo hhi f u hf hucont hu hineq hmem P hP
  have hf' : Measurable (fun P : HypoellipticAleksandrov.KineticAleksandrov.backwardCylinder
      (Bridge.toLib P₀) R => f (Bridge.ofLib P)) :=
    hf.comp (Measurable.subtype_mk (h := fun P => P.2)
      ((Bridge.measurable_ofLib d).comp measurable_subtype_coe))
  have hcl : closure (HypoellipticAleksandrov.KineticAleksandrov.backwardCylinder
      (Bridge.toLib P₀) R) = Bridge.ofLib ⁻¹' closure (backwardCylinder P₀ R) :=
    (Bridge.closure_cylinder_preimage P₀ R).symm
  have hucont' : ContinuousOn (fun P : Bridge.LP d => u (Bridge.ofLib P))
      (closure (HypoellipticAleksandrov.KineticAleksandrov.backwardCylinder
        (Bridge.toLib P₀) R)) := by
    rw [hcl]
    exact hucont.comp (Bridge.continuous_ofLib d).continuousOn (mapsTo_preimage _ _)
  have key := hmain (Bridge.toLib P₀) R hR A (Bridge.coefficient_measurable hmeas)
    (fun P => hsymm (Bridge.ofLib P))
    (Bridge.ae_transfer hlo) (Bridge.ae_transfer hhi)
    (fun P => f (Bridge.ofLib P)) (fun P => u (Bridge.ofLib P)) hf' hucont'
    (Bridge.isKineticC112On_comp hu)
    (Bridge.ae_restrict_transfer hineq)
    (hmem.comp_measurePreserving (Bridge.measurePreserving_restrict_ofLib d (backwardCylinder P₀ R)))
    (Bridge.toLib P) (by rw [hcl]; exact hP)
  have e1 : (fun P : Bridge.LP d => max (u (Bridge.ofLib P)) 0) ''
      HypoellipticAleksandrov.KineticAleksandrov.kineticBoundary (Bridge.toLib P₀) R =
      (fun Q => max (u Q) 0) '' kineticBoundary P₀ R := by
    rw [← Bridge.image_comp_ofLib (fun Q => max (u Q) 0), Bridge.boundary_preimage]
  have e2 : eLpNorm ({P : Bridge.LP d | 0 < u (Bridge.ofLib P)}.indicator
        (fun P => max (f (Bridge.ofLib P)) 0)) (ENNReal.ofReal p)
      (volume.restrict (HypoellipticAleksandrov.KineticAleksandrov.backwardCylinder
        (Bridge.toLib P₀) R)) =
      eLpNorm ({P | 0 < u P}.indicator (fun P => max (f P) 0)) (ENNReal.ofReal p)
        (volume.restrict (backwardCylinder P₀ R)) := by
    have e3 : {P : Bridge.LP d | 0 < u (Bridge.ofLib P)}.indicator
        (fun P => max (f (Bridge.ofLib P)) 0) =
        fun P : Bridge.LP d =>
          ({P | 0 < u P}.indicator (fun P => max (f P) 0)) (Bridge.ofLib P) := by
      funext P
      by_cases h : 0 < u (Bridge.ofLib P) <;> simp [Set.indicator, h]
    rw [e3]
    exact Bridge.eLpNorm_comp_ofLib ({P | 0 < u P}.indicator (fun P => max (f P) 0))
      (ENNReal.ofReal p) (backwardCylinder P₀ R)
  rw [e1, e2] at key
  exact key

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
  obtain ⟨alpha, C, ha, ha1, hmain⟩ :=
    HypoellipticAleksandrov.KineticAleksandrov.kinetic_holder_fullCoefficient d hd lam Lam hlam hLam
  refine ⟨alpha, C, ha, ha1, ?_⟩
  intro A hmeas hsymm hlo hhi Omega hOmega u hbdd hu hOp K hKΩ hK R₀ hR₀ hcl P hP P' hP'
  have hopen : IsOpen (Bridge.ofLib ⁻¹' Omega : Set (Bridge.LP d)) :=
    hOmega.preimage (Bridge.continuous_ofLib d)
  have hKc : IsCompact (Bridge.ofLib ⁻¹' K : Set (Bridge.LP d)) := by
    rw [← Bridge.homeo_coe]
    exact (Bridge.homeo d).isCompact_preimage.mpr hK
  have hKs : (Bridge.ofLib ⁻¹' K : Set (Bridge.LP d)) ⊆ Bridge.ofLib ⁻¹' Omega :=
    preimage_mono hKΩ
  have hcl' : ∀ P ∈ (Bridge.ofLib ⁻¹' K : Set (Bridge.LP d)),
      closure (HypoellipticAleksandrov.KineticAleksandrov.backwardCylinder P (2 * R₀)) ⊆
        Bridge.ofLib ⁻¹' Omega := by
    intro Q hQ
    have := Bridge.closure_cylinder_preimage (Bridge.ofLib Q) (2 * R₀)
    rw [Bridge.toLib_ofLib] at this
    rw [← this]
    exact preimage_mono (hcl _ hQ)
  have hu' := Bridge.isKineticC112On_comp hu
  have hOp' := Bridge.ae_restrict_transfer hOp
  have key := hmain A (Bridge.coefficient_measurable hmeas)
    (fun P => hsymm (Bridge.ofLib P))
    (Bridge.ae_transfer hlo) (Bridge.ae_transfer hhi) (Bridge.ofLib ⁻¹' Omega) hopen
    (fun P : Bridge.LP d => u (Bridge.ofLib P))
    (by obtain ⟨M, hM⟩ := hbdd; exact ⟨M, fun P hP => hM _ hP⟩) hu' hOp'
    _ hKs hKc R₀ hR₀ hcl' (Bridge.toLib P) hP (Bridge.toLib P') hP'
  rw [← Bridge.holderNeighbourhood_preimage, Bridge.oscillationOn_comp] at key
  exact key

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
  obtain ⟨alpha, C, ha, ha1, hmain⟩ :=
    HypoellipticAleksandrov.KineticAleksandrov.kinetic_holder_of_aleksandrov d hd lam Lam p C_A hlam hLam hp
  refine ⟨alpha, C, ha, ha1, ?_⟩
  intro A hmeas hsymm hlo hhi Omega hOmega u hbdd hadm K hKΩ hK R₀ hR₀ hcl P hP P' hP'
  have hopen : IsOpen (Bridge.ofLib ⁻¹' Omega : Set (Bridge.LP d)) :=
    hOmega.preimage (Bridge.continuous_ofLib d)
  have hKc : IsCompact (Bridge.ofLib ⁻¹' K : Set (Bridge.LP d)) := by
    rw [← Bridge.homeo_coe]
    exact (Bridge.homeo d).isCompact_preimage.mpr hK
  have hKs : (Bridge.ofLib ⁻¹' K : Set (Bridge.LP d)) ⊆ Bridge.ofLib ⁻¹' Omega :=
    preimage_mono hKΩ
  have hcl' : ∀ P ∈ (Bridge.ofLib ⁻¹' K : Set (Bridge.LP d)),
      closure (HypoellipticAleksandrov.KineticAleksandrov.backwardCylinder P (2 * R₀)) ⊆
        Bridge.ofLib ⁻¹' Omega := by
    intro Q hQ
    have := Bridge.closure_cylinder_preimage (Bridge.ofLib Q) (2 * R₀)
    rw [Bridge.toLib_ofLib] at this
    rw [← this]
    exact preimage_mono (hcl _ hQ)
  have hadm' : HypoellipticAleksandrov.KineticAleksandrov.Holder.IsAdmissibleSolution A
      (Bridge.ofLib ⁻¹' Omega) p C_A (fun P : Bridge.LP d => u (Bridge.ofLib P)) :=
    ⟨Bridge.admissibleSupersolution_comp hadm.1, Bridge.admissibleSupersolution_comp hadm.2⟩
  have key := hmain A (Bridge.coefficient_measurable hmeas)
    (fun P => hsymm (Bridge.ofLib P))
    (Bridge.ae_transfer hlo) (Bridge.ae_transfer hhi) (Bridge.ofLib ⁻¹' Omega) hopen
    (fun P : Bridge.LP d => u (Bridge.ofLib P))
    (by obtain ⟨M, hM⟩ := hbdd; exact ⟨M, fun P hP => hM _ hP⟩) hadm'
    _ hKs hKc R₀ hR₀ hcl' (Bridge.toLib P) hP (Bridge.toLib P') hP'
  rw [← Bridge.holderNeighbourhood_preimage, Bridge.oscillationOn_comp] at key
  exact key

end FullCoefficientChallenge
