-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import Mathlib
public import HypoellipticAleksandrov.Statements.KineticAleksandrovTimeVelocity
public import HypoellipticAleksandrov.Statements.KineticAleksandrovTimeVelocityLocalised
public import HypoellipticAleksandrov.Statements.HolderTimeVelocity
public import HypoellipticAleksandrov.Statements.KineticAleksandrovAutonomous
public import HypoellipticAleksandrov.Statements.KineticAleksandrovAutonomousLocalised
public import HypoellipticAleksandrov.Statements.HolderAutonomous
public import HypoellipticAleksandrov.Statements.KineticAleksandrovCounterexample
public import HypoellipticAleksandrov.Statements.BellmanExponentWellDefined
public import HypoellipticAleksandrov.Statements.ParabolicAleksandrov
public import HypoellipticAleksandrov.Statements.ParabolicHarnack

/-!
# Kinetic Aleksandrov estimates for kinetic Fokker–Planck type operators

A standalone, Mathlib-only statement of the main results of the Döblin–Fourier companion paper
on the kinetic Aleksandrov–Bakelman–Pucci estimate. A kinetic point is `(t, x, v)` with
`x, v ∈ ℝᵈ = Fin d → ℝ`; the backward kinetic operator is `∂ₜ + v·∇ₓ − A : D²ᵥ`, acting on the
anisotropic class `C^{1,1,2}` (one time, one position, two velocity derivatives).

* `kinetic_aleksandrov_timeVelocity` (Theorem A): for coefficients `A(t, v)` that are Borel,
  symmetric and a.e. uniformly elliptic with bounds `lam ≤ A ≤ Lam`, and `p > 2d + 1`,
  a subsolution `u` in the backward cylinder `Q_R(P₀)` satisfies
  `sup u ≤ sup_{∂ₖ} u⁺ + C R^{2 - (4d+2)/p} ‖f⁺‖_{Lᵖ}`, with `C` independent of `P₀, R, A, f, u`.
* `kinetic_aleksandrov_timeVelocity_localised`: the same with the Lᵖ norm of `f⁺` restricted
  to the positivity set `{u > 0}`.
* `kinetic_holder_timeVelocity` (Hölder corollary c:holder-A): bounded solutions of
  `∂ₜu + v·∇ₓu − A:D²ᵥu = 0` are Hölder continuous in the kinetic quasi-distance.
* `kinetic_aleksandrov_autonomous` (Theorem a), `kinetic_aleksandrov_autonomous_localised`,
  `kinetic_holder_autonomous` (c:holder-a): the one-dimensional autonomous analogues for
  `a(x, v)` with `d = 1`, valid above the threshold `p_* = 1 + β_*(Lam/lam)`, where `β_*` is
  the Bellman exponent.
* `kinetic_aleksandrov_autonomous_counterexample`: for `1 ≤ p < 4d` the estimate fails for
  autonomous coefficients, in two forms (measurable coefficients; smooth coefficients).
* `parabolic_aleksandrov` (Krylov) and `parabolic_harnack_unit_cylinder` (Krylov–Safonov): the
  classical parabolic estimates for continuous coefficients on `ℝ × ℝᴺ`.
* `bellmanAdjointExponent` is defined explicitly as the supremum of the admissible degrees of
  the stationary adjoint equation on the punctured plane; `existsUnique_bellmanAdjointExponent`
  and `bellmanAdjointExponent_characterization` certify that it is the unique real least
  upper bound.

The quasi-distance is `√|t − t'| + |v − v'| + max(|x' − x − (t'−t)v|, |x − x' − (t−t')v'|)^{1/3}`
with Euclidean norms. The topology on kinetic points is the product topology (used only for
closures); the measure is product Lebesgue measure in the order `(t, x, v)`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal MatrixOrder

namespace KineticAleksandrovChallenge

/-! ## Euclidean ambient geometry -/

/-- The native coordinate model of `ℝᵈ`. -/
abbrev Vec (d : ℕ) := Fin d → ℝ

/-- Real `d × d` matrices acting on `Vec d`. -/
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℝ

/-- The Euclidean dot product. -/
def vecDot {d : ℕ} (x y : Vec d) : ℝ := ∑ i, x i * y i

/-- The squared Euclidean norm. -/
def vecNormSq {d : ℕ} (x : Vec d) : ℝ := vecDot x x

/-- The Euclidean norm (the inherited norm on `Fin d → ℝ` is the sup norm, so it is not used). -/
def vecEuclideanNorm {d : ℕ} (x : Vec d) : ℝ := Real.sqrt (vecNormSq x)

/-- The squared Euclidean distance. -/
def euclideanSqDist {d : ℕ} (x y : Vec d) : ℝ := vecNormSq (x - y)

/-- The round open Euclidean ball. -/
def euclideanBall {d : ℕ} (x₀ : Vec d) (R : ℝ) : Set (Vec d) :=
  {x | euclideanSqDist x x₀ < R ^ 2}

/-- The round Euclidean sphere. -/
def euclideanSphere {d : ℕ} (x₀ : Vec d) (R : ℝ) : Set (Vec d) :=
  {x | euclideanSqDist x x₀ = R ^ 2}

/-- The `i`th coordinate basis vector. -/
def basisVec {d : ℕ} (i : Fin d) : Vec d := Pi.single i (1 : ℝ)

/-- The classical gradient `(∂ᵢ f)ᵢ` through the Fréchet derivative. -/
def classicalGradient {d : ℕ} (f : Vec d → ℝ) (x : Vec d) : Vec d :=
  fun i => (fderiv ℝ f x) (basisVec i)

/-- The entrywise Frobenius contraction `A : H = Σᵢⱼ Aᵢⱼ Hᵢⱼ`. -/
def matrixContraction {d : ℕ} (A H : Mat d) : ℝ := ∑ i, ∑ j, A i j * H i j

/-! ## Kinetic points -/

/-- A point of kinetic spacetime. -/
structure KineticPoint (d : ℕ) where
  /-- Time coordinate. -/
  time : ℝ
  /-- Position coordinate. -/
  position : Vec d
  /-- Velocity coordinate. -/
  velocity : Vec d

/-- The coordinate equivalence with `ℝ × (ℝᵈ × ℝᵈ)`. -/
def KineticPoint.equivProd (d : ℕ) : KineticPoint d ≃ ℝ × (Vec d × Vec d) where
  toFun z := (z.time, (z.position, z.velocity))
  invFun z := ⟨z.1, z.2.1, z.2.2⟩
  left_inv z := by cases z; rfl
  right_inv z := by rcases z with ⟨t, x, v⟩; rfl

/-- The product metric transported along the coordinate equivalence; it supplies the product
topology only, never the kinetic or Euclidean geometry. -/
instance (d : ℕ) : MetricSpace (KineticPoint d) :=
  MetricSpace.induced (KineticPoint.equivProd d) (KineticPoint.equivProd d).injective
    inferInstance

/-- Borel sets for the product topology. -/
instance KineticPoint.instMeasurableSpace (d : ℕ) : MeasurableSpace (KineticPoint d) :=
  borel (KineticPoint d)

/-- Lebesgue measure: the product measure in the order `(t, x, v)`, transported. -/
instance KineticPoint.instMeasureSpace (d : ℕ) : MeasureSpace (KineticPoint d) where
  volume := Measure.map (KineticPoint.equivProd d).symm
    (volume : Measure (ℝ × (Vec d × Vec d)))

/-! ## Kinetic geometry -/

/-- Relative velocity of `P` with respect to the cylinder centre `P₀`. -/
def relativeVelocity {d : ℕ} (P₀ P : KineticPoint d) : Vec d := P.velocity - P₀.velocity

/-- Relative position in free-transport coordinates based at `P₀`. -/
def relativePosition {d : ℕ} (P₀ P : KineticPoint d) : Vec d :=
  P.position - P₀.position - (P.time - P₀.time) • P₀.velocity

/-- The open backward kinetic cylinder, with time, velocity and position radii `R²`, `R`, `R³`. -/
def backwardCylinder {d : ℕ} (P₀ : KineticPoint d) (R : ℝ) : Set (KineticPoint d) :=
  {P | P₀.time - R ^ 2 < P.time ∧ P.time < P₀.time ∧
    P.velocity ∈ euclideanBall P₀.velocity R ∧
    relativePosition P₀ P ∈ euclideanBall (0 : Vec d) (R ^ 3)}

/-- The kinetic boundary: the closure intersected with the bottom face, the velocity sphere,
or the inflow part of the relative-position sphere. -/
def kineticBoundary {d : ℕ} (P₀ : KineticPoint d) (R : ℝ) : Set (KineticPoint d) :=
  closure (backwardCylinder P₀ R) ∩
    ({P | P.time = P₀.time - R ^ 2} ∪
      {P | P.velocity ∈ euclideanSphere P₀.velocity R} ∪
      {P | relativePosition P₀ P ∈ euclideanSphere (0 : Vec d) (R ^ 3) ∧
        vecDot (relativeVelocity P₀ P) (relativePosition P₀ P) ≤ 0})

/-- The initial face and the full lateral boundary (including the whole position sphere). -/
def initialFullLateralBoundary {d : ℕ} (P₀ : KineticPoint d) (R : ℝ) : Set (KineticPoint d) :=
  closure (backwardCylinder P₀ R) ∩
    ({P | P.time = P₀.time - R ^ 2} ∪
      {P | P.velocity ∈ euclideanSphere P₀.velocity R} ∪
      {P | relativePosition P₀ P ∈ euclideanSphere (0 : Vec d) (R ^ 3)})

/-- The kinetic quasi-distance. -/
def quasiDistance {d : ℕ} (P P' : KineticPoint d) : ℝ :=
  Real.sqrt |P.time - P'.time| +
    vecEuclideanNorm (P.velocity - P'.velocity) +
    Real.rpow
      (max
        (vecEuclideanNorm (P'.position - P.position - (P'.time - P.time) • P.velocity))
        (vecEuclideanNorm (P.position - P'.position - (P.time - P'.time) • P'.velocity)))
      (1 / 3 : ℝ)

/-- The Hölder neighbourhood `Ω_{R₀,K} = ⋃_{P ∈ K} Q_{2R₀}(P)`. -/
def holderNeighbourhood {d : ℕ} (R₀ : ℝ) (K : Set (KineticPoint d)) : Set (KineticPoint d) :=
  ⋃ P ∈ K, backwardCylinder P (2 * R₀)

/-- Oscillation: the supremum of the values minus their infimum. -/
def oscillationOn {d : ℕ} (u : KineticPoint d → ℝ) (E : Set (KineticPoint d)) : ℝ :=
  sSup (u '' E) - sInf (u '' E)

/-! ## Derivatives, the class `C^{1,1,2}` and the operators -/

/-- The time derivative with position and velocity held fixed. -/
def kineticTimeDerivative {d : ℕ} (u : KineticPoint d → ℝ) (z : KineticPoint d) : ℝ :=
  deriv (fun r => u ⟨r, z.position, z.velocity⟩) z.time

/-- The position gradient with time and velocity held fixed. -/
def kineticPositionGradient {d : ℕ} (u : KineticPoint d → ℝ) (z : KineticPoint d) : Vec d :=
  classicalGradient (fun x => u ⟨z.time, x, z.velocity⟩) z.position

/-- The velocity gradient with time and position held fixed. -/
def kineticVelocityGradient {d : ℕ} (u : KineticPoint d → ℝ) (z : KineticPoint d) : Vec d :=
  classicalGradient (fun v => u ⟨z.time, z.position, v⟩) z.velocity

/-- The velocity Hessian, indexed as `Dᵢ(Dⱼ u)`. -/
def kineticVelocityHessian {d : ℕ} (u : KineticPoint d → ℝ) (z : KineticPoint d) : Mat d :=
  fun i j =>
    (fderiv ℝ (fun v : Vec d => classicalGradient (fun w : Vec d => u ⟨z.time, z.position, w⟩) v)
      z.velocity (basisVec i)) j

/-- The anisotropic kinetic `C^{1,1,2}` class on `D`: one time derivative, one position
derivative and two velocity derivatives, all continuous on `D`. -/
def IsKineticC112On {d : ℕ} (u : KineticPoint d → ℝ) (D : Set (KineticPoint d)) : Prop :=
  ContinuousOn u D ∧
    (∀ z ∈ D, DifferentiableAt ℝ (fun r => u ⟨r, z.position, z.velocity⟩) z.time) ∧
    (∀ z ∈ D, ContDiffAt ℝ 1 (fun x => u ⟨z.time, x, z.velocity⟩) z.position) ∧
    (∀ z ∈ D, ContDiffAt ℝ 2 (fun v => u ⟨z.time, z.position, v⟩) z.velocity) ∧
    ContinuousOn (kineticTimeDerivative u) D ∧
    ContinuousOn (kineticPositionGradient u) D ∧
    ContinuousOn (kineticVelocityGradient u) D ∧
    ContinuousOn (kineticVelocityHessian u) D

/-- A matrix coefficient depending on time and velocity, curried. -/
abbrev CoefficientField (d : ℕ) := ℝ → Vec d → Mat d

/-- A matrix coefficient depending on time, position and velocity, curried. -/
abbrev FullKineticCoefficient (d : ℕ) := ℝ → Vec d → Vec d → Mat d

/-- The product measurable structure on matrices. -/
local instance matrixMeasurableSpace (d : ℕ) : MeasurableSpace (Mat d) := by
  unfold Mat Matrix
  infer_instance

/-- Evaluates a coefficient field at a time–velocity pair. -/
def coefficientAt {d : ℕ} (A : CoefficientField d) (z : ℝ × Vec d) : Mat d := A z.1 z.2

/-- The coefficient field is Borel measurable on time–velocity space. -/
def IsBorelCoefficient {d : ℕ} (A : CoefficientField d) : Prop := Measurable (coefficientAt A)

/-- Every coefficient matrix is symmetric. -/
def IsSymmetricCoefficient {d : ℕ} (A : CoefficientField d) : Prop := ∀ t v, (A t v).IsSymm

/-- Almost-everywhere lower Loewner bound `lam • 1 ≤ A`, for Lebesgue measure on `ℝ × ℝᵈ`. -/
def HasLowerEllipticityAE {d : ℕ} (lam : ℝ) (A : CoefficientField d) : Prop :=
  ∀ᵐ z ∂(volume : Measure (ℝ × Vec d)), lam • (1 : Mat d) ≤ coefficientAt A z

/-- Almost-everywhere upper Loewner bound `A ≤ Lam • 1`, for Lebesgue measure on `ℝ × ℝᵈ`. -/
def HasUpperEllipticityAE {d : ℕ} (Lam : ℝ) (A : CoefficientField d) : Prop :=
  ∀ᵐ z ∂(volume : Measure (ℝ × Vec d)), coefficientAt A z ≤ Lam • (1 : Mat d)

/-- The backward kinetic operator `∂ₜ + v·∇ₓ − A : D²ᵥ` with a full coefficient. -/
def backwardOperator {d : ℕ} (A : FullKineticCoefficient d) (u : KineticPoint d → ℝ)
    (z : KineticPoint d) : ℝ :=
  kineticTimeDerivative u z + vecDot z.velocity (kineticPositionGradient u z) -
    matrixContraction (A z.time z.position z.velocity) (kineticVelocityHessian u z)

/-- The backward operator for a coefficient `A(t, v)` independent of position. -/
def backwardOperatorOfTimeVelocityCoefficient {d : ℕ} (A : CoefficientField d)
    (u : KineticPoint d → ℝ) (z : KineticPoint d) : ℝ :=
  backwardOperator (fun t _x v => A t v) u z

/-- The autonomous scalar backward operator `∂ₜ + v ∂ₓ − a(x, v) ∂ᵥᵥ` for `d = 1`. -/
def autonomousScalarOperator (a : ℝ → ℝ → ℝ) (u : KineticPoint 1 → ℝ) (z : KineticPoint 1) :
    ℝ :=
  kineticTimeDerivative u z + z.velocity 0 * kineticPositionGradient u z 0 -
    a (z.position 0) (z.velocity 0) * kineticVelocityHessian u z 0 0

/-! ## The Bellman exponent -/

/-- The real position–velocity plane with its origin removed. -/
abbrev BellmanPuncturedPlane := {q : ℝ × ℝ // q ≠ (0, 0)}

/-- The kinetic dilation `(x, v) ↦ (r³x, rv)` for `r > 0`. -/
def bellmanDilation (r : ℝ) (hr : 0 < r) :
    BellmanPuncturedPlane → BellmanPuncturedPlane := fun q =>
  ⟨(r ^ 3 * q.1.1, r * q.1.2), by
    intro h
    have hx : r ^ 3 * q.1.1 = 0 := congrArg Prod.fst h
    have hv : r * q.1.2 = 0 := congrArg Prod.snd h
    apply q.2
    apply Prod.ext
    · exact (mul_eq_zero.mp hx).resolve_left (pow_ne_zero 3 hr.ne')
    · exact (mul_eq_zero.mp hv).resolve_left hr.ne'⟩

/-- Density degree `β` of a measure: `μ(dilation_r E) = r^{4-β} μ(E)`. -/
def HasBellmanDensityDegree (β : ℝ) (μ : Measure BellmanPuncturedPlane) : Prop :=
  ∀ (r : ℝ) (hr : 0 < r) (E : Set BellmanPuncturedPlane), MeasurableSet E →
    μ (bellmanDilation r hr '' E) = ENNReal.ofReal (r ^ (4 - β)) * μ E

/-- The stationary adjoint equation `-∂ₓ(vμ) + ∂ᵥᵥη = 0` on the punctured plane, tested against
smooth compactly supported functions whose support avoids the origin. -/
def IsBellmanStationaryAdjointPair (μ η : Measure BellmanPuncturedPlane) : Prop :=
  ∀ (φ : ℝ × ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    tsupport φ ⊆ {q : ℝ × ℝ | q ≠ (0, 0)} →
      (∫ q, q.1.2 * fderiv ℝ φ q.1 (1, 0) ∂μ) +
        (∫ q, fderiv ℝ (fun z => fderiv ℝ φ z (0, 1)) q.1 (0, 1) ∂η) = 0

/-- The admissible degrees, after normalizing the ellipticity interval to `[1, ratio]`: radial
degrees of nonzero pairs of Radon measures `μ ≤ η ≤ ratio • μ` solving the adjoint equation. -/
def bellmanAdmissibleDegrees (ratio : ℝ) : Set ℝ :=
  {β | ∃ μ η : Measure BellmanPuncturedPlane,
    IsFiniteMeasureOnCompacts μ ∧ Measure.InnerRegular μ ∧
    IsFiniteMeasureOnCompacts η ∧ Measure.InnerRegular η ∧
    (μ ≠ 0 ∨ η ≠ 0) ∧ μ ≤ η ∧ η ≤ ENNReal.ofReal ratio • μ ∧
    IsBellmanStationaryAdjointPair μ η ∧
    HasBellmanDensityDegree β μ ∧ HasBellmanDensityDegree β η}

/-- The Bellman exponent `β_*(ratio)`: the supremum of the admissible degrees. -/
def bellmanAdjointExponent (ratio : ℝ) : ℝ := sSup (bellmanAdmissibleDegrees ratio)

/-! ## Bridge to the library: the Bellman exponent -/

namespace Bridge

/-- The admissible degrees of the Challenge are the library's. -/
theorem bellmanAdmissibleDegrees_eq (ratio : ℝ) :
    bellmanAdmissibleDegrees ratio =
      HypoellipticAleksandrov.KineticAleksandrov.bellmanAdmissibleDegrees ratio :=
  rfl

/-- The explicit supremum is the library's `Classical.choose`-based exponent. -/
theorem bellmanAdjointExponent_eq (ratio : ℝ) (hRatio : 1 ≤ ratio) :
    bellmanAdjointExponent ratio =
      HypoellipticAleksandrov.KineticAleksandrov.bellmanAdjointExponent ratio hRatio := by
  have h := (HypoellipticAleksandrov.KineticAleksandrov.bellmanAdjointExponent_characterization
    ratio hRatio).1
  exact h.csSup_eq h.nonempty

end Bridge

/-- Well-definedness: for `ratio ≥ 1` the admissible degrees have a unique real least upper
bound. Nonemptiness and boundedness are part of the conclusion. -/
theorem existsUnique_bellmanAdjointExponent (ratio : ℝ) (hRatio : 1 ≤ ratio) :
    ∃! β : ℝ, IsLUB (bellmanAdmissibleDegrees ratio) β := by
  rw [Bridge.bellmanAdmissibleDegrees_eq]
  exact HypoellipticAleksandrov.KineticAleksandrov.existsUnique_bellmanAdjointExponent ratio hRatio

/-- Characterization of the explicit exponent: it is the unique real least upper bound of the
admissible degrees. -/
theorem bellmanAdjointExponent_characterization (ratio : ℝ) (hRatio : 1 ≤ ratio) :
    IsLUB (bellmanAdmissibleDegrees ratio) (bellmanAdjointExponent ratio) ∧
      ∀ β : ℝ, IsLUB (bellmanAdmissibleDegrees ratio) β → β = bellmanAdjointExponent ratio := by
  obtain ⟨β, hβ, huniq⟩ := existsUnique_bellmanAdjointExponent ratio hRatio
  have h : bellmanAdjointExponent ratio = β := hβ.csSup_eq hβ.nonempty
  rw [h]
  exact ⟨hβ, fun γ hγ => huniq γ hγ⟩

/-! ## Bridge to the library: kinetic points, geometry and classes -/

namespace Bridge

/-- The library's kinetic points. -/
abbrev LKP (d : ℕ) := HypoellipticAleksandrov.KineticPoint d

/-- Challenge kinetic point to library kinetic point (fieldwise). -/
def toLib {d : ℕ} (z : KineticPoint d) : LKP d := ⟨z.time, z.position, z.velocity⟩

/-- Library kinetic point to Challenge kinetic point (fieldwise). -/
def ofLib {d : ℕ} (z : LKP d) : KineticPoint d := ⟨z.time, z.position, z.velocity⟩

theorem isometry_toLib (d : ℕ) : Isometry (toLib (d := d)) :=
  Isometry.of_dist_eq fun _ _ => rfl

theorem isometry_ofLib (d : ℕ) : Isometry (ofLib (d := d)) :=
  Isometry.of_dist_eq fun _ _ => rfl

theorem isometry_equivProd_symm (d : ℕ) : Isometry (KineticPoint.equivProd d).symm :=
  Isometry.of_dist_eq fun _ _ => rfl

/-- The coordinate homeomorphism between the Challenge's and the library's kinetic points. -/
def homeo (d : ℕ) : KineticPoint d ≃ₜ LKP d where
  toFun := toLib
  invFun := ofLib
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (isometry_toLib d).continuous
  continuous_invFun := (isometry_ofLib d).continuous

instance (d : ℕ) : BorelSpace (KineticPoint d) := ⟨rfl⟩

theorem continuous_ofLib (d : ℕ) : Continuous (ofLib (d := d)) := (homeo d).symm.continuous

theorem measurableEmbedding_ofLib (d : ℕ) : MeasurableEmbedding (ofLib (d := d)) :=
  (homeo d).symm.measurableEmbedding

theorem measurePreserving_ofLib (d : ℕ) : MeasurePreserving (ofLib (d := d)) volume volume := by
  have h1 : MeasurePreserving (KineticPoint.equivProd d).symm volume volume :=
    ⟨(isometry_equivProd_symm d).continuous.measurable, rfl⟩
  exact h1.comp (HypoellipticAleksandrov.KineticPoint.measurePreserving_equivProd d)

theorem surjective_ofLib (d : ℕ) : Function.Surjective (ofLib (d := d)) :=
  fun z => ⟨toLib z, rfl⟩

theorem image_comp_ofLib {d : ℕ} (g : KineticPoint d → ℝ) (S : Set (KineticPoint d)) :
    (fun P => g (ofLib P)) '' (ofLib ⁻¹' S) = g '' S := by
  have h : (fun P => g (ofLib P)) = g ∘ ofLib := rfl
  rw [h, Set.image_comp, (surjective_ofLib d).image_preimage]

theorem eLpNorm_comp_ofLib {d : ℕ} (g : KineticPoint d → ℝ) (p : ENNReal)
    (S : Set (KineticPoint d)) :
    eLpNorm (fun P => g (ofLib P)) p (volume.restrict (ofLib ⁻¹' S)) =
      eLpNorm g p (volume.restrict S) := by
  have hmp := (measurePreserving_ofLib d).restrict_preimage_emb (measurableEmbedding_ofLib d) S
  rw [← hmp.map_eq, (measurableEmbedding_ofLib d).eLpNorm_map_measure]
  rfl

theorem memLp_comp_ofLib {d : ℕ} {g : KineticPoint d → ℝ} {p : ENNReal}
    {S : Set (KineticPoint d)} (h : MemLp g p (volume.restrict S)) :
    MemLp (fun P => g (ofLib P)) p (volume.restrict (ofLib ⁻¹' S)) :=
  h.comp_measurePreserving
    ((measurePreserving_ofLib d).restrict_preimage_emb (measurableEmbedding_ofLib d) S)

theorem ae_comp_ofLib {d : ℕ} {F : KineticPoint d → Prop} {S : Set (KineticPoint d)}
    (h : ∀ᵐ P ∂(volume.restrict S), F P) :
    ∀ᵐ P ∂(volume.restrict (ofLib ⁻¹' S)), F (ofLib P) :=
  ((measurePreserving_ofLib d).restrict_preimage_emb
    (measurableEmbedding_ofLib d) S).quasiMeasurePreserving.ae h

theorem closure_preimage_ofLib {d : ℕ} (S : Set (KineticPoint d)) :
    closure (ofLib ⁻¹' S) = ofLib ⁻¹' closure S :=
  ((homeo d).symm.preimage_closure S).symm

theorem lib_backwardCylinder {d : ℕ} (P₀ : KineticPoint d) (R : ℝ) :
    HypoellipticAleksandrov.KineticAleksandrov.backwardCylinder (toLib P₀) R =
      ofLib ⁻¹' backwardCylinder P₀ R := rfl

theorem lib_kineticBoundary {d : ℕ} (P₀ : KineticPoint d) (R : ℝ) :
    HypoellipticAleksandrov.KineticAleksandrov.kineticBoundary (toLib P₀) R =
      ofLib ⁻¹' kineticBoundary P₀ R := by
  have hc : closure (HypoellipticAleksandrov.KineticAleksandrov.backwardCylinder (toLib P₀) R) =
      ofLib ⁻¹' closure (backwardCylinder P₀ R) := by
    rw [lib_backwardCylinder, closure_preimage_ofLib]
  ext P
  constructor
  · rintro ⟨h1, h2⟩
    rw [hc] at h1
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [hc]; exact h1, h2⟩

theorem lib_initialFullLateralBoundary {d : ℕ} (P₀ : KineticPoint d) (R : ℝ) :
    HypoellipticAleksandrov.KineticAleksandrov.initialFullLateralBoundary (toLib P₀) R =
      ofLib ⁻¹' initialFullLateralBoundary P₀ R := by
  have hc : closure (HypoellipticAleksandrov.KineticAleksandrov.backwardCylinder (toLib P₀) R) =
      ofLib ⁻¹' closure (backwardCylinder P₀ R) := by
    rw [lib_backwardCylinder, closure_preimage_ofLib]
  ext P
  constructor
  · rintro ⟨h1, h2⟩
    rw [hc] at h1
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [hc]; exact h1, h2⟩

theorem lib_holderNeighbourhood {d : ℕ} (R₀ : ℝ) (K : Set (KineticPoint d)) :
    HypoellipticAleksandrov.KineticAleksandrov.Holder.holderNeighbourhood R₀ (ofLib ⁻¹' K) =
      ofLib ⁻¹' holderNeighbourhood R₀ K := by
  ext P
  simp only [HypoellipticAleksandrov.KineticAleksandrov.Holder.holderNeighbourhood,
    holderNeighbourhood, Set.mem_iUnion, Set.mem_preimage]
  constructor
  · rintro ⟨Q, hQ, h⟩
    exact ⟨ofLib Q, hQ, h⟩
  · rintro ⟨Q, hQ, h⟩
    exact ⟨toLib Q, hQ, h⟩

theorem lib_oscillationOn {d : ℕ} (u : KineticPoint d → ℝ) (E : Set (KineticPoint d)) :
    HypoellipticAleksandrov.KineticAleksandrov.Holder.oscillationOn (fun P => u (ofLib P))
      (ofLib ⁻¹' E) = oscillationOn u E := by
  unfold HypoellipticAleksandrov.KineticAleksandrov.Holder.oscillationOn oscillationOn
  rw [image_comp_ofLib]

theorem ktd_comp {d : ℕ} (u : KineticPoint d → ℝ) :
    HypoellipticAleksandrov.Parabolic.kineticTimeDerivative (fun P => u (ofLib P)) =
      fun z => kineticTimeDerivative u (ofLib z) := by
  funext z
  unfold HypoellipticAleksandrov.Parabolic.kineticTimeDerivative kineticTimeDerivative
  rfl

theorem kpg_comp {d : ℕ} (u : KineticPoint d → ℝ) :
    HypoellipticAleksandrov.Parabolic.kineticPositionGradient (fun P => u (ofLib P)) =
      fun z => kineticPositionGradient u (ofLib z) := by
  funext z
  unfold HypoellipticAleksandrov.Parabolic.kineticPositionGradient kineticPositionGradient
  rfl

theorem kvg_comp {d : ℕ} (u : KineticPoint d → ℝ) :
    HypoellipticAleksandrov.Parabolic.kineticVelocityGradient (fun P => u (ofLib P)) =
      fun z => kineticVelocityGradient u (ofLib z) := by
  funext z
  unfold HypoellipticAleksandrov.Parabolic.kineticVelocityGradient kineticVelocityGradient
  rfl

theorem kvh_comp {d : ℕ} (u : KineticPoint d → ℝ) :
    HypoellipticAleksandrov.Parabolic.kineticVelocityHessian (fun P => u (ofLib P)) =
      fun z => kineticVelocityHessian u (ofLib z) := by
  funext z
  unfold HypoellipticAleksandrov.Parabolic.kineticVelocityHessian kineticVelocityHessian
  rfl

theorem isKineticC112On_comp {d : ℕ} {u : KineticPoint d → ℝ} {D : Set (KineticPoint d)}
    (h : IsKineticC112On u D) :
    HypoellipticAleksandrov.Parabolic.IsKineticC112On (fun P => u (ofLib P)) (ofLib ⁻¹' D) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  have hc : Continuous (ofLib (d := d)) := continuous_ofLib d
  have hm : Set.MapsTo ofLib (ofLib ⁻¹' D) D := fun _ hz => hz
  refine ⟨h1.comp hc.continuousOn hm, fun z hz => h2 (ofLib z) hz,
    fun z hz => h3 (ofLib z) hz, fun z hz => h4 (ofLib z) hz, ?_, ?_, ?_, ?_⟩
  · rw [ktd_comp]; exact h5.comp hc.continuousOn hm
  · rw [kpg_comp]; exact h6.comp hc.continuousOn hm
  · rw [kvg_comp]; exact h7.comp hc.continuousOn hm
  · rw [kvh_comp]; exact h8.comp hc.continuousOn hm

theorem measurable_comp_ofLib {d : ℕ} (P₀ : KineticPoint d) (R : ℝ) (f : KineticPoint d → ℝ)
    (hf : Measurable (fun P : backwardCylinder P₀ R => f P)) :
    Measurable (fun P : HypoellipticAleksandrov.KineticAleksandrov.backwardCylinder
      (toLib P₀) R => f (ofLib P)) := by
  have hm : Measurable (fun P : HypoellipticAleksandrov.KineticAleksandrov.backwardCylinder
      (toLib P₀) R => (⟨ofLib P.1, P.2⟩ : backwardCylinder P₀ R)) :=
    Measurable.subtype_mk ((continuous_ofLib d).measurable.comp measurable_subtype_coe)
  exact hf.comp hm

theorem continuousOn_closure_comp_ofLib {d : ℕ} (P₀ : KineticPoint d) (R : ℝ)
    (u : KineticPoint d → ℝ) (hu : ContinuousOn u (closure (backwardCylinder P₀ R))) :
    ContinuousOn (fun P => u (ofLib P))
      (closure (HypoellipticAleksandrov.KineticAleksandrov.backwardCylinder (toLib P₀) R)) := by
  have hc : closure (HypoellipticAleksandrov.KineticAleksandrov.backwardCylinder (toLib P₀) R) =
      ofLib ⁻¹' closure (backwardCylinder P₀ R) := by
    rw [lib_backwardCylinder, closure_preimage_ofLib]
  rw [hc]
  exact hu.comp (continuous_ofLib d).continuousOn (fun _ hz => hz)

theorem closure_lib_backwardCylinder {d : ℕ} (P₀ : KineticPoint d) (R : ℝ) :
    closure (HypoellipticAleksandrov.KineticAleksandrov.backwardCylinder (toLib P₀) R) =
      ofLib ⁻¹' closure (backwardCylinder P₀ R) := by
  rw [lib_backwardCylinder, closure_preimage_ofLib]

theorem sSup_boundary_eq {d : ℕ} (P₀ : KineticPoint d) (R : ℝ) (u : KineticPoint d → ℝ) :
    sSup ((fun P => max (u (ofLib P)) 0) ''
      HypoellipticAleksandrov.KineticAleksandrov.kineticBoundary (toLib P₀) R) =
      sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) := by
  rw [lib_kineticBoundary]
  exact congrArg sSup (image_comp_ofLib (fun P => max (u P) 0) _)

end Bridge

/-! ## Theorem A: time–velocity coefficients -/

/-- Theorem A, with the uniform constant quantified before the data. -/
theorem kinetic_aleksandrov_timeVelocity
    (d : ℕ) (hd : 1 ≤ d) (lam Lam p : ℝ)
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (hp : 2 * (d : ℝ) + 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (P₀ : KineticPoint d) (R : ℝ), 0 < R →
      ∀ (A : CoefficientField d),
        IsBorelCoefficient A → IsSymmetricCoefficient A →
        HasLowerEllipticityAE lam A → HasUpperEllipticityAE Lam A →
      ∀ (f u : KineticPoint d → ℝ),
        Measurable (fun P : backwardCylinder P₀ R => f P) →
        ContinuousOn u (closure (backwardCylinder P₀ R)) →
        IsKineticC112On u (backwardCylinder P₀ R) →
        (∀ᵐ P ∂(volume.restrict (backwardCylinder P₀ R)),
          backwardOperatorOfTimeVelocityCoefficient A u P ≤ f P) →
        MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
          (volume.restrict (backwardCylinder P₀ R)) →
        ∀ P ∈ closure (backwardCylinder P₀ R),
          u P ≤ sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) +
            C * R ^ (2 - (4 * (d : ℝ) + 2) / p) *
              (eLpNorm (fun P => max (f P) 0) (ENNReal.ofReal p)
                (volume.restrict (backwardCylinder P₀ R))).toReal := by
  obtain ⟨C, hC, H⟩ := HypoellipticAleksandrov.KineticAleksandrov.kinetic_aleksandrov_timeVelocity d hd lam Lam p hlam hLam hp
  refine ⟨C, hC, fun P₀ R hR A hAB hAS hAL hAU f u hf hcont hC112 hop hmem P hP => ?_⟩
  have key := H (Bridge.toLib P₀) R hR A hAB hAS hAL hAU (fun P => f (Bridge.ofLib P))
    (fun P => u (Bridge.ofLib P)) (Bridge.measurable_comp_ofLib P₀ R f hf)
    (Bridge.continuousOn_closure_comp_ofLib P₀ R u hcont)
    (Bridge.isKineticC112On_comp hC112) (Bridge.ae_comp_ofLib hop)
    (Bridge.memLp_comp_ofLib hmem) (Bridge.toLib P)
    (by rw [Bridge.closure_lib_backwardCylinder]; exact hP)
  have hnorm : eLpNorm (fun P' => max (f (Bridge.ofLib P')) 0) (ENNReal.ofReal p)
      (volume.restrict (HypoellipticAleksandrov.KineticAleksandrov.backwardCylinder (Bridge.toLib P₀) R)) =
      eLpNorm (fun P => max (f P) 0) (ENNReal.ofReal p) (volume.restrict (backwardCylinder P₀ R)) :=
    by
      rw [Bridge.lib_backwardCylinder]
      exact Bridge.eLpNorm_comp_ofLib (fun P => max (f P) 0) _ _
  rw [Bridge.sSup_boundary_eq, hnorm] at key
  exact key

/-- Localised Theorem A: the norm of `f⁺` is taken over the positivity set `{u > 0}`. -/
theorem kinetic_aleksandrov_timeVelocity_localised
    (d : ℕ) (hd : 1 ≤ d) (lam Lam p : ℝ)
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (hp : 2 * (d : ℝ) + 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (P₀ : KineticPoint d) (R : ℝ), 0 < R →
      ∀ (A : CoefficientField d),
        IsBorelCoefficient A → IsSymmetricCoefficient A →
        HasLowerEllipticityAE lam A → HasUpperEllipticityAE Lam A →
      ∀ (f u : KineticPoint d → ℝ),
        Measurable (fun P : backwardCylinder P₀ R => f P) →
        ContinuousOn u (closure (backwardCylinder P₀ R)) →
        IsKineticC112On u (backwardCylinder P₀ R) →
        (∀ᵐ P ∂(volume.restrict (backwardCylinder P₀ R)),
          backwardOperatorOfTimeVelocityCoefficient A u P ≤ f P) →
        MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
          (volume.restrict (backwardCylinder P₀ R)) →
        ∀ P ∈ closure (backwardCylinder P₀ R),
          u P ≤ sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) +
            C * R ^ (2 - (4 * (d : ℝ) + 2) / p) *
              (eLpNorm ({P | 0 < u P}.indicator (fun P => max (f P) 0)) (ENNReal.ofReal p)
                (volume.restrict (backwardCylinder P₀ R))).toReal := by
  obtain ⟨C, hC, H⟩ := HypoellipticAleksandrov.KineticAleksandrov.kinetic_aleksandrov_timeVelocity_localised d hd lam Lam p hlam hLam hp
  refine ⟨C, hC, fun P₀ R hR A hAB hAS hAL hAU f u hf hcont hC112 hop hmem P hP => ?_⟩
  have key := H (Bridge.toLib P₀) R hR A hAB hAS hAL hAU (fun P => f (Bridge.ofLib P))
    (fun P => u (Bridge.ofLib P)) (Bridge.measurable_comp_ofLib P₀ R f hf)
    (Bridge.continuousOn_closure_comp_ofLib P₀ R u hcont)
    (Bridge.isKineticC112On_comp hC112) (Bridge.ae_comp_ofLib hop)
    (Bridge.memLp_comp_ofLib hmem) (Bridge.toLib P)
    (by rw [Bridge.closure_lib_backwardCylinder]; exact hP)
  have hnorm : eLpNorm ({P' | 0 < u (Bridge.ofLib P')}.indicator (fun P' => max (f (Bridge.ofLib P')) 0)) (ENNReal.ofReal p)
      (volume.restrict (HypoellipticAleksandrov.KineticAleksandrov.backwardCylinder (Bridge.toLib P₀) R)) =
      eLpNorm ({P | 0 < u P}.indicator (fun P => max (f P) 0)) (ENNReal.ofReal p) (volume.restrict (backwardCylinder P₀ R)) :=
    by
      have e : ({P' | 0 < u (Bridge.ofLib P')}.indicator (fun P' => max (f (Bridge.ofLib P')) 0)) = fun P' => ({P | 0 < u P}.indicator (fun P => max (f P) 0)) (Bridge.ofLib P') := funext fun P' => rfl
      rw [e, Bridge.lib_backwardCylinder]
      exact Bridge.eLpNorm_comp_ofLib ({P | 0 < u P}.indicator (fun P => max (f P) 0)) _ _
  rw [Bridge.sSup_boundary_eq, hnorm] at key
  exact key

/-- Corollary c:holder-A: Hölder continuity of bounded solutions, time–velocity coefficients. -/
theorem kinetic_holder_timeVelocity
    (d : ℕ) (hd : 1 ≤ d) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ alpha C : ℝ, 0 < alpha ∧ alpha ≤ 1 ∧
      ∀ A : CoefficientField d,
        IsBorelCoefficient A → IsSymmetricCoefficient A →
        HasLowerEllipticityAE lam A → HasUpperEllipticityAE Lam A →
      ∀ (Omega : Set (KineticPoint d)), IsOpen Omega →
      ∀ (u : KineticPoint d → ℝ),
        (∃ M : ℝ, ∀ P ∈ Omega, |u P| ≤ M) →
        IsKineticC112On u Omega →
        (∀ᵐ P ∂(volume.restrict Omega),
          backwardOperatorOfTimeVelocityCoefficient A u P = 0) →
      ∀ (K : Set (KineticPoint d)), K ⊆ Omega → IsCompact K →
      ∀ (R₀ : ℝ), 0 < R₀ →
        (∀ P ∈ K, closure (backwardCylinder P (2 * R₀)) ⊆ Omega) →
      ∀ P ∈ K, ∀ P' ∈ K,
        |u P - u P'| ≤ C * oscillationOn u (holderNeighbourhood R₀ K) *
          (quasiDistance P P' / R₀) ^ alpha := by
  obtain ⟨alpha, C, hα, hα1, H⟩ := HypoellipticAleksandrov.KineticAleksandrov.kinetic_holder_timeVelocity d hd lam Lam hlam hLam
  refine ⟨alpha, C, hα, hα1, fun A hB hS hL hU Ω hΩ u hbd hu hop K hK hKc R₀ hR₀ hcl P hP P' hP' => ?_⟩
  obtain ⟨M, hM⟩ := hbd
  have key := H A hB hS hL hU (Bridge.ofLib ⁻¹' Ω)
    (hΩ.preimage (Bridge.continuous_ofLib _)) (fun P => u (Bridge.ofLib P))
    ⟨M, fun P hP => hM _ hP⟩ (Bridge.isKineticC112On_comp hu) (Bridge.ae_comp_ofLib hop)
    (Bridge.ofLib ⁻¹' K) (Set.preimage_mono hK)
    ((Bridge.homeo _).symm.isCompact_preimage.2 hKc) R₀ hR₀
    (fun Q hQ => by
      have h1 := hcl (Bridge.ofLib Q) hQ
      have h2 : closure (HypoellipticAleksandrov.KineticAleksandrov.backwardCylinder Q (2 * R₀)) =
          Bridge.ofLib ⁻¹' closure (backwardCylinder (Bridge.ofLib Q) (2 * R₀)) :=
        Bridge.closure_lib_backwardCylinder (Bridge.ofLib Q) (2 * R₀)
      rw [h2]
      exact Set.preimage_mono h1)
    (Bridge.toLib P) hP (Bridge.toLib P') hP'
  rw [Bridge.lib_holderNeighbourhood, Bridge.lib_oscillationOn] at key
  exact key

/-! ## Theorem a: the autonomous one-dimensional case -/

/-- Theorem a: the autonomous scalar Aleksandrov estimate above `p_* = 1 + β_*(Lam / lam)`. -/
theorem kinetic_aleksandrov_autonomous
    (lam Lam p : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hp : 1 + bellmanAdjointExponent (Lam / lam) < p) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (P₀ : KineticPoint 1) (R : ℝ), 0 < R →
      ∀ (a : ℝ → ℝ → ℝ),
        Measurable (Function.uncurry a) →
        (∀ x v : ℝ, lam ≤ a x v ∧ a x v ≤ Lam) →
      ∀ (f u : KineticPoint 1 → ℝ),
        Measurable (fun P : backwardCylinder P₀ R => f P) →
        ContinuousOn u (closure (backwardCylinder P₀ R)) →
        IsKineticC112On u (backwardCylinder P₀ R) →
        (∀ᵐ P ∂(volume.restrict (backwardCylinder P₀ R)),
          autonomousScalarOperator a u P ≤ f P) →
        MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
          (volume.restrict (backwardCylinder P₀ R)) →
        ∀ P ∈ closure (backwardCylinder P₀ R),
          u P ≤ sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) +
            C * R ^ (2 - 6 / p) *
              (eLpNorm (fun P => max (f P) 0) (ENNReal.ofReal p)
                (volume.restrict (backwardCylinder P₀ R))).toReal := by
  obtain ⟨C, hC, H⟩ := HypoellipticAleksandrov.KineticAleksandrov.kinetic_aleksandrov_autonomous lam Lam p hlam hLam
    (by
      rw [Bridge.bellmanAdjointExponent_eq (Lam / lam)
        ((le_div_iff₀ hlam).2 (by simpa only [one_mul] using hLam))] at hp
      exact hp)
  refine ⟨C, hC, fun P₀ R hR a ha hab f u hf hcont hC112 hop hmem P hP => ?_⟩
  have key := H (Bridge.toLib P₀) R hR a ha hab (fun P => f (Bridge.ofLib P))
    (fun P => u (Bridge.ofLib P)) (Bridge.measurable_comp_ofLib P₀ R f hf)
    (Bridge.continuousOn_closure_comp_ofLib P₀ R u hcont)
    (Bridge.isKineticC112On_comp hC112) (Bridge.ae_comp_ofLib hop)
    (Bridge.memLp_comp_ofLib hmem) (Bridge.toLib P)
    (by rw [Bridge.closure_lib_backwardCylinder]; exact hP)
  have hnorm : eLpNorm (fun P' => max (f (Bridge.ofLib P')) 0) (ENNReal.ofReal p)
      (volume.restrict (HypoellipticAleksandrov.KineticAleksandrov.backwardCylinder (Bridge.toLib P₀) R)) =
      eLpNorm (fun P => max (f P) 0) (ENNReal.ofReal p) (volume.restrict (backwardCylinder P₀ R)) :=
    by
      rw [Bridge.lib_backwardCylinder]
      exact Bridge.eLpNorm_comp_ofLib (fun P => max (f P) 0) _ _
  rw [Bridge.sSup_boundary_eq, hnorm] at key
  exact key

/-- Localised Theorem a: the norm of `f⁺` is taken over the positivity set `{u > 0}`. -/
theorem kinetic_aleksandrov_autonomous_localised
    (lam Lam p : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hp : 1 + bellmanAdjointExponent (Lam / lam) < p) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (P₀ : KineticPoint 1) (R : ℝ), 0 < R →
      ∀ (a : ℝ → ℝ → ℝ),
        Measurable (Function.uncurry a) →
        (∀ x v : ℝ, lam ≤ a x v ∧ a x v ≤ Lam) →
      ∀ (f u : KineticPoint 1 → ℝ),
        Measurable (fun P : backwardCylinder P₀ R => f P) →
        ContinuousOn u (closure (backwardCylinder P₀ R)) →
        IsKineticC112On u (backwardCylinder P₀ R) →
        (∀ᵐ P ∂(volume.restrict (backwardCylinder P₀ R)),
          autonomousScalarOperator a u P ≤ f P) →
        MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
          (volume.restrict (backwardCylinder P₀ R)) →
        ∀ P ∈ closure (backwardCylinder P₀ R),
          u P ≤ sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) +
            C * R ^ (2 - 6 / p) *
              (eLpNorm ({P | 0 < u P}.indicator (fun P => max (f P) 0)) (ENNReal.ofReal p)
                (volume.restrict (backwardCylinder P₀ R))).toReal := by
  obtain ⟨C, hC, H⟩ := HypoellipticAleksandrov.KineticAleksandrov.kinetic_aleksandrov_autonomous_localised lam Lam p hlam hLam
    (by
      rw [Bridge.bellmanAdjointExponent_eq (Lam / lam)
        ((le_div_iff₀ hlam).2 (by simpa only [one_mul] using hLam))] at hp
      exact hp)
  refine ⟨C, hC, fun P₀ R hR a ha hab f u hf hcont hC112 hop hmem P hP => ?_⟩
  have key := H (Bridge.toLib P₀) R hR a ha hab (fun P => f (Bridge.ofLib P))
    (fun P => u (Bridge.ofLib P)) (Bridge.measurable_comp_ofLib P₀ R f hf)
    (Bridge.continuousOn_closure_comp_ofLib P₀ R u hcont)
    (Bridge.isKineticC112On_comp hC112) (Bridge.ae_comp_ofLib hop)
    (Bridge.memLp_comp_ofLib hmem) (Bridge.toLib P)
    (by rw [Bridge.closure_lib_backwardCylinder]; exact hP)
  have hnorm : eLpNorm ({P' | 0 < u (Bridge.ofLib P')}.indicator (fun P' => max (f (Bridge.ofLib P')) 0)) (ENNReal.ofReal p)
      (volume.restrict (HypoellipticAleksandrov.KineticAleksandrov.backwardCylinder (Bridge.toLib P₀) R)) =
      eLpNorm ({P | 0 < u P}.indicator (fun P => max (f P) 0)) (ENNReal.ofReal p) (volume.restrict (backwardCylinder P₀ R)) :=
    by
      have e : ({P' | 0 < u (Bridge.ofLib P')}.indicator (fun P' => max (f (Bridge.ofLib P')) 0)) = fun P' => ({P | 0 < u P}.indicator (fun P => max (f P) 0)) (Bridge.ofLib P') := funext fun P' => rfl
      rw [e, Bridge.lib_backwardCylinder]
      exact Bridge.eLpNorm_comp_ofLib ({P | 0 < u P}.indicator (fun P => max (f P) 0)) _ _
  rw [Bridge.sSup_boundary_eq, hnorm] at key
  exact key

/-- Corollary c:holder-a: Hölder continuity of bounded solutions, autonomous coefficients. -/
theorem kinetic_holder_autonomous
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ alpha C : ℝ, 0 < alpha ∧ alpha ≤ 1 ∧
      ∀ a : ℝ → ℝ → ℝ,
        Measurable (Function.uncurry a) →
        (∀ x v : ℝ, lam ≤ a x v ∧ a x v ≤ Lam) →
      ∀ (Omega : Set (KineticPoint 1)), IsOpen Omega →
      ∀ (u : KineticPoint 1 → ℝ),
        (∃ M : ℝ, ∀ P ∈ Omega, |u P| ≤ M) →
        IsKineticC112On u Omega →
        (∀ᵐ P ∂(volume.restrict Omega), autonomousScalarOperator a u P = 0) →
      ∀ (K : Set (KineticPoint 1)), K ⊆ Omega → IsCompact K →
      ∀ (R₀ : ℝ), 0 < R₀ →
        (∀ P ∈ K, closure (backwardCylinder P (2 * R₀)) ⊆ Omega) →
      ∀ P ∈ K, ∀ P' ∈ K,
        |u P - u P'| ≤ C * oscillationOn u (holderNeighbourhood R₀ K) *
          (quasiDistance P P' / R₀) ^ alpha := by
  obtain ⟨alpha, C, hα, hα1, H⟩ := HypoellipticAleksandrov.KineticAleksandrov.kinetic_holder_autonomous lam Lam hlam hLam
  refine ⟨alpha, C, hα, hα1, fun a ha hab Ω hΩ u hbd hu hop K hK hKc R₀ hR₀ hcl P hP P' hP' => ?_⟩
  obtain ⟨M, hM⟩ := hbd
  have key := H a ha hab (Bridge.ofLib ⁻¹' Ω)
    (hΩ.preimage (Bridge.continuous_ofLib _)) (fun P => u (Bridge.ofLib P))
    ⟨M, fun P hP => hM _ hP⟩ (Bridge.isKineticC112On_comp hu) (Bridge.ae_comp_ofLib hop)
    (Bridge.ofLib ⁻¹' K) (Set.preimage_mono hK)
    ((Bridge.homeo _).symm.isCompact_preimage.2 hKc) R₀ hR₀
    (fun Q hQ => by
      have h1 := hcl (Bridge.ofLib Q) hQ
      have h2 : closure (HypoellipticAleksandrov.KineticAleksandrov.backwardCylinder Q (2 * R₀)) =
          Bridge.ofLib ⁻¹' closure (backwardCylinder (Bridge.ofLib Q) (2 * R₀)) :=
        Bridge.closure_lib_backwardCylinder (Bridge.ofLib Q) (2 * R₀)
      rw [h2]
      exact Set.preimage_mono h1)
    (Bridge.toLib P) hP (Bridge.toLib P') hP'
  rw [Bridge.lib_holderNeighbourhood, Bridge.lib_oscillationOn] at key
  exact key

/-! ## The autonomous counterexample below `4d` -/

/-- Autonomous counterexamples for `1 ≤ p < 4d`, with shared fixed bounds and cylinder. -/
theorem kinetic_aleksandrov_autonomous_counterexample
    (d : ℕ) (hd : 1 ≤ d) (p : ℝ) (hp : 1 ≤ p) (hpd : p < 4 * (d : ℝ)) :
    ∃ lam Lam : ℝ, ∃ P₀ : KineticPoint d, ∃ R : ℝ,
      0 < lam ∧ lam ≤ Lam ∧ 0 < R ∧
      ((∃ A : (Vec d × Vec d) → Mat d,
        ∃ U : ℕ → KineticPoint d → ℝ,
          (∀ i k, Measurable (fun z => A z i k)) ∧
          (∀ z, lam • (1 : Mat d) ≤ A z ∧ A z ≤ Lam • (1 : Mat d)) ∧
          (∀ j, ContDiff ℝ (⊤ : ℕ∞)
            (fun q : ℝ × (Vec d × Vec d) => U j ((KineticPoint.equivProd d).symm q))) ∧
          (∀ j P, 0 ≤ U j P) ∧
          (∀ j P, P ∈ initialFullLateralBoundary P₀ R → U j P = 0) ∧
          (∀ j, ∃ P ∈ backwardCylinder P₀ R, (1 / 4 : ℝ) ≤ U j P) ∧
          Tendsto (fun j => eLpNorm
            (fun P => max (backwardOperator (fun _t x v => A (x, v)) (U j) P) 0)
            (ENNReal.ofReal p) (volume.restrict (backwardCylinder P₀ R)))
            atTop (nhds 0)) ∧
       (∃ A : ℕ → (Vec d × Vec d) → Mat d,
        ∃ U : ℕ → KineticPoint d → ℝ,
          (∀ j i k, ContDiff ℝ (⊤ : ℕ∞) (fun z => A j z i k)) ∧
          (∀ j z, lam • (1 : Mat d) ≤ A j z ∧ A j z ≤ Lam • (1 : Mat d)) ∧
          (∀ j, ContDiff ℝ (⊤ : ℕ∞)
            (fun q : ℝ × (Vec d × Vec d) => U j ((KineticPoint.equivProd d).symm q))) ∧
          (∀ j P, 0 ≤ U j P) ∧
          (∀ j P, P ∈ initialFullLateralBoundary P₀ R → U j P = 0) ∧
          (∀ j, ∃ P ∈ backwardCylinder P₀ R, (1 / 4 : ℝ) ≤ U j P) ∧
          Tendsto (fun j => eLpNorm
            (fun P => max (backwardOperator (fun _t x v => A j (x, v)) (U j) P) 0)
            (ENNReal.ofReal p) (volume.restrict (backwardCylinder P₀ R)))
            atTop (nhds 0))) := by
  obtain ⟨lam, Lam, P₀, R, hlam, hLL, hR, ⟨A, U, hAm, hAb, hUs, hU0, hUb, hUp, hUt⟩,
    ⟨A', U', hAs, hAb', hUs', hU0', hUb', hUp', hUt'⟩⟩ :=
    HypoellipticAleksandrov.KineticAleksandrov.kinetic_aleksandrov_autonomous_counterexample d hd p hp hpd
  refine ⟨lam, Lam, Bridge.ofLib P₀, R, hlam, hLL, hR, ⟨A, fun j P => U j (Bridge.toLib P),
    hAm, hAb, fun j => hUs j, fun j P => hU0 j _, ?_, ?_, ?_⟩,
    ⟨A', fun j P => U' j (Bridge.toLib P), hAs, hAb', fun j => hUs' j,
      fun j P => hU0' j _, ?_, ?_, ?_⟩⟩
  · intro j P hP
    exact hUb j (Bridge.toLib P) (show Bridge.toLib P ∈ HypoellipticAleksandrov.KineticAleksandrov.initialFullLateralBoundary
        (Bridge.toLib (Bridge.ofLib P₀)) R by
        rw [Bridge.lib_initialFullLateralBoundary]
        exact hP)
  · intro j
    obtain ⟨Q, hQ, hQ'⟩ := hUp j
    exact ⟨Bridge.ofLib Q, hQ, hQ'⟩
  · refine hUt.congr fun j => ?_
    exact Bridge.eLpNorm_comp_ofLib
      (fun P => max (backwardOperator (fun _t x v => A (x, v))
        (fun P => U j (Bridge.toLib P)) P) 0) _
      (backwardCylinder (Bridge.ofLib P₀) R)
  · intro j P hP
    exact hUb' j (Bridge.toLib P) (show Bridge.toLib P ∈ HypoellipticAleksandrov.KineticAleksandrov.initialFullLateralBoundary
        (Bridge.toLib (Bridge.ofLib P₀)) R by
        rw [Bridge.lib_initialFullLateralBoundary]
        exact hP)
  · intro j
    obtain ⟨Q, hQ, hQ'⟩ := hUp' j
    exact ⟨Bridge.ofLib Q, hQ, hQ'⟩
  · refine hUt'.congr fun j => ?_
    exact Bridge.eLpNorm_comp_ofLib
      (fun P => max (backwardOperator (fun _t x v => A' j (x, v))
        (fun P => U' j (Bridge.toLib P)) P) 0) _
      (backwardCylinder (Bridge.ofLib P₀) R)

/-! ## Parabolic Krylov–Safonov theory (Aleksandrov estimate and Harnack inequality) -/

/-- Time–velocity space `ℝ × ℝᴺ` (time first). -/
abbrev TimeVelocity (N : ℕ) := ℝ × Vec N

/-- The round closed Euclidean ball. -/
def euclideanClosedBall {d : ℕ} (x₀ : Vec d) (R : ℝ) : Set (Vec d) :=
  {x | euclideanSqDist x x₀ ≤ R ^ 2}

/-- The time derivative of `u`, with the velocity coordinate fixed. -/
def scalarTimeDerivative {n : ℕ} (u : TimeVelocity n → ℝ) (z : TimeVelocity n) : ℝ :=
  deriv (fun r : ℝ => u (r, z.2)) z.1

/-- The spatial gradient of `u` at a fixed time. -/
def scalarSpatialGradient {n : ℕ} (u : TimeVelocity n → ℝ) (z : TimeVelocity n) : Vec n :=
  classicalGradient (fun y : Vec n => u (z.1, y)) z.2

/-- The spatial Hessian of `u`, indexed as `Dᵢ(Dⱼ u)`. -/
def scalarSpatialHessian {n : ℕ} (u : TimeVelocity n → ℝ) (z : TimeVelocity n) : Mat n :=
  fun i j =>
    (fderiv ℝ (fun y : Vec n => classicalGradient (fun w : Vec n => u (z.1, w)) y) z.2
      (basisVec i)) j

/-- The anisotropic scalar class `C^{1,2}` on `D`: one time and two spatial derivatives. -/
def IsScalarC12On {n : ℕ} (u : TimeVelocity n → ℝ) (D : Set (TimeVelocity n)) : Prop :=
  ContinuousOn u D ∧
    (∀ z ∈ D, DifferentiableAt ℝ (fun r : ℝ => u (r, z.2)) z.1) ∧
    (∀ z ∈ D, ContDiffAt ℝ 2 (fun y : Vec n => u (z.1, y)) z.2) ∧
    ContinuousOn (scalarTimeDerivative u) D ∧
    ContinuousOn (scalarSpatialGradient u) D ∧
    ContinuousOn (scalarSpatialHessian u) D

/-- The round unit cylinder `(t₀ − h, t₀) × B₁(v₀)`. -/
def krylovCylinder {N : ℕ} (t₀ h : ℝ) (v₀ : Vec N) : Set (TimeVelocity N) :=
  Set.Ioo (t₀ - h) t₀ ×ˢ euclideanBall v₀ 1

/-- The closed round unit cylinder `[t₀ − h, t₀] × B̄₁(v₀)`. -/
def krylovClosedCylinder {N : ℕ} (t₀ h : ℝ) (v₀ : Vec N) : Set (TimeVelocity N) :=
  Set.Icc (t₀ - h) t₀ ×ˢ euclideanClosedBall v₀ 1

/-- The bottom and lateral faces; the top face is excluded. -/
def krylovParabolicBoundary {N : ℕ} (t₀ h : ℝ) (v₀ : Vec N) : Set (TimeVelocity N) :=
  ({t₀ - h} : Set ℝ) ×ˢ euclideanClosedBall v₀ 1 ∪ Set.Icc (t₀ - h) t₀ ×ˢ euclideanSphere v₀ 1

/-- Interior `C^{1,2}` regularity with continuous boundary traces of the value, time derivative,
spatial gradient and spatial Hessian. -/
def IsScalarC12UpTo {N : ℕ} (u : TimeVelocity N → ℝ) (Q K : Set (TimeVelocity N)) : Prop :=
  IsScalarC12On u Q ∧ ContinuousOn u K ∧
    ∃ (dt : TimeVelocity N → ℝ) (dv : TimeVelocity N → Vec N) (dvv : TimeVelocity N → Mat N),
      ContinuousOn dt K ∧ ContinuousOn dv K ∧ ContinuousOn dvv K ∧
      Set.EqOn dt (scalarTimeDerivative u) Q ∧
      Set.EqOn dv (scalarSpatialGradient u) Q ∧
      Set.EqOn dvv (scalarSpatialHessian u) Q

/-- The Lebesgue exponent `N + 1` of the parabolic Aleksandrov estimate. -/
def parabolicExponent (N : ℕ) : ℝ≥0∞ := N + 1

/-- The real `L^{N+1}` norm of `f` on `s` (`ENNReal.toReal` of the extended norm). -/
def parabolicLpNormOn (N : ℕ) (f : TimeVelocity N → ℝ) (s : Set (TimeVelocity N)) : ℝ :=
  (eLpNorm f (parabolicExponent N) (volume.restrict s)).toReal

/-- The coefficient is continuous (as a matrix-valued map on time–velocity space) on `U`. -/
def IsContinuousCoefficientOn {d : ℕ} (A : CoefficientField d) (U : Set (TimeVelocity d)) :
    Prop :=
  ContinuousOn (coefficientAt A) U

/-- Lower Loewner ellipticity bound on `U`. -/
def HasLowerEllipticityOn {d : ℕ} (lam : ℝ) (A : CoefficientField d)
    (U : Set (TimeVelocity d)) : Prop :=
  ∀ z ∈ U, lam • (1 : Mat d) ≤ coefficientAt A z

/-- Upper Loewner ellipticity bound on `U`. -/
def HasUpperEllipticityOn {d : ℕ} (Lam : ℝ) (A : CoefficientField d)
    (U : Set (TimeVelocity d)) : Prop :=
  ∀ z ∈ U, coefficientAt A z ≤ Lam • (1 : Mat d)

/-- The function is nonnegative on `U`. -/
def IsNonnegativeOn {d : ℕ} (q : TimeVelocity d → ℝ) (U : Set (TimeVelocity d)) : Prop :=
  ∀ z ∈ U, 0 ≤ q z

/-- Krylov's parabolic Aleksandrov estimate, uniformly over location and height. -/
theorem parabolic_aleksandrov
    (N : ℕ) (hN : 1 ≤ N) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (t₀ : ℝ) (v₀ : Vec N) (h : ℝ), 0 < h → h ≤ 1 →
      ∀ (a : TimeVelocity N → Mat N) (f u : TimeVelocity N → ℝ),
        ContinuousOn a (krylovClosedCylinder t₀ h v₀) →
        (∀ z ∈ krylovClosedCylinder t₀ h v₀, (a z).IsSymm) →
        (∀ z ∈ krylovClosedCylinder t₀ h v₀,
          lam • (1 : Mat N) ≤ a z ∧ a z ≤ Lam • (1 : Mat N)) →
        MemLp f (parabolicExponent N) (volume.restrict (krylovCylinder t₀ h v₀)) →
        IsScalarC12UpTo u (krylovCylinder t₀ h v₀) (krylovClosedCylinder t₀ h v₀) →
        (∀ᵐ z ∂volume.restrict (krylovCylinder t₀ h v₀),
          scalarTimeDerivative u z - matrixContraction (a z) (scalarSpatialHessian u z)
            ≤ f z) →
        (∀ z ∈ krylovParabolicBoundary t₀ h v₀, u z ≤ 0) →
        ∀ z ∈ krylovCylinder t₀ h v₀,
          u z ≤ C * parabolicLpNormOn N f (krylovCylinder t₀ h v₀) := by
  exact HypoellipticAleksandrov.Parabolic.parabolic_aleksandrov N hN lam Lam hlam hLam

/-- The parabolic Harnack inequality (Krylov–Safonov), comparing every pair of points in the
lower and upper cylinders with a uniform positive constant. -/
theorem parabolic_harnack_unit_cylinder
    (N : ℕ) (hN : 1 ≤ N) (lam : ℝ) (hlam : 0 < lam)
    (Lam : ℝ) (hlamLam : lam ≤ Lam) :
    ∃ h : ℝ, 0 < h ∧
      ∀ (B : CoefficientField N) (u : TimeVelocity N → ℝ),
        IsContinuousCoefficientOn B
          (Set.Ioo (0 : ℝ) 1 ×ˢ euclideanBall (0 : Vec N) 1) →
        (∀ z ∈ Set.Ioo (0 : ℝ) 1 ×ˢ euclideanBall (0 : Vec N) 1,
          (coefficientAt B z).IsSymm) →
        HasLowerEllipticityOn lam B
          (Set.Ioo (0 : ℝ) 1 ×ˢ euclideanBall (0 : Vec N) 1) →
        HasUpperEllipticityOn Lam B
          (Set.Ioo (0 : ℝ) 1 ×ˢ euclideanBall (0 : Vec N) 1) →
        IsScalarC12On u (Set.Ioo (0 : ℝ) 1 ×ˢ euclideanBall (0 : Vec N) 1) →
        IsNonnegativeOn u (Set.Ioo (0 : ℝ) 1 ×ˢ euclideanBall (0 : Vec N) 1) →
        (∀ z ∈ Set.Ioo (0 : ℝ) 1 ×ˢ euclideanBall (0 : Vec N) 1,
          scalarTimeDerivative u z =
            matrixContraction (coefficientAt B z) (scalarSpatialHessian u z)) →
        ∀ P ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2 : ℝ) ×ˢ euclideanBall (0 : Vec N) (1 / 2 : ℝ),
          ∀ P' ∈ Set.Ioo (3 / 4 : ℝ) 1 ×ˢ euclideanBall (0 : Vec N) (1 / 2 : ℝ),
            h * u P ≤ u P' := by
  exact HypoellipticAleksandrov.Parabolic.parabolic_harnack_unit_cylinder N hN lam hlam Lam hlamLam

end KineticAleksandrovChallenge
