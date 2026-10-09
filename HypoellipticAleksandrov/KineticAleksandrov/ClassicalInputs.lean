module

public import HypoellipticAleksandrov.KineticAleksandrov.Hormander
public import HypoellipticAleksandrov.KineticAleksandrov.EllipsoidDirichlet
public import HypoellipticAleksandrov.Parabolic.ScalarDirichletData
public import HypoellipticAleksandrov.Parabolic.KrylovCylinder
public import PDEFoundation.Geometry.EuclideanBall.Basic

/-!
# Classical theorems as ordinary propositions

Three classical results are used: the locally integrable Hörmander regularity theorem and two
classical parabolic Dirichlet solvability theorems.  This module states each as a `Prop` whose
body is a literal copy of the full type of the corresponding theorem in
`HypoellipticAleksandrov.Statements.*`, without importing it.  Downstream proofs can therefore
take such a `Prop` as an ordinary hypothesis.  Each `Prop` is definitionally the type of the
corresponding theorem.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov

section Hormander

open Set MeasureTheory
open HypoellipticAleksandrov
open scoped BigOperators

/-- Hörmander's hypoellipticity theorem for
locally integrable weak solutions, L. Hörmander, *Hypoelliptic second order differential
equations*, Acta Math. 119 (1967), Thm 1.1.  Mirrors
`HypoellipticAleksandrov.KineticAleksandrov.exists_smooth_aeRepresentative_of_hormander`. -/
def HormanderHypoellipticityStatement : Prop :=
  ∀ {k N : ℕ} {Ω : Set (PDE.Vec N)}
    (_ : IsOpen Ω)
    (X : Fin (k + 1) → PDE.Vec N → PDE.Vec N)
    (c g u : PDE.Vec N → ℝ)
    (_ : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (_ : LieAlgebraSpansOn Ω X)
    (_ : ContDiffOn ℝ (⊤ : ℕ∞) c Ω)
    (_ : HasWeakHormanderEquation Ω X c g u),
    ∃ f : PDE.Vec N → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) f Ω ∧
        u =ᵐ[Measure.restrict volume Ω] f

end Hormander

section LiebermanEllipsoid

open Set
open HypoellipticAleksandrov
open HypoellipticAleksandrov.Parabolic
open scoped MatrixOrder

/-- Classical solvability and uniqueness of
the smooth-data terminal Cauchy--Dirichlet problem on a cylinder over an open ellipsoid,
G. M. Lieberman, *Second Order Parabolic Differential Equations*, World Scientific (1996),
Thm 5.14 (cf. Ladyzhenskaya--Solonnikov--Ural'tseva, Ch. IV).  Mirrors
`HypoellipticAleksandrov.KineticAleksandrov.`
`exists_isClassicalBackwardDirichletSolution_openEllipsoid_uniqueOn_of_lieberman`. -/
def LiebermanEllipsoidDirichletStatement : Prop :=
  ∀ {N : ℕ} {r₀ r₁ : ℝ} {Q : PDE.Mat N}
    (_ : Q.PosDef)
    (_ : r₀ < r₁)
    (lam Lam : ℝ)
    (_ : 0 < lam)
    (_ : lam ≤ Lam)
    (a : CoefficientField N)
    (b : ℝ → PDE.Vec N → PDE.Vec N)
    (_ : ∀ t v, (a t v).IsSymm)
    (_ : IsSmoothCoefficient a)
    (_ : ∀ t v, lam • (1 : PDE.Mat N) ≤ a t v)
    (_ : ∀ t v, a t v ≤ Lam • (1 : PDE.Mat N))
    (_ : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : TimeVelocity N => b z.1 z.2))
    (φ : PDE.Vec N → ℝ)
    (_ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (_ : HasCompactSupport φ)
    (_ : tsupport φ ⊆ openEllipsoid Q),
    ∃ u : TimeVelocity N → ℝ,
      IsClassicalBackwardDirichletSolution
        r₀ r₁ (openEllipsoid Q) a b
        (fun _ _ => 0) (fun _ _ => 0) φ (fun _ => 0) u ∧
      ∀ v : TimeVelocity N → ℝ,
        IsClassicalBackwardDirichletSolution
          r₀ r₁ (openEllipsoid Q) a b
          (fun _ _ => 0) (fun _ _ => 0) φ (fun _ => 0) v →
          Set.EqOn v u
            (scalarParabolicClosedCylinder r₀ r₁ (openEllipsoid Q))

end LiebermanEllipsoid

section LiebermanSource

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open scoped MatrixOrder

end LiebermanSource

end HypoellipticAleksandrov.KineticAleksandrov
