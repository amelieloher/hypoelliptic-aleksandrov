module

public import HypoellipticAleksandrov.KineticAleksandrov.EvolutionProblem
public import HypoellipticAleksandrov.LinearAlgebra.LoewnerEntryBound
public import HypoellipticAleksandrov.Geometry.KineticPointMeasure
public import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Null-set replacement of full kinetic coefficients

The passage from smooth to Borel coefficients. A Borel symmetric coefficient
`A(t,x,v)` whose Loewner bounds hold almost everywhere is replaced, on the exceptional null set
only, by `λ I`. The replacement is Borel, symmetric, uniformly elliptic everywhere, and almost
everywhere equal to `A` for kinetic volume.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

open MeasureTheory Set
open scoped MatrixOrder

/-- The coefficient read in product coordinates `(t, (x, v))`. -/
def fullCoefficientProd {d : ℕ} (A : FullKineticCoefficient d) :
    ℝ × (PDE.Vec d × PDE.Vec d) → PDE.Mat d :=
  fun q => A q.1 q.2.1 q.2.2

/-- Reading a kinetic point in product coordinates recovers the kinetic evaluation. -/
theorem fullKineticCoefficientAt_eq_prod {d : ℕ} (A : FullKineticCoefficient d)
    (P : KineticPoint d) :
    fullKineticCoefficientAt A P = fullCoefficientProd A (KineticPoint.equivProd d P) :=
  rfl

/-- Replace only the matrices violating the source bounds by `λ I`. -/
def fullEllipticRepresentative {d : ℕ} (lam Lam : ℝ) (A : FullKineticCoefficient d) :
    FullKineticCoefficient d := by
  classical
  exact fun t x v =>
    if lam • (1 : PDE.Mat d) ≤ A t x v ∧ A t x v ≤ Lam • (1 : PDE.Mat d)
    then A t x v else lam • (1 : PDE.Mat d)

/-- The replacement is Borel, symmetric, elliptic everywhere, and a.e. unchanged. -/
theorem fullEllipticRepresentative_spec {d : ℕ} (lam Lam : ℝ) (hLam : lam ≤ Lam)
    (A : FullKineticCoefficient d)
    (hBorel : Measurable (fullKineticCoefficientAt A))
    (hsymm : ∀ P : KineticPoint d, (fullKineticCoefficientAt A P).IsSymm)
    (hlo : ∀ᵐ P ∂(volume : Measure (KineticPoint d)),
      lam • (1 : PDE.Mat d) ≤ fullKineticCoefficientAt A P)
    (hhi : ∀ᵐ P ∂(volume : Measure (KineticPoint d)),
      fullKineticCoefficientAt A P ≤ Lam • (1 : PDE.Mat d)) :
    Measurable (fullKineticCoefficientAt (fullEllipticRepresentative lam Lam A)) ∧
    (∀ P : KineticPoint d,
      (fullKineticCoefficientAt (fullEllipticRepresentative lam Lam A) P).IsSymm) ∧
    (∀ P : KineticPoint d,
      lam • (1 : PDE.Mat d) ≤ fullKineticCoefficientAt (fullEllipticRepresentative lam Lam A) P ∧
      fullKineticCoefficientAt (fullEllipticRepresentative lam Lam A) P ≤
        Lam • (1 : PDE.Mat d)) ∧
    fullKineticCoefficientAt (fullEllipticRepresentative lam Lam A) =ᵐ[volume]
      fullKineticCoefficientAt A := by
  classical
  let : SecondCountableTopology (PDE.Mat d) :=
    inferInstanceAs (SecondCountableTopology (Fin d → Fin d → ℝ))
  have hscalar : lam • (1 : PDE.Mat d) ≤ Lam • (1 : PDE.Mat d) := by
    rw [Matrix.le_iff, ← sub_smul]
    exact Matrix.PosSemidef.one.smul (sub_nonneg.mpr hLam)
  have heq : fullKineticCoefficientAt (fullEllipticRepresentative lam Lam A) =
      fun P => if lam • (1 : PDE.Mat d) ≤ fullKineticCoefficientAt A P ∧
        fullKineticCoefficientAt A P ≤ Lam • (1 : PDE.Mat d)
        then fullKineticCoefficientAt A P else lam • (1 : PDE.Mat d) := by
    funext P
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [heq]
    exact hBorel.ite
      ((measurableSet_le measurable_const hBorel).inter
        (measurableSet_le hBorel measurable_const)) measurable_const
  · intro P
    rw [heq]
    dsimp only
    split_ifs
    · exact hsymm P
    · exact Matrix.isSymm_one.smul lam
  · intro P
    rw [heq]
    dsimp only
    split_ifs with h
    · exact h
    · exact ⟨le_rfl, hscalar⟩
  · filter_upwards [hlo, hhi] with P hl hh
    rw [heq]
    exact ite_eq_left_iff.mpr fun h => absurd ⟨hl, hh⟩ h

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
