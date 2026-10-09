module

public import HypoellipticAleksandrov.Ambient.Basic
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import Mathlib.Tactic.NormNum

/-!
# Coefficient fields and ellipticity

This module fixes the curried time--velocity coefficient convention and the
Mathlib Loewner-order ellipticity predicates.  It also proves the matrix-level
positive-definiteness and determinant consequences of a positive lower bound.
-/

@[expose] public section

open scoped BigOperators ContDiff MatrixOrder Matrix.Norms.Elementwise
open Matrix
open MeasureTheory

namespace HypoellipticAleksandrov

/-- The product measurable-space structure on finite real matrices used for coefficient fields. -/
local instance matrixMeasurableSpace (d : ℕ) : MeasurableSpace (PDE.Mat d) := by
  unfold PDE.Mat Matrix
  infer_instance

/-- A real matrix-valued coefficient field, curried in time and velocity. -/
abbrev CoefficientField (d : ℕ) := ℝ → PDE.Vec d → PDE.Mat d

/-- Evaluates a curried coefficient field at a time--velocity pair. -/
def coefficientAt {d : ℕ} (A : CoefficientField d) (z : ℝ × PDE.Vec d) : PDE.Mat d :=
  A z.1 z.2

/-- Evaluation of a coefficient field at a pair agrees with curried evaluation. -/
@[simp] theorem coefficientAt_apply {d : ℕ} (A : CoefficientField d)
    (t : ℝ) (v : PDE.Vec d) :
    coefficientAt A (t, v) = A t v :=
  rfl

/-- A coefficient field is Borel measurable on time--velocity space. -/
def IsBorelCoefficient {d : ℕ} (A : CoefficientField d) : Prop :=
  Measurable (coefficientAt A)

/-- A coefficient field is continuous on time--velocity space. -/
def IsContinuousCoefficient {d : ℕ} (A : CoefficientField d) : Prop :=
  Continuous (coefficientAt A)

/-- A coefficient field is smooth on time--velocity space. -/
def IsSmoothCoefficient {d : ℕ} (A : CoefficientField d) : Prop :=
  ContDiff ℝ ∞ (coefficientAt A)

/-- Every coefficient matrix is symmetric. -/
def IsSymmetricCoefficient {d : ℕ} (A : CoefficientField d) : Prop :=
  ∀ t v, (A t v).IsSymm

/-- Every coefficient matrix is positive definite. -/
def IsPositiveDefiniteCoefficient {d : ℕ} (A : CoefficientField d) : Prop :=
  ∀ t v, (A t v).PosDef

/-- A pointwise lower Loewner ellipticity bound. -/
def HasLowerEllipticity {d : ℕ} (lam : ℝ) (A : CoefficientField d) : Prop :=
  ∀ t v, lam • (1 : PDE.Mat d) ≤ A t v

/-- A pointwise upper Loewner ellipticity bound. -/
def HasUpperEllipticity {d : ℕ} (Lam : ℝ) (A : CoefficientField d) : Prop :=
  ∀ t v, A t v ≤ Lam • (1 : PDE.Mat d)

/-- An almost-everywhere lower Loewner ellipticity bound for product volume. -/
def HasLowerEllipticityAE {d : ℕ} (lam : ℝ) (A : CoefficientField d) : Prop :=
  ∀ᵐ z ∂(volume : Measure (ℝ × PDE.Vec d)), lam • (1 : PDE.Mat d) ≤ coefficientAt A z

/-- An almost-everywhere upper Loewner ellipticity bound for product volume. -/
def HasUpperEllipticityAE {d : ℕ} (Lam : ℝ) (A : CoefficientField d) : Prop :=
  ∀ᵐ z ∂(volume : Measure (ℝ × PDE.Vec d)), coefficientAt A z ≤ Lam • (1 : PDE.Mat d)

/-- The PDE coordinate dot product is Mathlib's finite dot product. -/
theorem vecDot_eq_dotProduct {d : ℕ} (x y : PDE.Vec d) : PDE.vecDot x y = x ⬝ᵥ y :=
  rfl

/-- A Loewner lower bound, with no sign condition on `lam`, gives the
corresponding coordinate quadratic lower bound. -/
theorem vecDot_mulVec_lower_of_loewner
    {d : ℕ} {lam : ℝ} {A : PDE.Mat d}
    (hlo : lam • (1 : PDE.Mat d) ≤ A) (x : PDE.Vec d) :
    lam * PDE.vecNormSq x ≤ PDE.vecDot x (A *ᵥ x) := by
  have hgap : (A - lam • (1 : PDE.Mat d)).PosSemidef := Matrix.le_iff.mp hlo
  have hquad := hgap.dotProduct_mulVec_nonneg x
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul] at hquad
  simpa only [PDE.vecNormSq, PDE.vecDot, dotProduct, mul_comm] using sub_nonneg.mp hquad

private theorem isHermitian_of_isSymm {d : ℕ} {A : PDE.Mat d} (hA : A.IsSymm) :
    A.IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simpa using hA.apply i j

/-- A symmetric coordinate quadratic lower bound implies the corresponding Loewner bound. -/
theorem loewner_lower_of_quadraticForm {d : ℕ} {lam : ℝ} {A : PDE.Mat d}
    (hA : A.IsSymm)
    (hquad : ∀ x, lam * PDE.vecNormSq x ≤ PDE.vecDot x (A *ᵥ x)) :
    lam • (1 : PDE.Mat d) ≤ A := by
  rw [Matrix.le_iff]
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact (isHermitian_of_isSymm hA).sub (by
      apply Matrix.IsHermitian.ext
      intro i j
      by_cases hij : i = j
      · subst j
        simp
      · have hji : j ≠ i := Ne.symm hij
        simp [hij, hji])
  · intro x
    have hquad' : lam * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x) := by
      simpa [PDE.vecNormSq, vecDot_eq_dotProduct] using hquad x
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_sub, dotProduct_smul]
    simpa [sub_eq_add_neg,
      mul_comm, mul_left_comm, mul_assoc] using sub_nonneg.mpr hquad'

/-- A positive lower Loewner bound makes a real matrix positive definite. -/
theorem posDef_of_loewner_lower {d : ℕ} {lam : ℝ} {A : PDE.Mat d}
    (hlam : 0 < lam) (hA : lam • (1 : PDE.Mat d) ≤ A) : A.PosDef := by
  have hP : (A - lam • (1 : PDE.Mat d)).PosSemidef := Matrix.le_iff.mp hA
  have hlamI : (lam • (1 : PDE.Mat d)).PosDef := Matrix.PosDef.one.smul hlam
  have hsplit : A = lam • (1 : PDE.Mat d) + (A - lam • (1 : PDE.Mat d)) := by
    abel
  rw [hsplit]
  exact hlamI.add_posSemidef hP

/-- A positive lower Loewner bound gives the sharp determinant lower bound. -/
theorem det_lower_of_loewner {d : ℕ} {lam : ℝ} {A : PDE.Mat d}
    (hlam : 0 < lam) (hlo : lam • (1 : PDE.Mat d) ≤ A) : lam ^ d ≤ A.det := by
  classical
  have hP : (A - lam • (1 : PDE.Mat d)).PosSemidef := Matrix.le_iff.mp hlo
  have hA : A.PosDef := posDef_of_loewner_lower hlam hlo
  have heigen : ∀ i : Fin d, lam ≤ hA.isHermitian.eigenvalues i := by
    intro i
    have hnonneg := hP.dotProduct_mulVec_nonneg (⇑(hA.isHermitian.eigenvectorBasis i))
    rw [dotProduct_comm] at hnonneg
    have hsub : 0 ≤ hA.isHermitian.eigenvalues i - lam := by
      simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        hA.isHermitian.mulVec_eigenvectorBasis, sub_dotProduct, smul_dotProduct,
        ← EuclideanSpace.inner_eq_star_dotProduct,
        inner_self_eq_norm_sq_to_K, hA.isHermitian.eigenvectorBasis.orthonormal.1 i,
        smul_eq_mul] at hnonneg
      norm_num at hnonneg
      exact sub_nonneg.mpr hnonneg
    exact sub_nonneg.mp hsub
  calc
    lam ^ d = ∏ _i : Fin d, lam := by simp
    _ ≤ ∏ i : Fin d, hA.isHermitian.eigenvalues i :=
      Finset.prod_le_prod₀
        (fun _ _ => hlam.le)
        (fun i _ => heigen i)
    _ = A.det := by
      rw [hA.isHermitian.det_eq_prod_eigenvalues]
      simp

namespace HasLowerEllipticity

/-- A positive pointwise lower ellipticity bound gives pointwise positive definiteness. -/
theorem posDef {d : ℕ} {lam : ℝ} {A : CoefficientField d}
    (h : HasLowerEllipticity lam A) (hlam : 0 < lam) (t : ℝ) (v : PDE.Vec d) :
    (A t v).PosDef :=
  posDef_of_loewner_lower hlam (h t v)

/-- A positive pointwise lower ellipticity bound gives the pointwise determinant bound. -/
theorem det_lower {d : ℕ} {lam : ℝ} {A : CoefficientField d}
    (h : HasLowerEllipticity lam A) (hlam : 0 < lam) (t : ℝ) (v : PDE.Vec d) :
    lam ^ d ≤ (A t v).det :=
  det_lower_of_loewner hlam (h t v)

end HasLowerEllipticity

end HypoellipticAleksandrov
