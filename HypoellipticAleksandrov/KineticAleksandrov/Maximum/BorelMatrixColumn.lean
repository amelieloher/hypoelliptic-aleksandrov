module

public import HypoellipticAleksandrov.LinearAlgebra.LoewnerEntryBound
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Sharp Euclidean column bounds for elliptic matrices -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov
open scoped MatrixOrder Matrix.Norms.L2Operator

/-- Every column has Euclidean norm at most the upper ellipticity constant. -/
theorem borel_matrix_column_sq_sum_le {d : ℕ} {lam Lam : ℝ} {A : PDE.Mat d}
    (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hlo : lam • (1 : PDE.Mat d) ≤ A) (hhi : A ≤ Lam • (1 : PDE.Mat d))
    (j : Fin d) : ∑ i, (A i j) ^ 2 ≤ Lam ^ 2 := by
  classical
  have hLam0 : 0 ≤ Lam := hlam.le.trans hLam
  have hpos := (HypoellipticAleksandrov.posDef_of_loewner_lower hlam hlo).posSemidef
  have hgap : (Lam • (1 : PDE.Mat d) - A).PosSemidef := Matrix.le_iff.mp hhi
  have hcomm : Commute A (Lam • (1 : PDE.Mat d) - A) := by
    unfold Commute SemiconjBy
    simp only [mul_sub,sub_mul,Matrix.mul_smul,Matrix.smul_mul,
      Matrix.mul_one,Matrix.one_mul]
  have hgprod := hcomm.mul_nonneg hpos.nonneg hgap.nonneg
  have hd := (Matrix.nonneg_iff_posSemidef.mp hgprod).diag_nonneg (i := j)
  have hjj := hgap.diag_nonneg (i := j)
  have hs : A.IsSymm := Matrix.isHermitian_iff_isSymm.mp hpos.isHermitian
  have he : ∑ i, A j i * A i j = ∑ i, (A i j) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hs.apply j i,pow_two]
  have heprod : A * (Lam • (1 : PDE.Mat d) - A) = Lam • A - A * A := by
    rw [Matrix.mul_sub,Matrix.mul_smul,Matrix.mul_one]
  rw [heprod] at hd
  simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,Matrix.mul_apply,he] at hd
  simp only [Matrix.sub_apply,Matrix.smul_apply,Matrix.one_apply,ite_eq_left,
    smul_eq_mul,mul_one,sub_nonneg] at hjj
  nlinarith only [hd,hjj,hLam0]

end HypoellipticAleksandrov.KineticAleksandrov
