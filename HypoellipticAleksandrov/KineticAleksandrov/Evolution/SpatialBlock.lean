module

public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.PosDef
public import PDEFoundation.Ambient.EuclideanNorm

/-!
# Block coordinates on `PDE.Vec (n + n)`

The straightened truncation problem of Proposition 2.1 lives on the
spatial space `PDE.Vec (n + n)` of the pair `(Y, z)`, with `Y = y - γ_k(σ)` the straightened
diffused coordinate and `z` the transported coordinate.  This module records the literal
block-coordinate definitions: the two coordinate projections, the packing map, and the block
matrix `diag(A, ε I)`, together with their basic evaluations, the block quadratic form, and
the Loewner-order and positive-definiteness facts used to discharge the premises of the
Dirichlet solvability theorem (Lieberman, Theorem 5.14).  No new vector carrier is introduced.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open scoped MatrixOrder ContDiff Matrix

namespace HypoellipticAleksandrov.KineticAleksandrov

/-- The first (diffused `Y`) block of a vector of `PDE.Vec (n + n)`. -/
def spatialY {n : ℕ} (x : PDE.Vec (n + n)) : PDE.Vec n :=
  fun i => x (Fin.castAdd n i)

/-- The second (transported `z`) block of a vector of `PDE.Vec (n + n)`. -/
def spatialZ {n : ℕ} (x : PDE.Vec (n + n)) : PDE.Vec n :=
  fun i => x (Fin.natAdd n i)

/-- Pack a diffused block `y` and a transported block `z` into `PDE.Vec (n + n)`. -/
def spatialPack {n : ℕ} (y z : PDE.Vec n) : PDE.Vec (n + n) :=
  Fin.append y z

/-- The block matrix `diag(A, ε I)` on `PDE.Vec (n + n)`. -/
noncomputable def viscousBlockMatrix {n : ℕ} (A : PDE.Mat n) (ε : ℝ) :
    PDE.Mat (n + n) :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks A 0 0 (ε • (1 : PDE.Mat n)))

section Coordinates

variable {n : ℕ}

@[simp] theorem spatialY_apply (x : PDE.Vec (n + n)) (i : Fin n) :
    spatialY x i = x (Fin.castAdd n i) :=
  rfl

theorem spatialZ_apply_natAdd (x : PDE.Vec (n + n)) (i : Fin n) :
    spatialZ x i = x (Fin.natAdd n i) :=
  rfl

@[simp] theorem spatialZ_apply (x : PDE.Vec (n + n)) (i : Fin n) :
    spatialZ x i = x (i.addNat n) := by
  rw [← Fin.natAdd_eq_addNat]
  rfl

@[simp] theorem spatialPack_castAdd (y z : PDE.Vec n) (i : Fin n) :
    spatialPack y z (Fin.castAdd n i) = y i :=
  Fin.append_left y z i

theorem spatialPack_natAdd (y z : PDE.Vec n) (i : Fin n) :
    spatialPack y z (Fin.natAdd n i) = z i :=
  Fin.append_right y z i

@[simp] theorem spatialPack_addNat (y z : PDE.Vec n) (i : Fin n) :
    spatialPack y z (i.addNat n) = z i := by
  rw [← Fin.natAdd_eq_addNat]
  exact spatialPack_natAdd y z i

@[simp] theorem spatialY_spatialPack (y z : PDE.Vec n) : spatialY (spatialPack y z) = y := by
  funext i
  simp

@[simp] theorem spatialZ_spatialPack (y z : PDE.Vec n) : spatialZ (spatialPack y z) = z := by
  funext i
  exact spatialPack_natAdd y z i

@[simp] theorem spatialPack_spatialY_spatialZ (x : PDE.Vec (n + n)) :
    spatialPack (spatialY x) (spatialZ x) = x := by
  funext k
  refine Fin.addCases (fun i => ?_) (fun i => ?_) k
  · rw [spatialPack_castAdd]; rfl
  · rw [spatialPack_natAdd]; rfl

theorem spatialPack_injective : Function.Injective (fun p : PDE.Vec n × PDE.Vec n =>
    spatialPack p.1 p.2) := by
  intro p q h
  have h1 := congrArg spatialY h
  have h2 := congrArg spatialZ h
  simp only [spatialY_spatialPack, spatialZ_spatialPack] at h1 h2
  exact Prod.ext h1 h2

theorem spatialPack_eq_iff {y z y' z' : PDE.Vec n} :
    spatialPack y z = spatialPack y' z' ↔ y = y' ∧ z = z' := by
  constructor
  · intro h
    exact ⟨by simpa using congrArg spatialY h, by simpa using congrArg spatialZ h⟩
  · rintro ⟨rfl, rfl⟩
    rfl

@[simp] theorem spatialY_add (x x' : PDE.Vec (n + n)) :
    spatialY (x + x') = spatialY x + spatialY x' :=
  rfl

@[simp] theorem spatialZ_add (x x' : PDE.Vec (n + n)) :
    spatialZ (x + x') = spatialZ x + spatialZ x' :=
  rfl

@[simp] theorem spatialY_sub (x x' : PDE.Vec (n + n)) :
    spatialY (x - x') = spatialY x - spatialY x' :=
  rfl

@[simp] theorem spatialZ_sub (x x' : PDE.Vec (n + n)) :
    spatialZ (x - x') = spatialZ x - spatialZ x' :=
  rfl

@[simp] theorem spatialY_neg (x : PDE.Vec (n + n)) : spatialY (-x) = -spatialY x :=
  rfl

@[simp] theorem spatialZ_neg (x : PDE.Vec (n + n)) : spatialZ (-x) = -spatialZ x :=
  rfl

@[simp] theorem spatialY_smul (c : ℝ) (x : PDE.Vec (n + n)) :
    spatialY (c • x) = c • spatialY x :=
  rfl

@[simp] theorem spatialZ_smul (c : ℝ) (x : PDE.Vec (n + n)) :
    spatialZ (c • x) = c • spatialZ x :=
  rfl

@[simp] theorem spatialY_zero : spatialY (0 : PDE.Vec (n + n)) = 0 :=
  rfl

@[simp] theorem spatialZ_zero : spatialZ (0 : PDE.Vec (n + n)) = 0 :=
  rfl

theorem spatialPack_add (y z y' z' : PDE.Vec n) :
    spatialPack (y + y') (z + z') = spatialPack y z + spatialPack y' z' := by
  rw [← spatialPack_spatialY_spatialZ (spatialPack y z + spatialPack y' z')]
  simp

theorem spatialPack_sub (y z y' z' : PDE.Vec n) :
    spatialPack (y - y') (z - z') = spatialPack y z - spatialPack y' z' := by
  rw [← spatialPack_spatialY_spatialZ (spatialPack y z - spatialPack y' z')]
  simp

theorem spatialPack_neg (y z : PDE.Vec n) :
    spatialPack (-y) (-z) = -spatialPack y z := by
  rw [← spatialPack_spatialY_spatialZ (-spatialPack y z)]
  simp

theorem spatialPack_smul (c : ℝ) (y z : PDE.Vec n) :
    spatialPack (c • y) (c • z) = c • spatialPack y z := by
  rw [← spatialPack_spatialY_spatialZ (c • spatialPack y z)]
  simp

@[simp] theorem spatialPack_zero : spatialPack (0 : PDE.Vec n) 0 = 0 := by
  simpa using spatialPack_smul 0 (0 : PDE.Vec n) 0

/-- The Euclidean dot product splits along the block decomposition. -/
theorem vecDot_eq_spatial (x x' : PDE.Vec (n + n)) :
    PDE.vecDot x x' = PDE.vecDot (spatialY x) (spatialY x') +
      PDE.vecDot (spatialZ x) (spatialZ x') := by
  simp only [PDE.vecDot, Fin.sum_univ_add, spatialY, spatialZ]

/-- The squared Euclidean norm splits along the block decomposition. -/
theorem vecNormSq_eq_spatial (x : PDE.Vec (n + n)) :
    PDE.vecNormSq x = PDE.vecNormSq (spatialY x) + PDE.vecNormSq (spatialZ x) :=
  vecDot_eq_spatial x x

theorem vecNormSq_spatialPack (y z : PDE.Vec n) :
    PDE.vecNormSq (spatialPack y z) = PDE.vecNormSq y + PDE.vecNormSq z := by
  rw [vecNormSq_eq_spatial]
  simp

/-- The first block projection is smooth. -/
theorem contDiff_spatialY {m : WithTop ℕ∞} :
    ContDiff ℝ m (spatialY : PDE.Vec (n + n) → PDE.Vec n) :=
  contDiff_pi.2 fun i => contDiff_apply ℝ ℝ (Fin.castAdd n i)

/-- The second block projection is smooth. -/
theorem contDiff_spatialZ {m : WithTop ℕ∞} :
    ContDiff ℝ m (spatialZ : PDE.Vec (n + n) → PDE.Vec n) :=
  contDiff_pi.2 fun i => contDiff_apply ℝ ℝ (Fin.natAdd n i)

/-- Packing two smooth block maps is smooth. -/
theorem contDiff_spatialPack {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : WithTop ℕ∞} {f g : E → PDE.Vec n} (hf : ContDiff ℝ m f) (hg : ContDiff ℝ m g) :
    ContDiff ℝ m (fun x => spatialPack (f x) (g x)) := by
  refine contDiff_pi.2 fun k => ?_
  refine Fin.addCases (fun i => ?_) (fun i => ?_) k
  · simp only [spatialPack_castAdd]
    exact contDiff_pi.1 hf i
  · simp only [spatialPack_natAdd]
    exact contDiff_pi.1 hg i

end Coordinates

section BlockMatrix

variable {n : ℕ}

@[simp] theorem viscousBlockMatrix_castAdd_castAdd (A : PDE.Mat n) (ε : ℝ) (i j : Fin n) :
    viscousBlockMatrix A ε (Fin.castAdd n i) (Fin.castAdd n j) = A i j := by
  simp only [viscousBlockMatrix, Matrix.reindex_apply, Matrix.submatrix_apply,
    finSumFinEquiv_symm_apply_castAdd, Matrix.fromBlocks_apply₁₁]

theorem viscousBlockMatrix_castAdd_natAdd (A : PDE.Mat n) (ε : ℝ) (i j : Fin n) :
    viscousBlockMatrix A ε (Fin.castAdd n i) (Fin.natAdd n j) = 0 := by
  simp only [viscousBlockMatrix, Matrix.reindex_apply, Matrix.submatrix_apply,
    finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
    Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]

theorem viscousBlockMatrix_natAdd_castAdd (A : PDE.Mat n) (ε : ℝ) (i j : Fin n) :
    viscousBlockMatrix A ε (Fin.natAdd n i) (Fin.castAdd n j) = 0 := by
  simp only [viscousBlockMatrix, Matrix.reindex_apply, Matrix.submatrix_apply,
    finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
    Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]

theorem viscousBlockMatrix_natAdd_natAdd (A : PDE.Mat n) (ε : ℝ) (i j : Fin n) :
    viscousBlockMatrix A ε (Fin.natAdd n i) (Fin.natAdd n j) =
      ε * (1 : PDE.Mat n) i j := by
  simp only [viscousBlockMatrix, Matrix.reindex_apply, Matrix.submatrix_apply,
    finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₂₂, Matrix.smul_apply,
    smul_eq_mul]

@[simp] theorem viscousBlockMatrix_castAdd_addNat (A : PDE.Mat n) (ε : ℝ) (i j : Fin n) :
    viscousBlockMatrix A ε (Fin.castAdd n i) (j.addNat n) = 0 := by
  rw [← Fin.natAdd_eq_addNat]
  exact viscousBlockMatrix_castAdd_natAdd A ε i j

@[simp] theorem viscousBlockMatrix_addNat_castAdd (A : PDE.Mat n) (ε : ℝ) (i j : Fin n) :
    viscousBlockMatrix A ε (i.addNat n) (Fin.castAdd n j) = 0 := by
  rw [← Fin.natAdd_eq_addNat]
  exact viscousBlockMatrix_natAdd_castAdd A ε i j

@[simp] theorem viscousBlockMatrix_addNat_addNat (A : PDE.Mat n) (ε : ℝ) (i j : Fin n) :
    viscousBlockMatrix A ε (i.addNat n) (j.addNat n) = ε * (1 : PDE.Mat n) i j := by
  rw [← Fin.natAdd_eq_addNat, ← Fin.natAdd_eq_addNat]
  exact viscousBlockMatrix_natAdd_natAdd A ε i j

/-- Entrywise extensionality for matrices on `Fin (n + n)` along the block decomposition. -/
theorem matrix_ext_blocks {M M' : PDE.Mat (n + n)}
    (h₁₁ : ∀ i j, M (Fin.castAdd n i) (Fin.castAdd n j) = M' (Fin.castAdd n i) (Fin.castAdd n j))
    (h₁₂ : ∀ i j, M (Fin.castAdd n i) (Fin.natAdd n j) = M' (Fin.castAdd n i) (Fin.natAdd n j))
    (h₂₁ : ∀ i j, M (Fin.natAdd n i) (Fin.castAdd n j) = M' (Fin.natAdd n i) (Fin.castAdd n j))
    (h₂₂ : ∀ i j, M (Fin.natAdd n i) (Fin.natAdd n j) = M' (Fin.natAdd n i) (Fin.natAdd n j)) :
    M = M' := by
  ext k l
  refine Fin.addCases (fun i => ?_) (fun i => ?_) k <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) l
  · exact h₁₁ i j
  · exact h₁₂ i j
  · exact h₂₁ i j
  · exact h₂₂ i j

/-- The block matrix applied to a vector acts blockwise. -/
theorem viscousBlockMatrix_mulVec (A : PDE.Mat n) (ε : ℝ) (x : PDE.Vec (n + n)) :
    viscousBlockMatrix A ε *ᵥ x = spatialPack (A *ᵥ spatialY x) (ε • spatialZ x) := by
  funext k
  refine Fin.addCases (fun i => ?_) (fun i => ?_) k
  · rw [spatialPack_castAdd]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_add]
  · rw [spatialPack_natAdd]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_add, Matrix.one_apply]

/-- The block quadratic form. -/
theorem vecDot_viscousBlockMatrix_mulVec (A : PDE.Mat n) (ε : ℝ) (x : PDE.Vec (n + n)) :
    PDE.vecDot x (viscousBlockMatrix A ε *ᵥ x) =
      PDE.vecDot (spatialY x) (A *ᵥ spatialY x) + ε * PDE.vecNormSq (spatialZ x) := by
  rw [viscousBlockMatrix_mulVec, vecDot_eq_spatial]
  simp only [spatialY_spatialPack, spatialZ_spatialPack]
  simp [PDE.vecDot, PDE.vecNormSq, Finset.mul_sum, mul_left_comm]

theorem viscousBlockMatrix_sub (A A' : PDE.Mat n) (ε ε' : ℝ) :
    viscousBlockMatrix A ε - viscousBlockMatrix A' ε' = viscousBlockMatrix (A - A') (ε - ε') := by
  refine matrix_ext_blocks ?_ ?_ ?_ ?_ <;> intro i j <;> simp [sub_mul]

theorem viscousBlockMatrix_smul_one (c : ℝ) :
    viscousBlockMatrix (c • (1 : PDE.Mat n)) c = c • (1 : PDE.Mat (n + n)) := by
  refine matrix_ext_blocks ?_ ?_ ?_ ?_ <;> intro i j
  · simp [Matrix.one_apply, Fin.castAdd_inj]
  · simp only [viscousBlockMatrix_castAdd_natAdd, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul]
    have hne : ¬ Fin.castAdd n i = Fin.natAdd n j := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_castAdd, Fin.val_natAdd] at this
      omega
    simp only [hne, ↓reduceIte, mul_zero]
  · simp only [viscousBlockMatrix_natAdd_castAdd, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul]
    have hne : ¬ Fin.natAdd n i = Fin.castAdd n j := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_castAdd, Fin.val_natAdd] at this
      omega
    simp only [hne, ↓reduceIte, mul_zero]
  · simp [Matrix.one_apply]

theorem viscousBlockMatrix_isSymm {A : PDE.Mat n} (hA : A.IsSymm) (ε : ℝ) :
    (viscousBlockMatrix A ε).IsSymm := by
  ext k l
  rw [Matrix.transpose_apply]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) k <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) l
  · simp [hA.apply]
  · simp
  · simp
  · simp [Matrix.one_apply, eq_comm]

theorem viscousBlockMatrix_posSemidef {A : PDE.Mat n} (hA : A.PosSemidef) {ε : ℝ}
    (hε : 0 ≤ ε) : (viscousBlockMatrix A ε).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · rw [Matrix.isHermitian_iff_isSymm]
    exact viscousBlockMatrix_isSymm hA.isHermitian.isSymm ε
  · have h := vecDot_viscousBlockMatrix_mulVec A ε x
    have hA' := hA.dotProduct_mulVec_nonneg (spatialY x)
    have hz := PDE.vecNormSq_nonneg (spatialZ x)
    simp only [star_trivial] at hA' ⊢
    change 0 ≤ PDE.vecDot x (viscousBlockMatrix A ε *ᵥ x)
    rw [h]
    exact add_nonneg hA' (mul_nonneg hε hz)

theorem viscousBlockMatrix_posDef {A : PDE.Mat n} (hA : A.PosDef) {ε : ℝ}
    (hε : 0 < ε) : (viscousBlockMatrix A ε).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec] at hA ⊢
  refine ⟨?_, fun x hx => ?_⟩
  · rw [Matrix.isHermitian_iff_isSymm]
    exact viscousBlockMatrix_isSymm hA.1.isSymm ε
  · have h := vecDot_viscousBlockMatrix_mulVec A ε x
    change 0 < PDE.vecDot x (viscousBlockMatrix A ε *ᵥ x)
    rw [h]
    by_cases hy : spatialY x = 0
    · have hz : spatialZ x ≠ 0 := by
        intro hz
        apply hx
        rw [← spatialPack_spatialY_spatialZ x, hy, hz]
        simp
      have hzpos : 0 < PDE.vecNormSq (spatialZ x) := by
        rcases (PDE.vecNormSq_nonneg (spatialZ x)).lt_or_eq with h' | h'
        · exact h'
        · exfalso
          apply hz
          funext i
          have := PDE.sq_apply_le_vecNormSq (spatialZ x) i
          rw [← h'] at this
          simpa using this
      rw [hy]
      simp only [Matrix.mulVec_zero, PDE.vecDot, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
        zero_add]
      exact mul_pos hε hzpos
    · have hA' := hA.2 hy
      simp only [star_trivial] at hA'
      have hz := PDE.vecNormSq_nonneg (spatialZ x)
      exact add_pos_of_pos_of_nonneg hA' (mul_nonneg hε.le hz)

/-- `c • 1 ≤ d • 1` for `c ≤ d`, in the Loewner order. -/
theorem smul_one_le_smul_one {m : ℕ} {c d : ℝ} (h : c ≤ d) :
    c • (1 : PDE.Mat m) ≤ d • (1 : PDE.Mat m) := by
  rw [Matrix.le_iff, ← sub_smul]
  exact Matrix.PosSemidef.one.smul (sub_nonneg.2 h)

/-- The block matrix is monotone in both blocks for the Loewner order. -/
theorem viscousBlockMatrix_mono {A A' : PDE.Mat n} {ε ε' : ℝ} (hA : A ≤ A') (hε : ε ≤ ε') :
    viscousBlockMatrix A ε ≤ viscousBlockMatrix A' ε' := by
  rw [Matrix.le_iff, viscousBlockMatrix_sub]
  exact viscousBlockMatrix_posSemidef (Matrix.le_iff.1 hA) (sub_nonneg.2 hε)

end BlockMatrix

end HypoellipticAleksandrov.KineticAleksandrov
