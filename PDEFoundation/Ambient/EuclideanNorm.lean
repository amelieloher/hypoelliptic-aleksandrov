module

public import PDEFoundation.Ambient.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Explicit Euclidean norm on native vectors

`PDE.Vec d = Fin d → ℝ` inherits the finite-product supremum norm. This
module supplies the distinct Euclidean dot product, squared norm, and norm
needed by energy estimates.
-/

@[expose] public section

open scoped BigOperators

namespace PDE

/-- The Euclidean dot product on native project vectors. -/
def vecDot {d : ℕ} (x y : Vec d) : ℝ :=
  ∑ i, x i * y i

/-- The square of the Euclidean norm on native project vectors. -/
def vecNormSq {d : ℕ} (x : Vec d) : ℝ :=
  vecDot x x

/-- The Euclidean norm on native project vectors. -/
noncomputable def vecEuclideanNorm {d : ℕ} (x : Vec d) : ℝ :=
  Real.sqrt (vecNormSq x)

theorem vecDot_comm {d : ℕ} (x y : Vec d) :
    vecDot x y = vecDot y x := by
  unfold vecDot
  refine Finset.sum_congr rfl ?_
  intro i _hi
  ring

theorem vecNormSq_eq_sum_sq {d : ℕ} (x : Vec d) :
    vecNormSq x = ∑ i, x i ^ 2 := by
  simp [vecNormSq, vecDot, pow_two]

theorem vecNormSq_nonneg {d : ℕ} (x : Vec d) :
    0 ≤ vecNormSq x := by
  rw [vecNormSq_eq_sum_sq]
  exact Finset.sum_nonneg fun i _hi => sq_nonneg (x i)

theorem sq_apply_le_vecNormSq {d : ℕ} (x : Vec d) (i : Fin d) :
    x i ^ 2 ≤ vecNormSq x := by
  rw [vecNormSq_eq_sum_sq]
  exact Finset.single_le_sum
    (fun j _hj => sq_nonneg (x j))
    (Finset.mem_univ i)

theorem sq_vecDot_le_vecNormSq_mul_vecNormSq {d : ℕ} (x y : Vec d) :
    vecDot x y ^ 2 ≤ vecNormSq x * vecNormSq y := by
  simpa [vecDot, vecNormSq, pow_two] using
    (Finset.sum_mul_sq_le_sq_mul_sq
      (s := Finset.univ) (f := x) (g := y))

/-- A real Young inequality packaged for Cauchy--Schwarz consequences. -/
theorem abs_le_add_halves_of_sq_le_mul {u A B : ℝ}
    (huSq : u ^ 2 ≤ A * B) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    |u| ≤ A / 2 + B / 2 := by
  have habsSq : |u| ^ 2 ≤ A * B := by
    simpa [sq_abs] using huSq
  have hsumSq : (2 * |u|) ^ 2 ≤ (A + B) ^ 2 := by
    have hzero : 0 ≤ (A - B) ^ 2 := sq_nonneg _
    nlinarith [habsSq, hzero]
  have hsumNonneg : 0 ≤ A + B := add_nonneg hA hB
  have habs2u : 2 * |u| ≤ A + B :=
    le_of_sq_le_sq hsumSq hsumNonneg
  linarith

/-- Young's inequality for the Euclidean dot product. -/
theorem abs_vecDot_le_add_halves_vecNormSq {d : ℕ}
    (x y : Vec d) :
    |vecDot x y| ≤ vecNormSq x / 2 + vecNormSq y / 2 :=
  abs_le_add_halves_of_sq_le_mul
    (sq_vecDot_le_vecNormSq_mul_vecNormSq x y)
    (vecNormSq_nonneg x)
    (vecNormSq_nonneg y)

/-- Young's inequality for scalar-weighted Euclidean dot products. -/
theorem abs_mul_mul_vecDot_le_add_halves_mul_sq_vecNormSq
    {d : ℕ} (a b : ℝ) (x y : Vec d) :
    |a * b * vecDot x y| ≤
      a ^ 2 * vecNormSq x / 2 +
        b ^ 2 * vecNormSq y / 2 := by
  have hcs := sq_vecDot_le_vecNormSq_mul_vecNormSq x y
  have hfactorNonneg : 0 ≤ a ^ 2 * b ^ 2 :=
    mul_nonneg (sq_nonneg a) (sq_nonneg b)
  have hmul :
      a ^ 2 * b ^ 2 * vecDot x y ^ 2 ≤
        a ^ 2 * b ^ 2 * (vecNormSq x * vecNormSq y) :=
    mul_le_mul_of_nonneg_left hcs hfactorNonneg
  have hsq :
      (a * b * vecDot x y) ^ 2 ≤
        (a ^ 2 * vecNormSq x) * (b ^ 2 * vecNormSq y) := by
    nlinarith
  exact abs_le_add_halves_of_sq_le_mul hsq
    (mul_nonneg (sq_nonneg a) (vecNormSq_nonneg x))
    (mul_nonneg (sq_nonneg b) (vecNormSq_nonneg y))

theorem vecNormSq_eq_zero {d : ℕ} {x : Vec d}
    (h : vecNormSq x = 0) :
    x = 0 := by
  funext i
  have hi : x i ^ 2 ≤ 0 := by
    simpa [h] using sq_apply_le_vecNormSq x i
  exact sq_eq_zero_iff.mp (le_antisymm hi (sq_nonneg (x i)))

theorem vecNormSq_eq_zero_iff {d : ℕ} {x : Vec d} :
    vecNormSq x = 0 ↔ x = 0 := by
  constructor
  · exact vecNormSq_eq_zero
  · intro hx
    rw [hx]
    simp [vecNormSq, vecDot]

theorem vecNormSq_smul {d : ℕ} (c : ℝ) (x : Vec d) :
    vecNormSq (c • x) = c ^ 2 * vecNormSq x := by
  rw [vecNormSq_eq_sum_sq, vecNormSq_eq_sum_sq]
  calc
    (∑ i, (c • x) i ^ 2) = ∑ i, c ^ 2 * x i ^ 2 := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    _ = c ^ 2 * ∑ i, x i ^ 2 := by
      rw [Finset.mul_sum]

theorem vecNormSq_add_expand {d : ℕ} (x y : Vec d) :
    vecNormSq (x + y) =
      vecNormSq x + 2 * vecDot x y + vecNormSq y := by
  simp only [vecNormSq, vecDot, Pi.add_apply]
  rw [Finset.sum_congr rfl (fun i (_hi : i ∈ Finset.univ) =>
    show (x i + y i) * (x i + y i) =
      x i * x i + 2 * (x i * y i) + y i * y i by ring)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]

theorem vecNormSq_add_le {d : ℕ} (x y : Vec d) :
    vecNormSq (x + y) ≤
      2 * (vecNormSq x + vecNormSq y) := by
  rw [vecNormSq_eq_sum_sq, vecNormSq_eq_sum_sq,
    vecNormSq_eq_sum_sq]
  calc
    (∑ i, (x + y) i ^ 2) ≤
        ∑ i, 2 * (x i ^ 2 + y i ^ 2) := by
      refine Finset.sum_le_sum ?_
      intro i _hi
      simp only [Pi.add_apply]
      nlinarith [sq_nonneg (x i - y i)]
    _ = 2 * ∑ i, (x i ^ 2 + y i ^ 2) := by
      rw [Finset.mul_sum]
    _ = 2 * (∑ i, x i ^ 2 + ∑ i, y i ^ 2) := by
      rw [Finset.sum_add_distrib]

/-- Four-term Cauchy estimate for the squared Euclidean norm. -/
theorem vecNormSq_four_add_le {d : ℕ} (w x y z : Vec d) :
    vecNormSq (w + x + y + z) ≤
      4 * (vecNormSq w + vecNormSq x +
        vecNormSq y + vecNormSq z) := by
  have hrewrite : w + x + y + z = (w + x) + (y + z) := by
    ext i
    simp
    ring
  calc
    vecNormSq (w + x + y + z) =
        vecNormSq ((w + x) + (y + z)) := by
      rw [hrewrite]
    _ ≤ 2 * (vecNormSq (w + x) + vecNormSq (y + z)) :=
      vecNormSq_add_le (w + x) (y + z)
    _ ≤ 4 * (vecNormSq w + vecNormSq x +
        vecNormSq y + vecNormSq z) := by
      nlinarith [vecNormSq_add_le w x, vecNormSq_add_le y z]

theorem vecNormSq_sub_le {d : ℕ} (x y : Vec d) :
    vecNormSq (x - y) ≤
      2 * (vecNormSq x + vecNormSq y) := by
  rw [vecNormSq_eq_sum_sq, vecNormSq_eq_sum_sq,
    vecNormSq_eq_sum_sq]
  calc
    (∑ i, (x - y) i ^ 2) ≤
        ∑ i, 2 * (x i ^ 2 + y i ^ 2) := by
      refine Finset.sum_le_sum ?_
      intro i _hi
      simp only [Pi.sub_apply]
      nlinarith [sq_nonneg (x i + y i)]
    _ = 2 * ∑ i, (x i ^ 2 + y i ^ 2) := by
      rw [Finset.mul_sum]
    _ = 2 * (∑ i, x i ^ 2 + ∑ i, y i ^ 2) := by
      rw [Finset.sum_add_distrib]

theorem vecNormSq_weighted_add_le {d : ℕ}
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (v w : Vec d) :
    vecNormSq (a • v + b • w) ≤
      a * vecNormSq v + b * vecNormSq w := by
  unfold vecNormSq vecDot
  calc
    ∑ i : Fin d, (a • v + b • w) i * (a • v + b • w) i
        ≤ ∑ i : Fin d,
            (a * (v i * v i) + b * (w i * w i)) := by
      refine Finset.sum_le_sum ?_
      intro i _hi
      have hnonneg :
          0 ≤ a * b * (v i - w i) ^ 2 :=
        mul_nonneg (mul_nonneg ha hb) (sq_nonneg _)
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith
    _ = a * (∑ i : Fin d, v i * v i) +
        b * (∑ i : Fin d, w i * w i) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

theorem vecNormSq_neg {d : ℕ} (x : Vec d) :
    vecNormSq (-x) = vecNormSq x := by
  rw [← neg_one_smul ℝ x, vecNormSq_smul]
  norm_num

theorem vecNormSq_sub_comm {d : ℕ} (x y : Vec d) :
    vecNormSq (x - y) = vecNormSq (y - x) := by
  have hxy : x - y = -(y - x) := by
    ext i
    simp only [Pi.sub_apply, Pi.neg_apply]
    ring
  rw [hxy, vecNormSq_neg]

theorem vecEuclideanNorm_nonneg {d : ℕ} (x : Vec d) :
    0 ≤ vecEuclideanNorm x :=
  Real.sqrt_nonneg _

theorem vecEuclideanNorm_sq {d : ℕ} (x : Vec d) :
    vecEuclideanNorm x ^ 2 = vecNormSq x := by
  exact Real.sq_sqrt (vecNormSq_nonneg x)

theorem vecEuclideanNorm_eq_zero_iff {d : ℕ} {x : Vec d} :
    vecEuclideanNorm x = 0 ↔ x = 0 := by
  constructor
  · intro h
    apply vecNormSq_eq_zero
    rw [← vecEuclideanNorm_sq, h]
    norm_num
  · intro hx
    rw [hx]
    simp [vecEuclideanNorm, vecNormSq, vecDot]

theorem vecEuclideanNorm_pos_iff {d : ℕ} {x : Vec d} :
    0 < vecEuclideanNorm x ↔ x ≠ 0 := by
  rw [lt_iff_le_and_ne, ne_eq, eq_comm,
    vecEuclideanNorm_eq_zero_iff]
  exact and_iff_right (vecEuclideanNorm_nonneg x)

theorem abs_apply_le_vecEuclideanNorm {d : ℕ}
    (x : Vec d) (i : Fin d) :
    |x i| ≤ vecEuclideanNorm x := by
  unfold vecEuclideanNorm
  exact Real.abs_le_sqrt (sq_apply_le_vecNormSq x i)

/-- The Euclidean norm is bounded by the coordinate `ℓ¹` norm. -/
theorem vecEuclideanNorm_le_sum_abs {d : ℕ} (x : Vec d) :
    vecEuclideanNorm x ≤ ∑ i : Fin d, |x i| := by
  have hsumNonneg : 0 ≤ ∑ i : Fin d, |x i| :=
    Finset.sum_nonneg fun i _hi => abs_nonneg (x i)
  have hsq :
      vecNormSq x ≤ (∑ i : Fin d, |x i|) ^ 2 := by
    rw [vecNormSq_eq_sum_sq]
    simpa only [sq_abs] using
      (Finset.sum_sq_le_sq_sum_of_nonneg
        (s := Finset.univ) (f := fun i : Fin d => |x i|)
        (fun i _hi => abs_nonneg (x i)))
  calc
    vecEuclideanNorm x =
        Real.sqrt (vecNormSq x) :=
      rfl
    _ ≤ Real.sqrt ((∑ i : Fin d, |x i|) ^ 2) :=
      Real.sqrt_le_sqrt hsq
    _ = ∑ i : Fin d, |x i| :=
      Real.sqrt_sq hsumNonneg

theorem abs_vecDot_le_vecEuclideanNorm_mul {d : ℕ}
    (x y : Vec d) :
    |vecDot x y| ≤ vecEuclideanNorm x * vecEuclideanNorm y := by
  calc
    |vecDot x y| = Real.sqrt (vecDot x y ^ 2) :=
      (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (vecNormSq x * vecNormSq y) :=
      Real.sqrt_le_sqrt
        (sq_vecDot_le_vecNormSq_mul_vecNormSq x y)
    _ = Real.sqrt (vecNormSq x) * Real.sqrt (vecNormSq y) :=
      Real.sqrt_mul (vecNormSq_nonneg x) _
    _ = vecEuclideanNorm x * vecEuclideanNorm y := rfl

theorem vecEuclideanNorm_smul {d : ℕ} (c : ℝ) (x : Vec d) :
    vecEuclideanNorm (c • x) = |c| * vecEuclideanNorm x := by
  rw [vecEuclideanNorm, vecEuclideanNorm, vecNormSq_smul]
  rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

theorem vecEuclideanNorm_neg {d : ℕ} (x : Vec d) :
    vecEuclideanNorm (-x) = vecEuclideanNorm x := by
  rw [← neg_one_smul ℝ x, vecEuclideanNorm_smul]
  norm_num

theorem vecEuclideanNorm_sub_comm {d : ℕ} (x y : Vec d) :
    vecEuclideanNorm (x - y) = vecEuclideanNorm (y - x) := by
  unfold vecEuclideanNorm
  rw [vecNormSq_sub_comm]

theorem vecEuclideanNorm_add_le {d : ℕ} (x y : Vec d) :
    vecEuclideanNorm (x + y) ≤
      vecEuclideanNorm x + vecEuclideanNorm y := by
  have hdot :
      vecDot x y ≤ vecEuclideanNorm x * vecEuclideanNorm y :=
    (le_abs_self _).trans (abs_vecDot_le_vecEuclideanNorm_mul x y)
  have hsq :
      vecNormSq (x + y) ≤
        (vecEuclideanNorm x + vecEuclideanNorm y) ^ 2 := by
    have hx :
        vecEuclideanNorm x ^ 2 = vecNormSq x :=
      vecEuclideanNorm_sq x
    have hy :
        vecEuclideanNorm y ^ 2 = vecNormSq y :=
      vecEuclideanNorm_sq y
    rw [vecNormSq_add_expand]
    nlinarith [hdot, hx, hy]
  calc
    vecEuclideanNorm (x + y)
        = Real.sqrt (vecNormSq (x + y)) := rfl
    _ ≤ Real.sqrt
          ((vecEuclideanNorm x + vecEuclideanNorm y) ^ 2) :=
      Real.sqrt_le_sqrt hsq
    _ = vecEuclideanNorm x + vecEuclideanNorm y :=
      Real.sqrt_sq
        (add_nonneg
          (vecEuclideanNorm_nonneg x)
          (vecEuclideanNorm_nonneg y))

theorem norm_le_vecEuclideanNorm {d : ℕ} (x : Vec d) :
    ‖x‖ ≤ vecEuclideanNorm x := by
  rw [pi_norm_le_iff_of_nonneg (vecEuclideanNorm_nonneg x)]
  intro i
  simpa only [Real.norm_eq_abs] using
    abs_apply_le_vecEuclideanNorm x i

theorem vecNormSq_le_natCast_mul_norm_sq {d : ℕ} (x : Vec d) :
    vecNormSq x ≤ (d : ℝ) * ‖x‖ ^ 2 := by
  rw [vecNormSq_eq_sum_sq]
  calc
    (∑ i : Fin d, x i ^ 2) ≤ ∑ _i : Fin d, ‖x‖ ^ 2 := by
      refine Finset.sum_le_sum ?_
      intro i _hi
      have hi : |x i| ≤ ‖x‖ := by
        simpa [Real.norm_eq_abs] using norm_le_pi_norm x i
      nlinarith [abs_nonneg (x i), norm_nonneg x, sq_abs (x i)]
    _ = (d : ℝ) * ‖x‖ ^ 2 := by
      simp [Finset.sum_const, nsmul_eq_mul]

theorem vecEuclideanNorm_le_sqrt_natCast_mul_norm {d : ℕ}
    (x : Vec d) :
    vecEuclideanNorm x ≤ Real.sqrt d * ‖x‖ := by
  calc
    vecEuclideanNorm x = Real.sqrt (vecNormSq x) := rfl
    _ ≤ Real.sqrt ((d : ℝ) * ‖x‖ ^ 2) :=
      Real.sqrt_le_sqrt (vecNormSq_le_natCast_mul_norm_sq x)
    _ = Real.sqrt d * ‖x‖ := by
      rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq (norm_nonneg x)]

end PDE
