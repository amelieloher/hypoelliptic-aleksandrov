module

public import HypoellipticAleksandrov.LinearAlgebra.LoewnerEntryBound
public import HypoellipticAleksandrov.Parabolic.SpatialDifferenceQuotient

/-!
# Pointwise coercivity for the generic pre-lift spatial difference quotient

This focused support module isolates the algebraic fixed-direction flux coercivity
estimate used by the generic fixed-cylinder argument.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory Set
open scoped Convex ENNReal MatrixOrder

/-- A coarse scalar Young inequality with the coefficient used for absorbing
one error term into elliptic coercivity. -/
private theorem mul_le_lambda_eighth_sq_add (lam a b : ℝ) (hlam : 0 < lam) :
    a * b ≤ (lam / 8) * b ^ 2 + (2 / lam) * a ^ 2 := by
  rw [show (lam / 8) * b ^ 2 + (2 / lam) * a ^ 2 =
      ((lam ^ 2 / 8) * b ^ 2 + 2 * a ^ 2) / lam by field_simp]
  rw [le_div_iff₀ hlam]
  nlinarith [sq_nonneg (lam * b - 4 * a)]

/-- A lower Loewner bound at the forward-translated point gives the weighted
coordinate coercivity needed by the fixed-core principal term. -/
private theorem translatedPrincipal_lower_pointwise
    {d : ℕ} {lam w : ℝ} (A : TimeVelocity d → PDE.Mat d)
    (k : Fin d) (h : ℝ) (z : TimeVelocity d) (H : Fin d → ℝ)
    (hw : 0 ≤ w)
    (hAlower : lam • (1 : PDE.Mat d) ≤ A (spatialShift k h z)) :
    lam * w * ∑ i, H i ^ 2 ≤
      w * ∑ i, ∑ j,
        spatialTranslate k h (fun x ↦ A x i j) z * H j * H i := by
  have hquad := vecDot_mulVec_lower_of_loewner hAlower H
  have hscaled := mul_le_mul_of_nonneg_left hquad hw
  calc
    lam * w * ∑ i, H i ^ 2 = w * (lam * PDE.vecNormSq H) := by
      unfold PDE.vecNormSq PDE.vecDot
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ w * PDE.vecDot H (Matrix.mulVec (A (spatialShift k h z)) H) := hscaled
    _ = w * ∑ i, ∑ j,
        spatialTranslate k h (fun x ↦ A x i j) z * H j * H i := by
      unfold PDE.vecDot Matrix.mulVec dotProduct
      simp only [Finset.mul_sum, spatialTranslate_apply]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- Sharp pointwise coercive decomposition of the fixed-direction flux pairing.
The actual three error sums are retained, rather than first replacing the
cutoff gradient by a uniform bound.  This is the algebraic checkpoint needed
for an absorption that remains valid where the cutoff vanishes. -/
private theorem fixedDirection_fluxPairing_coercive_raw
    {d : ℕ} {lam w : ℝ}
    (A : TimeVelocity d → PDE.Mat d)
    (G H : Fin d → ℝ) (Dw : Fin d → ℝ) (Q : ℝ)
    (k : Fin d) (h : ℝ) (z : TimeVelocity d)
    (hw : 0 ≤ w)
    (hAlower : lam • (1 : PDE.Mat d) ≤ A (spatialShift k h z)) :
    lam * w * ∑ i, H i ^ 2 ≤
      (∑ i : Fin d,
        (∑ j : Fin d,
          (spatialTranslate k h (fun x ↦ A x i j) z * H j +
            spatialDifferenceQuotient k h (fun x ↦ A x i j) z * G j)) *
          (Dw i * Q + w * H i)) +
      |∑ i : Fin d, ∑ j : Fin d,
        spatialTranslate k h (fun x ↦ A x i j) z * H j * (Dw i * Q)| +
      |∑ i : Fin d, ∑ j : Fin d,
        spatialDifferenceQuotient k h (fun x ↦ A x i j) z * G j * (w * H i)| +
      |∑ i : Fin d, ∑ j : Fin d,
        spatialDifferenceQuotient k h (fun x ↦ A x i j) z * G j * (Dw i * Q)| := by
  let main : ℝ := w * ∑ i : Fin d, ∑ j : Fin d,
    spatialTranslate k h (fun x ↦ A x i j) z * H j * H i
  let e₁ : ℝ := ∑ i : Fin d, ∑ j : Fin d,
    spatialTranslate k h (fun x ↦ A x i j) z * H j * (Dw i * Q)
  let e₂ : ℝ := ∑ i : Fin d, ∑ j : Fin d,
    spatialDifferenceQuotient k h (fun x ↦ A x i j) z * G j * (w * H i)
  let e₃ : ℝ := ∑ i : Fin d, ∑ j : Fin d,
    spatialDifferenceQuotient k h (fun x ↦ A x i j) z * G j * (Dw i * Q)
  have hmain : lam * w * ∑ i, H i ^ 2 ≤ main := by
    simpa only [main] using
      translatedPrincipal_lower_pointwise A k h z H hw hAlower
  have hsplit :
      (∑ i : Fin d,
        (∑ j : Fin d,
          (spatialTranslate k h (fun x ↦ A x i j) z * H j +
            spatialDifferenceQuotient k h (fun x ↦ A x i j) z * G j)) *
          (Dw i * Q + w * H i)) = main + e₁ + e₂ + e₃ := by
    simp only [main, e₁, e₂, e₃]
    simp_rw [Finset.mul_sum]
    repeat rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Finset.sum_add_distrib]
    repeat rw [← Finset.sum_add_distrib]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsplit]
  have h₁ : -|e₁| ≤ e₁ := neg_abs_le e₁
  have h₂ : -|e₂| ≤ e₂ := neg_abs_le e₂
  have h₃ : -|e₃| ≤ e₃ := neg_abs_le e₃
  simpa only [e₁, e₂, e₃] using (show
    lam * w * ∑ i, H i ^ 2 ≤ main + e₁ + e₂ + e₃ + |e₁| + |e₂| + |e₃| by
      linarith)

/-- Summing an expression independent of the first of two positive-dimensional
indices contributes the real dimension factor. -/
private theorem sum_fin_sum_repeated_right
    {d : ℕ} (_hd : 0 < d) (f : Fin d → ℝ) :
    ∑ _i : Fin d, ∑ j : Fin d, f j = (d : ℝ) * ∑ j : Fin d, f j := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Summing an expression independent of the second of two positive-dimensional
indices contributes the real dimension factor. -/
private theorem sum_fin_sum_repeated_left
    {d : ℕ} (_hd : 0 < d) (f : Fin d → ℝ) :
    ∑ i : Fin d, ∑ _j : Fin d, f i = (d : ℝ) * ∑ i : Fin d, f i := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Finset.mul_sum]

/-- The translated-coefficient cutoff error is absorbed entrywise while
retaining the literal cutoff-gradient square bound. -/
private theorem fixedDirection_errorOne_le
    {d : ℕ} {lam Lam Keta w : ℝ}
    (A : TimeVelocity d → PDE.Mat d) (H Dw : Fin d → ℝ) (Q : ℝ)
    (k : Fin d) (h : ℝ) (z : TimeVelocity d)
    (hd : 0 < d) (hlam : 0 < lam) (hKeta : 0 ≤ Keta)
    (hw : 0 ≤ w)
    (hEll : lam • (1 : PDE.Mat d) ≤ A (spatialShift k h z) ∧
      A (spatialShift k h z) ≤ Lam • (1 : PDE.Mat d))
    (hDwSq : ∀ i, Dw i ^ 2 ≤ 4 * Keta ^ 2 * w) :
    |∑ i : Fin d, ∑ j : Fin d,
        spatialTranslate k h (fun x ↦ A x i j) z * H j * (Dw i * Q)| ≤
      (lam / 8) * w * ∑ j : Fin d, H j ^ 2 +
        (8 * (d : ℝ) ^ 3 / lam * Lam ^ 2 * Keta ^ 2) * Q ^ 2 := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have halloc : 0 < lam / (d : ℝ) := div_pos hlam hdR
  have hwSqrt : (Real.sqrt w) ^ 2 = w := Real.sq_sqrt hw
  have hDw (i : Fin d) : |Dw i| ≤ 2 * Keta * Real.sqrt w := by
    have hright : 0 ≤ 2 * Keta * Real.sqrt w :=
      mul_nonneg (mul_nonneg (by norm_num) hKeta) (Real.sqrt_nonneg _)
    apply (sq_le_sq₀ (abs_nonneg _) hright).1
    rw [sq_abs, mul_pow, mul_pow, hwSqrt]
    norm_num
    exact hDwSq i
  have hLam : 0 ≤ Lam := by
    have hcoef := abs_apply_le_of_loewner hlam hEll.1 hEll.2
      (⟨0, hd⟩ : Fin d) (⟨0, hd⟩ : Fin d)
    exact (abs_nonneg _).trans hcoef
  calc
    |∑ i : Fin d, ∑ j : Fin d,
        spatialTranslate k h (fun x ↦ A x i j) z * H j * (Dw i * Q)| ≤
        ∑ i : Fin d, ∑ j : Fin d,
          |spatialTranslate k h (fun x ↦ A x i j) z * H j * (Dw i * Q)| := by
      exact (Finset.abs_sum_le_sum_abs _ _).trans <|
        Finset.sum_le_sum fun _ _ ↦ Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin d, ∑ j : Fin d,
        (((lam / (d : ℝ)) / 8) * (Real.sqrt w * |H j|) ^ 2 +
          (2 / (lam / (d : ℝ))) * (2 * Lam * Keta * |Q|) ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      have hcoef : |spatialTranslate k h (fun x ↦ A x i j) z| ≤ Lam := by
        simpa only [spatialTranslate_apply] using
          abs_apply_le_of_loewner hlam hEll.1 hEll.2 i j
      have hpre :
          |spatialTranslate k h (fun x ↦ A x i j) z * H j * (Dw i * Q)| ≤
            (2 * Lam * Keta * |Q|) * (Real.sqrt w * |H j|) := by
        rw [abs_mul, abs_mul, abs_mul]
        calc
          |spatialTranslate k h (fun x ↦ A x i j) z| * |H j| *
              (|Dw i| * |Q|) ≤ Lam * |H j| *
                ((2 * Keta * Real.sqrt w) * |Q|) := by
            gcongr
            exact hDw i
          _ = (2 * Lam * Keta * |Q|) * (Real.sqrt w * |H j|) := by ring
      exact hpre.trans (mul_le_lambda_eighth_sq_add
        (lam / (d : ℝ)) (2 * Lam * Keta * |Q|)
          (Real.sqrt w * |H j|) halloc)
    _ = (lam / 8) * w * ∑ j : Fin d, H j ^ 2 +
        (8 * (d : ℝ) ^ 3 / lam * Lam ^ 2 * Keta ^ 2) * Q ^ 2 := by
      simp_rw [Finset.sum_add_distrib]
      simp only [← Finset.mul_sum, sum_fin_sum_repeated_right hd,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_pow, hwSqrt, sq_abs]
      field_simp
      ring

/-- The principal coefficient-quotient error is absorbed entrywise with the
same dimension allocation as the translated-coefficient error. -/
private theorem fixedDirection_errorTwo_le
    {d : ℕ} {lam Ma w : ℝ}
    (A : TimeVelocity d → PDE.Mat d) (G H : Fin d → ℝ)
    (k : Fin d) (h : ℝ) (z : TimeVelocity d)
    (hd : 0 < d) (hlam : 0 < lam) (hw : 0 ≤ w) (hwLe : w ≤ 1)
    (hAquot : ∀ i j,
      |spatialDifferenceQuotient k h (fun x ↦ A x i j) z| ≤ Ma) :
    |∑ i : Fin d, ∑ j : Fin d,
        spatialDifferenceQuotient k h (fun x ↦ A x i j) z * G j * (w * H i)| ≤
      (lam / 8) * w * ∑ i : Fin d, H i ^ 2 +
        (2 * (d : ℝ) ^ 2 / lam * Ma ^ 2) * ∑ j : Fin d, G j ^ 2 := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have halloc : 0 < lam / (d : ℝ) := div_pos hlam hdR
  have hwSqrt : (Real.sqrt w) ^ 2 = w := Real.sq_sqrt hw
  calc
    |∑ i : Fin d, ∑ j : Fin d,
        spatialDifferenceQuotient k h (fun x ↦ A x i j) z * G j * (w * H i)| ≤
        ∑ i : Fin d, ∑ j : Fin d,
          |spatialDifferenceQuotient k h (fun x ↦ A x i j) z * G j *
            (w * H i)| := by
      exact (Finset.abs_sum_le_sum_abs _ _).trans <|
        Finset.sum_le_sum fun _ _ ↦ Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin d, ∑ j : Fin d,
        (((lam / (d : ℝ)) / 8) * (Real.sqrt w * |H i|) ^ 2 +
          (2 / (lam / (d : ℝ))) * (Ma * Real.sqrt w * |G j|) ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      have hpre :
          |spatialDifferenceQuotient k h (fun x ↦ A x i j) z * G j *
              (w * H i)| ≤
            (Ma * Real.sqrt w * |G j|) * (Real.sqrt w * |H i|) := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hw]
        calc
          |spatialDifferenceQuotient k h (fun x ↦ A x i j) z| * |G j| *
              (w * |H i|) ≤ Ma * |G j| * (w * |H i|) := by
            gcongr
            exact hAquot i j
          _ = (Ma * Real.sqrt w * |G j|) * (Real.sqrt w * |H i|) := by
            ring_nf
            rw [hwSqrt]
            ring
      exact hpre.trans (mul_le_lambda_eighth_sq_add
        (lam / (d : ℝ)) (Ma * Real.sqrt w * |G j|)
          (Real.sqrt w * |H i|) halloc)
    _ ≤ ∑ i : Fin d, ∑ j : Fin d,
        (((lam / (d : ℝ)) / 8) * (w * H i ^ 2) +
          (2 / (lam / (d : ℝ))) * (Ma ^ 2 * G j ^ 2)) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [mul_pow, sq_abs, hwSqrt, mul_pow, mul_pow, sq_abs, hwSqrt]
      have hMaSqG : 0 ≤ Ma ^ 2 * G j ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
      have hcore : Ma ^ 2 * w * G j ^ 2 ≤ Ma ^ 2 * G j ^ 2 := by
        calc
          Ma ^ 2 * w * G j ^ 2 = w * (Ma ^ 2 * G j ^ 2) := by ring
          _ ≤ 1 * (Ma ^ 2 * G j ^ 2) :=
            mul_le_mul_of_nonneg_right hwLe hMaSqG
          _ = Ma ^ 2 * G j ^ 2 := one_mul _
      gcongr
    _ = (lam / 8) * w * ∑ i : Fin d, H i ^ 2 +
        (2 * (d : ℝ) ^ 2 / lam * Ma ^ 2) * ∑ j : Fin d, G j ^ 2 := by
      simp_rw [Finset.sum_add_distrib]
      simp only [← Finset.mul_sum, sum_fin_sum_repeated_left hd,
        sum_fin_sum_repeated_right hd]
      field_simp

/-- The cutoff-gradient coefficient commutator is a pure data error. -/
private theorem fixedDirection_errorThree_le
    {d : ℕ} {Ma Keta w : ℝ}
    (A : TimeVelocity d → PDE.Mat d) (G Dw : Fin d → ℝ) (Q : ℝ)
    (k : Fin d) (h : ℝ) (z : TimeVelocity d)
    (hd : 0 < d) (hKeta : 0 ≤ Keta) (_hw : 0 ≤ w) (hwLe : w ≤ 1)
    (hAquot : ∀ i j,
      |spatialDifferenceQuotient k h (fun x ↦ A x i j) z| ≤ Ma)
    (hDwSq : ∀ i, Dw i ^ 2 ≤ 4 * Keta ^ 2 * w) :
    |∑ i : Fin d, ∑ j : Fin d,
        spatialDifferenceQuotient k h (fun x ↦ A x i j) z * G j * (Dw i * Q)| ≤
      ((d : ℝ) ^ 2 + (d : ℝ)) * Ma * Keta *
        (Q ^ 2 + ∑ j : Fin d, G j ^ 2) := by
  have hMa : 0 ≤ Ma := by
    exact (abs_nonneg _).trans
      (hAquot (⟨0, hd⟩ : Fin d) (⟨0, hd⟩ : Fin d))
  have hDw (i : Fin d) : |Dw i| ≤ 2 * Keta := by
    have hsq : Dw i ^ 2 ≤ (2 * Keta) ^ 2 := by
      calc
        Dw i ^ 2 ≤ 4 * Keta ^ 2 * w := hDwSq i
        _ ≤ 4 * Keta ^ 2 * 1 := by gcongr
        _ = (2 * Keta) ^ 2 := by ring
    exact (sq_le_sq₀ (abs_nonneg _)
      (mul_nonneg (by norm_num) hKeta)).1 (by simpa only [sq_abs] using hsq)
  calc
    |∑ i : Fin d, ∑ j : Fin d,
        spatialDifferenceQuotient k h (fun x ↦ A x i j) z * G j * (Dw i * Q)| ≤
        ∑ i : Fin d, ∑ j : Fin d,
          |spatialDifferenceQuotient k h (fun x ↦ A x i j) z * G j *
            (Dw i * Q)| := by
      exact (Finset.abs_sum_le_sum_abs _ _).trans <|
        Finset.sum_le_sum fun _ _ ↦ Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin d, ∑ j : Fin d, Ma * Keta * (G j ^ 2 + Q ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_mul, abs_mul]
      have hprod :
          |spatialDifferenceQuotient k h (fun x ↦ A x i j) z| * |G j| *
              (|Dw i| * |Q|) ≤ 2 * Ma * Keta * (|G j| * |Q|) := by
        calc
          _ ≤ Ma * |G j| * ((2 * Keta) * |Q|) := by
            gcongr
            · exact hAquot i j
            · exact hDw i
          _ = 2 * Ma * Keta * (|G j| * |Q|) := by ring
      have hyoung : 2 * (|G j| * |Q|) ≤ G j ^ 2 + Q ^ 2 := by
        rw [← sq_abs (G j), ← sq_abs Q]
        nlinarith [sq_nonneg (|G j| - |Q|)]
      exact hprod.trans (by
        have := mul_le_mul_of_nonneg_left hyoung (mul_nonneg hMa hKeta)
        nlinarith)
    _ ≤ ((d : ℝ) ^ 2 + (d : ℝ)) * Ma * Keta *
        (Q ^ 2 + ∑ j : Fin d, G j ^ 2) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
        sum_fin_sum_repeated_right hd, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      have hdR : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
      have hG : 0 ≤ ∑ j : Fin d, G j ^ 2 := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
      have hQ : 0 ≤ Q ^ 2 := sq_nonneg _
      have hinner :
          (d : ℝ) * (∑ j : Fin d, G j ^ 2) +
              (d : ℝ) * ((d : ℝ) * Q ^ 2) ≤
            ((d : ℝ) ^ 2 + (d : ℝ)) *
              (Q ^ 2 + ∑ j : Fin d, G j ^ 2) := by
        nlinarith [mul_nonneg hdR hG, mul_nonneg hdR hQ]
      have := mul_le_mul_of_nonneg_left hinner (mul_nonneg hMa hKeta)
      nlinarith

/-- Pointwise fixed-core coercivity after absorbing the two Hessian errors and
bounding the remaining commutator solely by quotient data. -/
theorem fixedDirection_fluxPairing_coercive_absorbed
    {d : ℕ} {lam Lam Ma Keta w : ℝ}
    (A : TimeVelocity d → PDE.Mat d)
    (G H Dw : Fin d → ℝ) (Q : ℝ)
    (k : Fin d) (h : ℝ) (z : TimeVelocity d)
    (hd : 0 < d) (hlam : 0 < lam) (hKeta : 0 ≤ Keta)
    (hw : 0 ≤ w) (hwLe : w ≤ 1)
    (hEll : lam • (1 : PDE.Mat d) ≤ A (spatialShift k h z) ∧
      A (spatialShift k h z) ≤ Lam • (1 : PDE.Mat d))
    (hAquot : ∀ i j,
      |spatialDifferenceQuotient k h (fun x ↦ A x i j) z| ≤ Ma)
    (hDwSq : ∀ i, Dw i ^ 2 ≤ 4 * Keta ^ 2 * w) :
    (lam / 2) * w * ∑ i : Fin d, H i ^ 2 ≤
      (∑ i : Fin d,
        (∑ j : Fin d,
          (spatialTranslate k h (fun x ↦ A x i j) z * H j +
            spatialDifferenceQuotient k h (fun x ↦ A x i j) z * G j)) *
          (Dw i * Q + w * H i)) +
      (8 * (d : ℝ) ^ 3 / lam * Lam ^ 2 * Keta ^ 2 +
        2 * (d : ℝ) ^ 2 / lam * Ma ^ 2 +
        ((d : ℝ) ^ 2 + (d : ℝ)) * Ma * Keta) *
          (Q ^ 2 + ∑ j : Fin d, G j ^ 2) := by
  have hraw := fixedDirection_fluxPairing_coercive_raw A G H Dw Q k h z hw hEll.1
  have h₁ := fixedDirection_errorOne_le A H Dw Q k h z hd hlam hKeta hw hEll hDwSq
  have h₂ := fixedDirection_errorTwo_le A G H k h z hd hlam hw hwLe hAquot
  have h₃ := fixedDirection_errorThree_le A G Dw Q k h z hd hKeta hw hwLe hAquot hDwSq
  have hsumH : 0 ≤ ∑ i : Fin d, H i ^ 2 := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hsumG : 0 ≤ ∑ j : Fin d, G j ^ 2 := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hLam : 0 ≤ Lam := by
    have hcoef := abs_apply_le_of_loewner hlam hEll.1 hEll.2
      (⟨0, hd⟩ : Fin d) (⟨0, hd⟩ : Fin d)
    exact (abs_nonneg _).trans hcoef
  have hMa : 0 ≤ Ma :=
    (abs_nonneg _).trans
      (hAquot (⟨0, hd⟩ : Fin d) (⟨0, hd⟩ : Fin d))
  have hdR : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hlam0 : 0 ≤ lam := le_of_lt hlam
  have hdata : 0 ≤ Q ^ 2 + ∑ j : Fin d, G j ^ 2 := add_nonneg (sq_nonneg _) hsumG
  have hC1 : 0 ≤ 8 * (d : ℝ) ^ 3 / lam * Lam ^ 2 * Keta ^ 2 := by positivity
  have hC2 : 0 ≤ 2 * (d : ℝ) ^ 2 / lam * Ma ^ 2 := by positivity
  have hC3 : 0 ≤ ((d : ℝ) ^ 2 + (d : ℝ)) * Ma * Keta := by positivity
  calc
    (lam / 2) * w * ∑ i : Fin d, H i ^ 2 ≤
        lam * w * ∑ i : Fin d, H i ^ 2 -
          ((lam / 8) * w * ∑ i : Fin d, H i ^ 2) -
          ((lam / 8) * w * ∑ i : Fin d, H i ^ 2) := by
      nlinarith [mul_nonneg hw hsumH]
    _ ≤ (∑ i : Fin d,
        (∑ j : Fin d,
          (spatialTranslate k h (fun x ↦ A x i j) z * H j +
            spatialDifferenceQuotient k h (fun x ↦ A x i j) z * G j)) *
          (Dw i * Q + w * H i)) +
        (8 * (d : ℝ) ^ 3 / lam * Lam ^ 2 * Keta ^ 2) * Q ^ 2 +
        (2 * (d : ℝ) ^ 2 / lam * Ma ^ 2) * ∑ j : Fin d, G j ^ 2 +
        ((d : ℝ) ^ 2 + (d : ℝ)) * Ma * Keta *
          (Q ^ 2 + ∑ j : Fin d, G j ^ 2) := by linarith
    _ ≤ _ := by
      have hQpart : Q ^ 2 ≤ Q ^ 2 + ∑ j : Fin d, G j ^ 2 := by linarith
      have hGpart : ∑ j : Fin d, G j ^ 2 ≤ Q ^ 2 + ∑ j : Fin d, G j ^ 2 := by
        linarith [sq_nonneg Q]
      have hC1' := mul_le_mul_of_nonneg_left hQpart hC1
      have hC2' := mul_le_mul_of_nonneg_left hGpart hC2
      nlinarith [mul_nonneg (add_nonneg (add_nonneg hC1 hC2) hC3) hdata]


end HypoellipticAleksandrov.Parabolic
