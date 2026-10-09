module

public import HypoellipticAleksandrov.Coefficients.Ellipticity
public import HypoellipticAleksandrov.LinearAlgebra.LoewnerEntryBound

/-!
# Matrix lemmas for the smoothing package

Elementary facts on real symmetric matrices with two-sided Loewner bounds used in
the smoothing estimates: the upper Loewner bound from a quadratic
form bound, the operator-type bound `|B x|² ≤ Λ² |x|²`, and the Frobenius bound
`∑ᵢⱼ Bᵢⱼ² ≤ d Λ²`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open Matrix
open scoped MatrixOrder

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ}

/-- The squared Frobenius norm `∑ᵢⱼ Bᵢⱼ²`. -/
def frobeniusSq (B : PDE.Mat d) : ℝ := ∑ i, ∑ j, B i j ^ 2

/-- A symmetric quadratic form bound `x·Bx ≤ Λ |x|²` gives the upper Loewner bound. -/
theorem le_smul_one_of_quadraticForm {B : PDE.Mat d} {Lam : ℝ} (hB : B.IsSymm)
    (hquad : ∀ x : PDE.Vec d, x ⬝ᵥ (B *ᵥ x) ≤ Lam * (x ⬝ᵥ x)) : B ≤ Lam • (1 : PDE.Mat d) := by
  have hneg : (-Lam) • (1 : PDE.Mat d) ≤ -B := by
    refine HypoellipticAleksandrov.loewner_lower_of_quadraticForm (A := -B) ?_ fun x => ?_
    · simpa using hB.neg
    · have := hquad x
      simp only [PDE.vecNormSq, PDE.vecDot, Matrix.neg_mulVec]
      change (-Lam) * (x ⬝ᵥ x) ≤ x ⬝ᵥ (-(B *ᵥ x))
      rw [dotProduct_neg]
      linarith
  have := neg_le_neg hneg
  simpa only [neg_neg, neg_smul] using this

/-- The quadratic form of a matrix below `Λ I`. -/
theorem quadraticForm_le_of_le_smul_one {B : PDE.Mat d} {Lam : ℝ} (hB : B ≤ Lam • (1 : PDE.Mat d))
    (x : PDE.Vec d) : x ⬝ᵥ (B *ᵥ x) ≤ Lam * (x ⬝ᵥ x) := by
  have hgap : (Lam • (1 : PDE.Mat d) - B).PosSemidef := Matrix.le_iff.mp hB
  have h := hgap.dotProduct_mulVec_nonneg x
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul] at h
  linarith

/-- The quadratic form of a matrix above `lam I`. -/
theorem le_quadraticForm_of_smul_one_le {B : PDE.Mat d} {lam : ℝ}
    (hB : lam • (1 : PDE.Mat d) ≤ B) (x : PDE.Vec d) : lam * (x ⬝ᵥ x) ≤ x ⬝ᵥ (B *ᵥ x) := by
  simpa [PDE.vecNormSq, PDE.vecDot, dotProduct] using
    HypoellipticAleksandrov.vecDot_mulVec_lower_of_loewner hB x

/-- For a positive semidefinite `B ≤ Λ I`, `|B x|² ≤ Λ² |x|²`. -/
theorem mulVec_dotProduct_le {B : PDE.Mat d} {Lam : ℝ} (hLam : 0 < Lam) (hpsd : B.PosSemidef)
    (hup : B ≤ Lam • (1 : PDE.Mat d)) (x : PDE.Vec d) :
    (B *ᵥ x) ⬝ᵥ (B *ᵥ x) ≤ Lam ^ 2 * (x ⬝ᵥ x) := by
  set u := B *ᵥ x with hu
  have hT : Bᵀ = B := by
    have h1 := hpsd.isHermitian.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h1
  have hcross : x ⬝ᵥ (B *ᵥ u) = u ⬝ᵥ u := by
    have hv : x ᵥ* B = B *ᵥ x := by
      conv_lhs => rw [← hT]
      exact Matrix.vecMul_transpose B x
    rw [Matrix.dotProduct_mulVec, hv]
  have hux : u ⬝ᵥ (B *ᵥ x) = u ⬝ᵥ u := by rw [← hu]
  have hq := hpsd.dotProduct_mulVec_nonneg (x - (1 / Lam) • u)
  simp only [star_trivial, Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub, sub_dotProduct,
    dotProduct_smul, smul_dotProduct, smul_eq_mul, hcross, hux] at hq
  have hQx := quadraticForm_le_of_le_smul_one hup x
  have hQu := quadraticForm_le_of_le_smul_one hup u
  have hLinv : Lam * (1 / Lam) = 1 := by field_simp
  have : 0 ≤ Lam * (x ⬝ᵥ x) - (1 / Lam) * (u ⬝ᵥ u) := by
    have e : (1 / Lam) * (1 / Lam) * (u ⬝ᵥ B *ᵥ u) ≤ (1 / Lam) * (1 / Lam) * (Lam * (u ⬝ᵥ u)) :=
      mul_le_mul_of_nonneg_left hQu (by positivity)
    have e2 : (1 / Lam) * (1 / Lam) * (Lam * (u ⬝ᵥ u)) = (1 / Lam) * (u ⬝ᵥ u) := by
      field_simp
    nlinarith
  have h3 : (u ⬝ᵥ u) ≤ Lam ^ 2 * (x ⬝ᵥ x) := by
    have := mul_le_mul_of_nonneg_left (sub_nonneg.mp this) hLam.le
    have e3 : Lam * ((1 / Lam) * (u ⬝ᵥ u)) = u ⬝ᵥ u := by field_simp
    nlinarith
  exact h3

/-- The Frobenius bound `∑ᵢⱼ Bᵢⱼ² ≤ d Λ²` for symmetric `0 ≤ B ≤ Λ I`. -/
theorem frobeniusSq_le {B : PDE.Mat d} {Lam : ℝ} (hLam : 0 < Lam) (hpsd : B.PosSemidef)
    (hup : B ≤ Lam • (1 : PDE.Mat d)) : frobeniusSq B ≤ d * Lam ^ 2 := by
  have hT : Bᵀ = B := by
    have h1 := hpsd.isHermitian.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h1
  unfold frobeniusSq
  have hcol : ∀ i : Fin d, ∑ j, B i j ^ 2 ≤ Lam ^ 2 := fun i => by
    have h := mulVec_dotProduct_le hLam hpsd hup (Pi.single i (1 : ℝ))
    have e1 : ((Pi.single i (1 : ℝ) : PDE.Vec d) ⬝ᵥ (Pi.single i (1 : ℝ) : PDE.Vec d)) = 1 := by
      simp
    have e2 : B *ᵥ (Pi.single i (1 : ℝ) : PDE.Vec d) = fun j => B j i := by
      ext j; simp [Matrix.mulVec_single]
    rw [e1, e2] at h
    have e3 : ∑ j, B i j ^ 2 = ∑ j, B j i * B j i := by
      refine Finset.sum_congr rfl fun j _ => ?_
      have : B i j = B j i := by
        have := congrFun (congrFun hT i) j
        simpa using this.symm
      rw [this, sq]
    rw [e3]
    simpa [dotProduct] using h.trans (by linarith)
  calc ∑ i, ∑ j, B i j ^ 2 ≤ ∑ _i : Fin d, Lam ^ 2 := Finset.sum_le_sum fun i _ => hcol i
    _ = d * Lam ^ 2 := by simp

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
